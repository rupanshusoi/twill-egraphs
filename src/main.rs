use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};

use egg::{Analysis, EGraph, FromOp, Id, Language, Symbol};
use good_lp::{
    Expression, Solution, SolverModel, constraint, default_solver, variable, variables,
};

type ResTable = Vec<Vec<i32>>;

pub trait MachineModel {
    fn get_rt(&self, op: &str) -> ResTable;
}

#[derive(Debug, Clone, Copy)]
pub struct EdgeData {
    pub id: Id,
    pub d: i32,
    pub delta: i32,
}

#[derive(Debug, Clone)]
pub struct TileLang {
    pub op: Symbol,
    pub children: Vec<Id>,
    pub edge_data: Vec<(i32, i32)>,
}

impl TileLang {
    pub fn new(op: impl Into<Symbol>, children: Vec<Id>, edge_data: Vec<(i32, i32)>) -> Self {
        Self {
            op: op.into(),
            children,
            edge_data,
        }
    }

    pub fn leaf(op: impl Into<Symbol>) -> Self {
        Self::new(op, vec![], vec![])
    }

    pub fn edges(&self) -> impl Iterator<Item = EdgeData> + '_ {
        self.children
            .iter()
            .zip(&self.edge_data)
            .map(|(&id, &(d, delta))| EdgeData { id, d, delta })
    }
}

fn modulo_rt(rt: &ResTable, ii: usize, n_resources: usize) -> ResTable {
    let mut mrt = vec![vec![0; n_resources]; ii];
    for (row_idx, row) in rt.iter().enumerate() {
        let target = row_idx % ii;
        for (col_idx, &val) in row.iter().enumerate() {
            if col_idx < n_resources {
                mrt[target][col_idx] += val;
            }
        }
    }
    mrt
}

impl PartialEq for TileLang {
    fn eq(&self, other: &Self) -> bool {
        self.op == other.op && self.children == other.children
    }
}
impl Eq for TileLang {}
impl PartialOrd for TileLang {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for TileLang {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.op, &self.children).cmp(&(other.op, &other.children))
    }
}
impl Hash for TileLang {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.op.hash(state);
        self.children.hash(state);
    }
}

impl Language for TileLang {
    type Discriminant = Symbol;
    fn discriminant(&self) -> Self::Discriminant {
        self.op
    }
    fn matches(&self, other: &Self) -> bool {
        self.op == other.op && self.children.len() == other.children.len()
    }
    fn children(&self) -> &[Id] {
        &self.children
    }
    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.children
    }
}

impl fmt::Display for TileLang {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.op)
    }
}

impl FromOp for TileLang {
    type Error = std::convert::Infallible;
    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        let n = children.len();
        Ok(Self::new(op, children, vec![(0, 0); n]))
    }
}

pub struct SwpExtractor<'a, N: Analysis<TileLang>, C: MachineModel> {
    egraph: &'a EGraph<TileLang, N>,
    machine_model: C,
    resource_limits: Vec<i32>,
}

#[derive(Debug, Clone)]
pub struct SwpSolution {
    pub ii: usize,
    pub makespan: i32,
    /// Canonical e-class IDs, indexed in the same order used by the other vectors.
    pub class_ids: Vec<Id>,
    /// Whether each e-class is selected on the chosen DAG.
    pub active: Vec<bool>,
    /// For each e-class, the index (within `EClass::nodes`) of the chosen e-node, or `None`
    /// if the class is inactive.
    pub selected_node: Vec<Option<usize>>,
    /// Absolute start time of each e-class (only meaningful when `active[i]`).
    pub start_time: Vec<i32>,
}

impl SwpSolution {
    pub fn class_index(&self, id: Id) -> Option<usize> {
        self.class_ids.iter().position(|&c| c == id)
    }
}

impl<'a, N: Analysis<TileLang>, C: MachineModel> SwpExtractor<'a, N, C> {
    pub fn new(
        egraph: &'a EGraph<TileLang, N>,
        machine_model: C,
        resource_limits: Vec<i32>,
    ) -> Self {
        Self {
            egraph,
            machine_model,
            resource_limits,
        }
    }

    pub fn solve(&self, roots: &[Id]) -> SwpSolution {
        for ii in 1..=64 {
            if let Some(sol) = self.solve_at(ii, roots) {
                return sol;
            }
        }
        panic!("could not find feasible II");
    }

    fn solve_at(&self, ii: usize, roots: &[Id]) -> Option<SwpSolution> {
        let n_resources = self.resource_limits.len();

        let classes: Vec<_> = self.egraph.classes().collect();
        let n = classes.len();
        let class_idx: HashMap<Id, usize> =
            classes.iter().enumerate().map(|(i, c)| (c.id, i)).collect();

        // Flat e-node indexing: e-node `m` lives in class `i` at offset `m - node_offset[i]`.
        let mut node_offset: Vec<usize> = Vec::with_capacity(n + 1);
        node_offset.push(0);
        for class in &classes {
            node_offset.push(node_offset.last().unwrap() + class.nodes.len());
        }
        let n_nodes = node_offset[n];

        // Pre-compute per-e-node cost and resource table.
        let mut node_cost: Vec<i32> = Vec::with_capacity(n_nodes);
        let mut node_rt: Vec<ResTable> = Vec::with_capacity(n_nodes);
        for class in &classes {
            for node in &class.nodes {
                let rt = self.machine_model.get_rt(node.op.as_str());
                node_cost.push(rt.len() as i32);
                node_rt.push(rt);
            }
        }

        // Big-M tight enough to deactivate dep constraints when x[m] = 0 without bloating
        // the LP relaxation: bounds (d - II*delta) - (t[i] - t[src]) above for any
        // schedule the LP could produce with this II.
        let sum_costs: i32 = node_cost.iter().sum();
        let max_d: i32 = classes
            .iter()
            .flat_map(|c| c.nodes.iter())
            .flat_map(|node| node.edge_data.iter().map(|&(d, _)| d))
            .max()
            .unwrap_or(0);
        let big_m = (ii as i32) * (sum_costs + 1) + max_d;

        let mut vars = variables!();
        let t: Vec<_> = (0..n)
            .map(|_| vars.add(variable().integer().min(0)))
            .collect();
        let k: Vec<_> = (0..n)
            .map(|_| vars.add(variable().integer().min(0)))
            .collect();
        let active: Vec<_> = (0..n).map(|_| vars.add(variable().binary())).collect();
        let x: Vec<_> = (0..n_nodes).map(|_| vars.add(variable().binary())).collect();
        let a: Vec<Vec<_>> = (0..ii)
            .map(|_| (0..n_nodes).map(|_| vars.add(variable().binary())).collect())
            .collect();
        let last_var = vars.add(variable().integer().min(0));
        let mut model = vars.minimise(last_var).using(default_solver);

        // Per-class constraints.
        for i in 0..n {
            let cls_lo = node_offset[i];
            let cls_hi = node_offset[i + 1];

            // Selection: exactly one e-node per active class, none when inactive.
            let sel: Expression = (cls_lo..cls_hi).map(|m| x[m]).sum();
            model.add_constraint(constraint!(sel == active[i]));

            // Modulo decomposition: t[i] = II*k[i] + sum_{m, tt} tt * a[tt][m].
            let mut decomp = Expression::from(0);
            for m in cls_lo..cls_hi {
                for tt in 0..ii {
                    decomp += (tt as i32) * a[tt][m];
                }
            }
            model.add_constraint(constraint!(t[i] == (ii as i32) * k[i] + decomp));

            // Makespan: t[i] + cost(chosen) <= last. At most one x[m] is 1 per active class.
            let cost_term: Expression = (cls_lo..cls_hi).map(|m| node_cost[m] * x[m]).sum();
            model.add_constraint(constraint!(t[i] + cost_term <= last_var));
        }

        // Per-e-node constraints.
        for (i, class) in classes.iter().enumerate() {
            for (j, node) in class.nodes.iter().enumerate() {
                let m = node_offset[i] + j;

                // Slot used iff selected.
                let slot_sum: Expression = (0..ii).map(|tt| a[tt][m]).sum();
                model.add_constraint(constraint!(slot_sum == x[m]));

                // Child propagation: if e-node m is chosen, every child class must be active.
                for &child in &node.children {
                    let c_idx = class_idx[&self.egraph.find(child)];
                    model.add_constraint(constraint!(x[m] - active[c_idx] <= 0));
                }

                // Per-edge dep with big-M, gated on x[m].
                for edge in node.edges() {
                    let src = class_idx[&self.egraph.find(edge.id)];
                    let rhs = edge.d - (ii as i32) * edge.delta;
                    model.add_constraint(constraint!(
                        t[i] - t[src] + big_m - big_m * x[m] >= rhs
                    ));
                }
            }
        }

        // Root forcing.
        for &r in roots {
            let i = class_idx[&self.egraph.find(r)];
            model.add_constraint(constraint!(active[i] == 1));
        }

        // Modulo resource constraint, summed per e-node.
        for s in 0..n_resources {
            for tt in 0..ii {
                let mut load = Expression::from(0);
                for m in 0..n_nodes {
                    let mrt = modulo_rt(&node_rt[m], ii, n_resources);
                    for l in 0..ii {
                        let coeff = mrt[l][s];
                        if coeff != 0 {
                            load += coeff * a[(tt + ii - l) % ii][m];
                        }
                    }
                }
                model.add_constraint(constraint!(load <= self.resource_limits[s]));
            }
        }

        let sol = model.solve().ok()?;

        let class_ids: Vec<Id> = classes.iter().map(|c| c.id).collect();
        let active_vals: Vec<bool> = (0..n)
            .map(|i| sol.value(active[i]).round() as i32 != 0)
            .collect();
        let start_time: Vec<i32> = (0..n).map(|i| sol.value(t[i]).round() as i32).collect();
        let mut selected_node: Vec<Option<usize>> = vec![None; n];
        for i in 0..n {
            let cls_lo = node_offset[i];
            let cls_hi = node_offset[i + 1];
            for (j, m) in (cls_lo..cls_hi).enumerate() {
                if sol.value(x[m]).round() as i32 == 1 {
                    selected_node[i] = Some(j);
                    break;
                }
            }
        }
        let makespan = sol.value(last_var).round() as i32;

        Some(SwpSolution {
            ii,
            makespan,
            class_ids,
            active: active_vals,
            selected_node,
            start_time,
        })
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dragon_book() {
        pub struct TestCostModel;

        impl MachineModel for TestCostModel {
            fn get_rt(&self, op: &str) -> ResTable {
                match op {
                    "a" => vec![vec![1, 0]],
                    "b" => vec![vec![0, 1]],
                    "c" => vec![vec![1, 0]],
                    "d" => vec![vec![1, 0], vec![0, 1]],
                    _ => panic!(),
                }
            }
        }

        let mut egraph: EGraph<TileLang, ()> = EGraph::default();

        let d_ph = egraph.add(TileLang::leaf("d"));
        let c = egraph.add(TileLang::new("c", vec![d_ph], vec![(0, 1)]));
        let b = egraph.add(TileLang::new("b", vec![c, d_ph], vec![(0, 1), (0, 2)]));
        let a = egraph.add(TileLang::new("a", vec![b], vec![(0, 2)]));
        let d_with_b = egraph.add(TileLang::new("d", vec![b], vec![(1, 1)]));
        egraph.union(d_ph, d_with_b);
        egraph.rebuild();

        // Drop the placeholder `d()` leaf so d's class is a singleton {d(b)}.
        for class in egraph.classes_mut() {
            class
                .nodes
                .retain(|n| !(n.op.as_str() == "d" && n.children.is_empty()));
        }
        for class in egraph.classes() {
            assert_eq!(class.nodes.len(), 1);
        }

        let sol = SwpExtractor::new(&egraph, TestCostModel, vec![1, 1]).solve(&[a]);
        assert_eq!(sol.ii, 3);
    }

    #[test]
    fn chain_two_nodes_per_class() {
        // Three e-classes c, b, a in a chain (a depends on b, b depends on c, c depends on
        // a single leaf). Each non-leaf class has two e-nodes with identical resource usage
        // but different incoming-edge latencies (d=2 vs d=1). The LP must pick the d=1 e-node
        // in every class to minimise makespan.
        pub struct CM;
        impl MachineModel for CM {
            fn get_rt(&self, op: &str) -> ResTable {
                match op {
                    "leaf" | "c1" | "c2" | "b1" | "b2" | "a1" | "a2" => vec![vec![1]],
                    _ => panic!("unknown op {op}"),
                }
            }
        }

        let mut g: EGraph<TileLang, ()> = EGraph::default();
        let leaf = g.add(TileLang::leaf("leaf"));

        let c1 = g.add(TileLang::new("c1", vec![leaf], vec![(2, 0)]));
        let c2 = g.add(TileLang::new("c2", vec![leaf], vec![(1, 0)]));
        g.union(c1, c2);

        let b1 = g.add(TileLang::new("b1", vec![c1], vec![(2, 0)]));
        let b2 = g.add(TileLang::new("b2", vec![c1], vec![(1, 0)]));
        g.union(b1, b2);

        let a1 = g.add(TileLang::new("a1", vec![b1], vec![(2, 0)]));
        let a2 = g.add(TileLang::new("a2", vec![b1], vec![(1, 0)]));
        g.union(a1, a2);

        g.rebuild();

        let sol = SwpExtractor::new(&g, CM, vec![1]).solve(&[a1]);
        // 4 ops each consuming 1 unit of the only resource → ii must be at least 4.
        assert_eq!(sol.ii, 4);
        // d=1 chain: t_leaf=0, t_c=1, t_b=2, t_a=3, makespan = t_a + cost(a) = 4.
        // d=2 chain would give makespan = 7.
        assert_eq!(sol.makespan, 4);
    }

    #[test]
    fn disjoint_root() {
        // Root e-class `a` has two e-nodes whose children are disjoint: a(p, q) vs a(r).
        // Resource limit 1 makes the 3-op a(p, q) branch require ii ≥ 3, while the 2-op
        // a(r) branch fits at ii = 2 — the LP must pick a(r), leaving p and q inactive.
        pub struct CM;
        impl MachineModel for CM {
            fn get_rt(&self, op: &str) -> ResTable {
                match op {
                    "p" | "q" | "r" | "a" => vec![vec![1]],
                    _ => panic!("unknown op {op}"),
                }
            }
        }

        let mut g: EGraph<TileLang, ()> = EGraph::default();
        let p = g.add(TileLang::leaf("p"));
        let q = g.add(TileLang::leaf("q"));
        let r = g.add(TileLang::leaf("r"));

        let a1 = g.add(TileLang::new("a", vec![p, q], vec![(1, 0), (1, 0)]));
        let a2 = g.add(TileLang::new("a", vec![r], vec![(1, 0)]));
        g.union(a1, a2);
        g.rebuild();

        let sol = SwpExtractor::new(&g, CM, vec![1]).solve(&[a1]);
        assert_eq!(sol.ii, 2);

        let p_idx = sol.class_index(g.find(p)).unwrap();
        let q_idx = sol.class_index(g.find(q)).unwrap();
        let r_idx = sol.class_index(g.find(r)).unwrap();
        let a_idx = sol.class_index(g.find(a1)).unwrap();

        assert!(!sol.active[p_idx], "p should be inactive when a(r) is picked");
        assert!(!sol.active[q_idx], "q should be inactive when a(r) is picked");
        assert!(sol.active[r_idx], "r must be active when a(r) is picked");
        assert!(sol.active[a_idx], "root a must be active");
    }
}
