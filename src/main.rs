use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};

use egg::{Analysis, EGraph, FromOp, Id, Language, Symbol};
use good_lp::{
    Expression, Solution, SolverModel, Variable, constraint, default_solver, variable, variables,
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

struct ClassVars {
    t: Variable,
    k: Variable,
    y: Variable,
}

struct NodeVars {
    x: Variable,
    a: Vec<Variable>,
}

pub struct SwpExtractor<'a, N: Analysis<TileLang>, C: MachineModel> {
    egraph: &'a EGraph<TileLang, N>,
    machine_model: C,
    resource_limits: Vec<i32>,
}

pub struct SwpSolution {
    pub ii: usize,
    pub end: usize,
    // Selected e-classes -> (index of e-node, t)
    pub selected: HashMap<Id, (usize, i32)>,
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
        // TODO: Set M properly
        const M: i32 = 1000;

        let mut vars = variables!();

        let mut class_vars: HashMap<Id, ClassVars> = HashMap::new();
        for class in self.egraph.classes() {
            class_vars.insert(
                class.id,
                ClassVars {
                    t: vars.add(variable().integer().min(0)),
                    k: vars.add(variable().integer().min(0)),
                    y: vars.add(variable().binary()),
                },
            );
        }

        let mut node_vars: HashMap<(Id, usize), NodeVars> = HashMap::new();
        let mut node_cost: HashMap<(Id, usize), i32> = HashMap::new();
        let mut node_mrt: HashMap<(Id, usize), ResTable> = HashMap::new();
        for class in self.egraph.classes() {
            for (j, node) in class.nodes.iter().enumerate() {
                let key = (class.id, j);
                let rt = self.machine_model.get_rt(node.op.as_str());
                node_cost.insert(key, rt.len() as i32);
                node_mrt.insert(key, modulo_rt(&rt, ii, n_resources));
                node_vars.insert(
                    key,
                    NodeVars {
                        x: vars.add(variable().binary()),
                        a: (0..ii).map(|_| vars.add(variable().binary())).collect(),
                    },
                );
            }
        }

        let last = vars.add(variable().integer().min(0));
        let mut model = vars.minimise(last).using(default_solver);

        // E-class constraints
        for class in self.egraph.classes() {
            let cv = &class_vars[&class.id];

            // E-class selected <=> One e-node selected
            let sum: Expression = (0..class.nodes.len())
                .map(|j| node_vars[&(class.id, j)].x)
                .sum();
            model.add_constraint(constraint!(sum == cv.y));

            // t = k * I + \sum_i i * a_i
            let mut ia = Expression::from(0);
            for j in 0..class.nodes.len() {
                let nv = &node_vars[&(class.id, j)];
                for tt in 0..ii {
                    ia += (tt as i32) * nv.a[tt];
                }
            }
            model.add_constraint(constraint!(cv.t == cv.k * (ii as i32) + ia));

            // Definition of objective
            let end: Expression = (0..class.nodes.len())
                .map(|j| node_cost[&(class.id, j)] * node_vars[&(class.id, j)].x)
                .sum();
            model.add_constraint(constraint!(last >= cv.t + end));
        }

        // E-node constraints
        for class in self.egraph.classes() {
            let cv = &class_vars[&class.id];
            for (j, node) in class.nodes.iter().enumerate() {
                let nv = &node_vars[&(class.id, j)];

                // sum_i a_i <=> x
                let slot_sum: Expression = (0..ii).map(|tt| nv.a[tt]).sum();
                model.add_constraint(constraint!(slot_sum == nv.x));

                // E-node selected => every child e-class selected
                for &child in &node.children {
                    let child_y = class_vars[&self.egraph.find(child)].y;
                    model.add_constraint(constraint!(nv.x - child_y <= 0));
                }

                // Modulo scheduling dependence constraint
                // TODO: Can't we merge the previous loop and this one?
                // FIXME: If I find a better e-node in a child e-class, its d will not change...
                for edge in node.edges() {
                    let src_t = class_vars[&self.egraph.find(edge.id)].t;
                    let rhs = edge.d - (ii as i32) * edge.delta;
                    model.add_constraint(constraint!(cv.t - src_t + M - M * nv.x >= rhs));
                }
            }
        }

        for &r in roots {
            let cv = &class_vars[&self.egraph.find(r)];
            model.add_constraint(constraint!(cv.y == 1));
        }

        // Resource constraints
        for s in 0..n_resources {
            for tt in 0..ii {
                let mut usage = Expression::from(0);
                for class in self.egraph.classes() {
                    for j in 0..class.nodes.len() {
                        let key = (class.id, j);
                        let mrt = &node_mrt[&key];
                        let nv = &node_vars[&key];
                        for i in 0..ii {
                            usage += mrt[(tt + ii - i) % ii][s] * nv.a[i];
                        }
                    }
                }
                model.add_constraint(constraint!(usage <= self.resource_limits[s]));
            }
        }

        let sol = model.solve().ok()?;

        let mut selected: HashMap<Id, (usize, i32)> = HashMap::new();
        for class in self.egraph.classes() {
            let cv = &class_vars[&class.id];
            if sol.value(cv.y).round() as i32 == 0 {
                continue;
            }
            let t = sol.value(cv.t).round() as i32;
            for j in 0..class.nodes.len() {
                if sol.value(node_vars[&(class.id, j)].x).round() as i32 == 1 {
                    selected.insert(class.id, (j, t));
                    break;
                }
            }
        }
        let end = sol.value(last).round() as usize;

        Some(SwpSolution { ii, end, selected })
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
        // d=1 chain: t_leaf=0, t_c=1, t_b=2, t_a=3, end = t_a + cost(a) = 4.
        // d=2 chain would give end = 7.
        assert_eq!(sol.end, 4);
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

        assert!(!sol.selected.contains_key(&g.find(p)), "p should be inactive when a(r) is picked");
        assert!(!sol.selected.contains_key(&g.find(q)), "q should be inactive when a(r) is picked");
        assert!(sol.selected.contains_key(&g.find(r)), "r must be active when a(r) is picked");
        assert!(sol.selected.contains_key(&g.find(a1)), "root a must be active");
    }
}
