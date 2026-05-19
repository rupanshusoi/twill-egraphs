use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

use egg::{Analysis, EGraph, FromOp, Id, Language, Rewrite, Runner, Symbol, rewrite};
use good_lp::{
    Expression, Solution, SolverModel, Variable, constraint, default_solver, variable, variables,
};

mod visualize;

pub type ResourceTable = Vec<Vec<i32>>;
pub type ResourceLimit = Vec<i32>;

#[derive(Debug, Clone, Copy)]
pub struct EdgeData<T> {
    pub id: T,
    pub d: i32,
    pub delta: i32,
}

#[derive(Debug, Clone)]
pub struct TileLang {
    pub op: Symbol,
    pub children: Vec<Id>,
    // NOTE: This is not EdgeData because it lacks children Ids. We cannot put
    // those here because the Language trait wants a slice of Ids, so the Ids
    // must be separate.
    pub edge_data: Vec<(i32, i32)>,
    pub rt: ResourceTable,
}

impl TileLang {
    pub fn new(
        op: impl Into<Symbol>,
        children: Vec<Id>,
        edge_data: Vec<(i32, i32)>,
        rt: ResourceTable,
    ) -> Self {
        Self {
            op: op.into(),
            children,
            edge_data,
            rt,
        }
    }

    pub fn leaf(op: impl Into<Symbol>) -> Self {
        Self::new(op, vec![], vec![], vec![])
    }

    pub fn edges(&self) -> impl Iterator<Item = EdgeData<Id>> + '_ {
        self.children
            .iter()
            .zip(&self.edge_data)
            .map(|(&id, &(d, delta))| EdgeData { id, d, delta })
    }
}

fn modulo_rt(rt: &ResourceTable, ii: usize, n_resources: usize) -> ResourceTable {
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
        Ok(Self::new(op, children, vec![(0, 0); n], vec![]))
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

pub struct SwpExtractor<'a, N: Analysis<TileLang>> {
    egraph: &'a EGraph<TileLang, N>,
    resource_limits: &'a ResourceLimit,
}

#[derive(Debug)]
pub struct SwpSolution {
    pub ii: usize,
    pub end: usize,
    // Selected e-classes -> (index of e-node, t)
    pub selected: HashMap<Id, (usize, i32)>,
}

impl<'a, N: Analysis<TileLang>> SwpExtractor<'a, N> {
    pub fn new(egraph: &'a EGraph<TileLang, N>, resource_limits: &'a ResourceLimit) -> Self {
        Self {
            egraph,
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
        let mut node_mrt: HashMap<(Id, usize), ResourceTable> = HashMap::new();
        for class in self.egraph.classes() {
            for (j, node) in class.nodes.iter().enumerate() {
                let key = (class.id, j);
                let rt = &node.rt;
                node_cost.insert(key, rt.len() as i32);
                node_mrt.insert(key, modulo_rt(rt, ii, n_resources));
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

struct DepGraph<'a> {
    nodes: HashSet<&'a str>,
    rts: HashMap<&'a str, ResourceTable>,
    edges: HashMap<&'a str, Vec<EdgeData<&'a str>>>,
    resource_limits: ResourceLimit,
}

impl<'a> DepGraph<'a> {
    fn new(
        nodes: Vec<&'a str>,
        rts: HashMap<&'a str, ResourceTable>,
        edges: HashMap<&'a str, Vec<EdgeData<&'a str>>>,
        resource_limits: ResourceLimit,
    ) -> Self {
        let mut set = HashSet::with_capacity(nodes.len());
        for n in &nodes {
            assert!(set.insert(*n), "duplicate node name: {n}");
        }
        Self { nodes: set, rts, edges, resource_limits }
    }

    fn class_of<N: Analysis<TileLang>>(&self, egraph: &EGraph<TileLang, N>, op: &str) -> Id {
        egraph
            .classes()
            .find(|c| c.nodes.iter().any(|n| n.op.as_str() == op))
            .map(|c| c.id)
            .unwrap_or_else(|| panic!("no e-class for op {op}"))
    }

    fn to_egraph(&self) -> EGraph<TileLang, ()> {
        let mut egraph: EGraph<TileLang, ()> = EGraph::default();

        let phantoms: HashMap<&str, Id> = self
            .nodes
            .iter()
            .map(|&name| (name, egraph.add(TileLang::leaf(format!("__phantom_{name}")))))
            .collect();

        for &name in &self.nodes {
            let in_edges = self.edges.get(name).cloned().unwrap_or_default();
            let children: Vec<Id> = in_edges.iter().map(|e| phantoms[e.id]).collect();
            let edge_data: Vec<(i32, i32)> = in_edges.iter().map(|e| (e.d, e.delta)).collect();
            let rt = self.rts.get(name).cloned().unwrap_or_default();
            let real = egraph.add(TileLang::new(name, children, edge_data, rt));
            egraph.union(phantoms[name], real);
        }
        egraph.rebuild();

        for class in egraph.classes_mut() {
            class
                .nodes
                .retain(|node| !node.op.as_str().starts_with("__phantom_"));
        }

        egraph
    }
}

fn main() {
  todo!("Temporarily removing vibecoded test infra")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flash_attn() {
        // for ... { k = load; v = load; s = matmul(q, k); p = softmax(s); o += matmul(v, p) }
        let nodes = vec!["q", "k", "v", "s", "p", "o"];

        // Resources: [TMA, SIMT, TC]
        let rts: HashMap<&str, ResourceTable> = HashMap::from([
            ("q", vec![]),
            ("k", vec![vec![1, 0, 0]]),
            ("v", vec![vec![1, 0, 0]]),
            ("s", vec![vec![0, 0, 1]]),
            ("p", vec![vec![0, 1, 0], vec![0, 1, 0]]),
            ("o", vec![vec![0, 0, 1]]),
        ]);

        let edges: HashMap<&str, Vec<EdgeData<&str>>> = HashMap::from([
            (
                "s",
                vec![
                    EdgeData { id: "q", d: 0, delta: 0 },
                    EdgeData { id: "k", d: 1, delta: 0 },
                ],
            ),
            ("p", vec![EdgeData { id: "s", d: 1, delta: 0 }]),
            (
                "o",
                vec![
                    EdgeData { id: "o", d: 1, delta: 1 },
                    EdgeData { id: "v", d: 1, delta: 0 },
                    EdgeData { id: "p", d: 2, delta: 0 },
                ],
            ),
        ]);

        let dep = DepGraph::new(nodes, rts, edges, vec![1, 1, 1]);
        let egraph = dep.to_egraph();

        let root = dep.class_of(&egraph, "o");
        let sol = SwpExtractor::new(&egraph, &dep.resource_limits).solve(&[root]);
        assert_eq!(sol.ii, 2);

        visualize::render_pipeline(&egraph, &dep.resource_limits, &sol, "fa.svg")
            .expect("failed to render pipeline diagram");
    }

    #[test]
    fn chain() {
        let nodes = vec!["a", "b", "c"];
        let rts: HashMap<&str, ResourceTable> = HashMap::from([
            ("a", vec![vec![1]]),
            ("b", vec![vec![1]]),
            ("c", vec![vec![1]]),
        ]);
        let edges: HashMap<&str, Vec<EdgeData<&str>>> = HashMap::from([
            ("b", vec![EdgeData { id: "a", d: 1, delta: 0 }]),
            ("c", vec![EdgeData { id: "b", d: 1, delta: 0 }]),
        ]);

        let dep = DepGraph::new(nodes, rts, edges, vec![1]);
        let egraph = dep.to_egraph();

        let sol = SwpExtractor::new(&egraph, &dep.resource_limits)
            .solve(&[dep.class_of(&egraph, "c")]);
        assert_eq!(sol.ii, 3);

        let rule: Rewrite<TileLang, ()> = rewrite!("ax"; "(b ?x)" => "(x y)");
        let egraph = Runner::default().with_egraph(egraph).run(&[rule]).egraph;

        let sol = SwpExtractor::new(&egraph, &dep.resource_limits)
            .solve(&[dep.class_of(&egraph, "c")]);
        assert!(!sol.selected.contains_key(&dep.class_of(&egraph, "a")));
        assert_eq!(sol.ii, 1);
    }
}
