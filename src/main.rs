use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};

use egg::{Analysis, EGraph, FromOp, Id, Language, Symbol};
use good_lp::{
    Expression, Solution, SolverModel, Variable, constraint, default_solver, variable, variables,
};

mod visualize;

pub type ResTable = Vec<Vec<i32>>;

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

#[derive(Debug)]
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

pub struct Problem {
    pub resource_limits: Vec<i32>,
    // NOTE: A node may only use one kind of resource
    // (node, duration, resource kind)
    pub nodes: Vec<(String, i32, usize)>,
    // (src, dst, d, delta)
    pub edges: Vec<(usize, usize, i32, i32)>,
}

pub fn parse_problem(path: &str) -> Problem {
    let raw = std::fs::read_to_string(path).expect("failed to read problem file");
    let mut tokens = raw
        .lines()
        .map(|l| l.split('#').next().unwrap_or(""))
        .flat_map(|l| l.split_ascii_whitespace());

    let mut next = || tokens.next().expect("unexpected end of file");
    let parse_i32 = |s: &str| s.parse::<i32>().expect("expected integer");
    let parse_usize = |s: &str| s.parse::<usize>().expect("expected unsigned integer");

    assert_eq!(next(), "R");
    let s = parse_usize(next());
    let resource_limits: Vec<i32> = (0..s).map(|_| parse_i32(next())).collect();

    assert_eq!(next(), "N");
    let n = parse_usize(next());
    let mut nodes = Vec::with_capacity(n);
    for _ in 0..n {
        let name = next().to_string();
        let cost = parse_i32(next());
        let resource = parse_usize(next());
        nodes.push((name, cost, resource));
    }

    assert_eq!(next(), "E");
    let m = parse_usize(next());
    let mut edges = Vec::with_capacity(m);
    for _ in 0..m {
        let src = parse_usize(next());
        let dst = parse_usize(next());
        let d = parse_i32(next());
        let delta = parse_i32(next());
        edges.push((src, dst, d, delta));
    }

    Problem {
        resource_limits,
        nodes,
        edges,
    }
}

#[derive(Clone)]
pub struct TableMachineModel {
    pub table: HashMap<String, ResTable>,
}

impl TableMachineModel {
    pub fn from_problem(problem: &Problem) -> Self {
        let n_resources = problem.resource_limits.len();
        let mut table = HashMap::new();
        for (name, cost, resource) in &problem.nodes {
            let mut rt = vec![vec![0i32; n_resources]; *cost as usize];
            for row in &mut rt {
                row[*resource] = 1;
            }
            table.insert(name.clone(), rt);
        }
        Self { table }
    }
}

impl MachineModel for TableMachineModel {
    fn get_rt(&self, op: &str) -> ResTable {
        self.table
            .get(op)
            .cloned()
            .unwrap_or_else(|| panic!("no resource table for op {op}"))
    }
}

pub fn add_phantom(egraph: &mut EGraph<TileLang, ()>, tag: &str) -> Id {
    egraph.add(TileLang::leaf(format!("__phantom_{tag}")))
}

pub fn strip_phantoms(egraph: &mut EGraph<TileLang, ()>) {
    egraph.rebuild();
    for class in egraph.classes_mut() {
        class
            .nodes
            .retain(|node| !node.op.as_str().starts_with("__phantom_"));
    }
}

pub fn add_cyclic(
    egraph: &mut EGraph<TileLang, ()>,
    op: &str,
    children: Vec<Option<Id>>,
    edge_data: Vec<(i32, i32)>,
) -> Id {
    let phantom = add_phantom(egraph, op);
    let resolved: Vec<Id> = children.iter().map(|c| c.unwrap_or(phantom)).collect();
    let real = egraph.add(TileLang::new(op, resolved, edge_data));
    egraph.union(phantom, real);
    real
}

pub fn build_egraph(problem: &Problem) -> (EGraph<TileLang, ()>, Vec<Id>) {
    let n = problem.nodes.len();
    let mut egraph: EGraph<TileLang, ()> = EGraph::default();

    let phantom: Vec<Id> = (0..n)
        .map(|i| add_phantom(&mut egraph, &i.to_string()))
        .collect();

    let mut incoming: Vec<Vec<(usize, i32, i32)>> = vec![Vec::new(); n];
    for &(src, dst, d, delta) in &problem.edges {
        incoming[dst].push((src, d, delta));
    }

    let real: Vec<Id> = (0..n)
        .map(|v| {
            let children: Vec<Id> = incoming[v].iter().map(|&(u, _, _)| phantom[u]).collect();
            let edge_data: Vec<(i32, i32)> =
                incoming[v].iter().map(|&(_, d, dl)| (d, dl)).collect();
            egraph.add(TileLang::new(
                problem.nodes[v].0.as_str(),
                children,
                edge_data,
            ))
        })
        .collect();

    for v in 0..n {
        egraph.union(phantom[v], real[v]);
    }
    strip_phantoms(&mut egraph);

    // All e-classes singleton
    assert_eq!(egraph.number_of_classes(), egraph.total_number_of_nodes());

    // NOTE: To match Python, we force all e-classes! For a real program, there
    // should a single e-class, corresponding to the output value, that is forced.
    let roots: Vec<Id> = real.iter().map(|&id| egraph.find(id)).collect();
    (egraph, roots)
}

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args.next().expect("usage: sme-swp <problem.swp> [dot_out]");
    let dot_out = args.next();

    let problem = parse_problem(&path);
    let (egraph, roots) = build_egraph(&problem);

    if let Some(out) = dot_out.as_deref() {
        egraph.dot().to_dot(out).expect("failed to write dot file");
    }

    let model = TableMachineModel::from_problem(&problem);
    let sol = SwpExtractor::new(&egraph, model, problem.resource_limits.clone()).solve(&roots);
    println!("RESULT_II={}", sol.ii);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fa() {
        // for ... { k = load; v = load; s = matmul(q, k); p = softmax(s); o += matmul(v, p) }
        let mut egraph: EGraph<TileLang, ()> = EGraph::default();

        let q = egraph.add(TileLang::leaf("q"));
        let k = egraph.add(TileLang::new("k", vec![], vec![]));
        let v = egraph.add(TileLang::new("v", vec![], vec![]));
        let s = egraph.add(TileLang::new("s", vec![q, k], vec![(0, 0), (1, 0)]));
        let p = egraph.add(TileLang::new("p", vec![s], vec![(1, 0)]));

        let o = add_cyclic(
            &mut egraph,
            "o",
            vec![None, Some(v), Some(p)],
            vec![(1, 1), (1, 0), (2, 0)],
        );
        strip_phantoms(&mut egraph);

        let root = egraph.find(o);

        // Resources: [TMA, SIMT, TC]
        let mut table: HashMap<String, ResTable> = HashMap::new();
        table.insert("q".into(), vec![]);
        table.insert("k".into(), vec![vec![1, 0, 0]]);
        table.insert("v".into(), vec![vec![1, 0, 0]]);
        table.insert("s".into(), vec![vec![0, 0, 1]]);
        table.insert("p".into(), vec![vec![0, 1, 0], vec![0, 1, 0]]);
        table.insert("o".into(), vec![vec![0, 0, 1]]);
        let model = TableMachineModel { table };
        let resource_limits = vec![1, 1, 1];

        // egraph
        //     .dot()
        //     .to_dot("flash_attention.dot")
        //     .expect("failed to write dot");
        // let _ = egraph.dot().to_png("flash_attention.png");

        let sol = SwpExtractor::new(&egraph, model.clone(), resource_limits.clone()).solve(&[root]);
        println!("ii = {}", sol.ii);

        visualize::render_pipeline(
            &egraph,
            &model,
            &resource_limits,
            &sol,
            "fa.svg",
        )
        .expect("failed to render pipeline diagram");
    }
}
