use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};

use egg::{Analysis, EGraph, FromOp, Id, Language, Symbol};
use good_lp::{constraint, default_solver, variable, variables, Expression, SolverModel};

type ResTable = Vec<Vec<i32>>;

pub trait CostModel {
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
    pub edge_attrs: Vec<(i32, i32)>,
}

impl TileLang {
    pub fn new(
        op: impl Into<Symbol>,
        children: Vec<Id>,
        edge_attrs: Vec<(i32, i32)>,
    ) -> Self {
        Self { op: op.into(), children, edge_attrs }
    }

    pub fn leaf(op: impl Into<Symbol>) -> Self {
        Self::new(op, vec![], vec![])
    }

    pub fn edges(&self) -> impl Iterator<Item = EdgeData> + '_ {
        self.children
            .iter()
            .zip(&self.edge_attrs)
            .map(|(&id, &(d, delta))| EdgeData { id, d, delta })
    }
}

/// Modulo reservation table at the given II: `ii` rows × `n_resources` cols.
/// Sums each cycle of the unfolded `rt` into row (cycle mod ii).
fn modulo_rt(rt: &ResTable, ii: usize, n_resources: usize) -> Vec<Vec<i32>> {
    let mut tbl = vec![vec![0; n_resources]; ii];
    for (row_idx, row) in rt.iter().enumerate() {
        let target = row_idx % ii;
        for (col_idx, &val) in row.iter().enumerate() {
            if col_idx < n_resources {
                tbl[target][col_idx] += val;
            }
        }
    }
    tbl
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

/// Modulo-scheduling extractor that returns the minimum feasible initiation
/// interval for the (singleton) e-graph, in the style of [`egg::LpExtractor`].
///
/// Mirrors `schedule_graph` in `src/ilp-modulo-sched.py`: for each candidate
/// II, sets up the same ILP (T, K, A, B, span variables; precedence, dep,
/// buffer, modulo-resource constraints) and minimises span. The first
/// feasible II is returned.
pub struct SwpExtractor<'a, N: Analysis<TileLang>, C: CostModel> {
    egraph: &'a EGraph<TileLang, N>,
    cost_model: C,
    resource_limits: Vec<i32>,
}

impl<'a, N: Analysis<TileLang>, C: CostModel> SwpExtractor<'a, N, C> {
    pub fn new(
        egraph: &'a EGraph<TileLang, N>,
        cost_model: C,
        resource_limits: Vec<i32>,
    ) -> Self {
        Self { egraph, cost_model, resource_limits }
    }

    pub fn solve(&self) -> usize {
        for ii in 1..=64 {
            if self.try_ii(ii) {
                return ii;
            }
        }
        panic!("no feasible II up to 64");
    }

    fn try_ii(&self, ii: usize) -> bool {
        let classes: Vec<_> = self.egraph.classes().collect();
        let n = classes.len();
        let class_idx: HashMap<Id, usize> = classes
            .iter()
            .enumerate()
            .map(|(i, c)| (c.id, i))
            .collect();
        let n_resources = self.resource_limits.len();
        let rt: Vec<ResTable> = classes
            .iter()
            .map(|c| self.cost_model.get_rt(c.nodes[0].op.as_str()))
            .collect();

        let mut vars = variables!();
        let t: Vec<_> = (0..n)
            .map(|_| vars.add(variable().integer().min(0)))
            .collect();
        let k: Vec<_> = (0..n)
            .map(|_| vars.add(variable().integer().min(0)))
            .collect();
        let buf: Vec<_> = (0..n)
            .map(|_| vars.add(variable().integer().min(0)))
            .collect();
        let a: Vec<Vec<_>> = (0..ii)
            .map(|_| (0..n).map(|_| vars.add(variable().binary())).collect())
            .collect();
        let span = vars.add(variable().integer().min(0));

        let mut model = vars.minimise(span).using(default_solver);

        // 1. Span: t[i] + cost(i) <= span
        for i in 0..n {
            let cost = rt[i].len() as f64;
            model.add_constraint(constraint!(t[i] + cost <= span));
        }

        // 2. Each job starts exactly once: sum_t a[t][i] == 1
        for i in 0..n {
            let mut sum: Expression = 0.0.into();
            for tt in 0..ii {
                sum = sum + a[tt][i];
            }
            model.add_constraint(constraint!(sum == 1));
        }

        // 3. Precedence: t[i] == ii * k[i] + sum_t (t * a[t][i])
        for i in 0..n {
            let mut weighted: Expression = 0.0.into();
            for tt in 0..ii {
                weighted = weighted + (tt as f64) * a[tt][i];
            }
            let rhs: Expression = (ii as f64) * k[i] + weighted;
            model.add_constraint(constraint!(t[i] == rhs));
        }

        // 4. Dependence: T[dst] - T[src] >= delay - II * distance
        //    In our e-graph, parent = consumer (dst), child = producer (src).
        for (dst, class) in classes.iter().enumerate() {
            let node = &class.nodes[0];
            for edge in node.edges() {
                let v_id = self.egraph.find(edge.id);
                let src = class_idx[&v_id];
                let rhs = (edge.d as f64) - (ii as f64) * (edge.delta as f64);
                model.add_constraint(constraint!(t[dst] - t[src] >= rhs));
            }
        }

        // 5. Buffer: II*B[src] + T[src] - T[dst] >= II*(distance + 1) - 1
        for (dst, class) in classes.iter().enumerate() {
            let node = &class.nodes[0];
            for edge in node.edges() {
                let v_id = self.egraph.find(edge.id);
                let src = class_idx[&v_id];
                let lhs: Expression = (ii as f64) * buf[src] + t[src] - t[dst];
                let rhs = (ii as f64) * ((edge.delta as f64) + 1.0) - 1.0;
                model.add_constraint(constraint!(lhs >= rhs));
            }
        }

        // 6. Modulo resource: for each resource s and cycle t in [0, II),
        //    sum over (i, l) of A[(t-l)%II, i] * modulo_rt, II)[l][s] <= R[s]
        for s in 0..n_resources {
            for tt in 0..ii {
                let mut expr: Expression = 0.0.into();
                for i in 0..n {
                    let table = modulo_rt(&rt[i], ii, n_resources);
                    for l in 0..ii {
                        let coeff = table[l][s];
                        if coeff == 0 {
                            continue;
                        }
                        let idx = (tt as i32 - l as i32).rem_euclid(ii as i32) as usize;
                        expr = expr + (coeff as f64) * a[idx][i];
                    }
                }
                model.add_constraint(constraint!(expr <= self.resource_limits[s] as f64));
            }
        }

        model.solve().is_ok()
    }
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use super::*;

    pub struct TestCostModel;

    impl CostModel for TestCostModel {
        fn get_rt(&self, op: &str) -> ResTable {
            match op {
                // a/b/c/d toy problem.
                "a" => vec![vec![1, 0]],
                "b" => vec![vec![0, 1]],
                "c" => vec![vec![1, 0]],
                "d" => vec![vec![1, 0], vec![0, 1]],
                // ilp-modulo-sched.py problem. I1=MMA0, I2=SOFTMAX, I3=MMA1.
                "I1" => vec![vec![1, 0]; 2],
                "I2" => vec![vec![0, 1]; 4],
                "I3" => vec![vec![1, 0]; 2],
                _ => Vec::new(),
            }
        }
    }

    #[test]
    fn ii_abcd() {
        let mut egraph: EGraph<TileLang, ()> = EGraph::default();

        let d_ph = egraph.add(TileLang::leaf("d"));
        let c = egraph.add(TileLang::new("c", vec![d_ph], vec![(0, 1)]));
        let b = egraph.add(TileLang::new("b", vec![c, d_ph], vec![(0, 1), (0, 2)]));
        let _a = egraph.add(TileLang::new("a", vec![b], vec![(0, 2)]));
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

        let ii = SwpExtractor::new(&egraph, TestCostModel, vec![1, 1]).solve();
        assert_eq!(ii, 3);
    }

    #[test]
    fn ii_matches_python() {
        // Mirrors the `G = ([I1, I2, I3], [...])` graph in
        // src/ilp-modulo-sched.py, with `schedule_graph(G, 4, [1, 1])`.
        let mut egraph: EGraph<TileLang, ()> = EGraph::default();

        let i1 = egraph.add(TileLang::leaf("I1"));
        let i2 = egraph.add(TileLang::new("I2", vec![i1], vec![(2, 0)]));
        let i3_ph = egraph.add(TileLang::leaf("I3"));
        let i3 = egraph.add(TileLang::new("I3", vec![i2, i3_ph], vec![(4, 0), (2, 1)]));
        egraph.union(i3_ph, i3);
        egraph.rebuild();

        // I1 is a legitimate leaf (no children); only the I3 placeholder leaf
        // gets pruned.
        for class in egraph.classes_mut() {
            class
                .nodes
                .retain(|n| !(n.op.as_str() == "I3" && n.children.is_empty()));
        }
        for class in egraph.classes() {
            assert_eq!(class.nodes.len(), 1);
        }

        let ii = SwpExtractor::new(&egraph, TestCostModel, vec![1, 1]).solve();
        assert_eq!(ii, 4);
    }
}
