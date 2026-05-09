from pulp import *
import random


class Node:
    def __init__(self, name, cost, resource):
        self.name = name
        self._cost = cost
        self._resource = resource

    def cost(self):
        return self._cost

    def resource(self):
        return self._resource

    def restable(self, II, num_resources):
        tbl = [[0 for _ in range(num_resources)] for _ in range(II)]
        for i in range(self.cost()):
            tbl[i % II][self.resource()] += 1
        return tbl

    def __str__(self):
        return self.name


class Edge:
    def __init__(self, src, dst, dep):
        self.src = src
        self.dst = dst
        self.dep = dep # (d, delta)

    def __str__(self):
        return f"({self.src}, {self.dst}, {self.dep})"


def schedule_graph(G, II, R, verbose=False):
    V, E = G
    num_resources = len(R)

    T = LpVariable.dicts("T", [i for i in range(len(V))], lowBound=0, cat=LpInteger)
    K = LpVariable.dicts("K", [i for i in range(len(V))], lowBound=0, cat=LpInteger)
    A = LpVariable.dicts("A", [(t, i) for t in range(II) for i in range(len(V))], cat=LpBinary)

    prob = LpProblem("scheduling", LpMinimize)

    span = LpVariable("span", lowBound=0, cat=LpInteger)
    prob += span
    for i in range(len(V)):
        prob += T[i] + V[i].cost() <= span

    for i in range(len(V)):
        prob += (lpSum([A[t, i] for t in range(II)]) == 1)

    for i in range(len(V)):
        prob += (T[i] == (II * K[i] + lpSum([A[t, i] * t for t in range(II)])))

    for edge in E:
        prob += (T[edge.dst] - T[edge.src] >= edge.dep[0] - II * edge.dep[1])

    for s in range(num_resources):
        for t in range(II):
            prob += (lpSum([
                A[(t - l) % II, i] * V[i].restable(II, num_resources)[l][s]
                for i in range(len(V))
                for l in range(II)
            ]) <= R[s])

    solver = PULP_CBC_CMD(msg=0)
    status = prob.solve(solver)

    if LpStatus[status] != "Optimal":
        return None

    T_vals = [int(value(T[i])) for i in range(len(V))]

    if verbose:
        tmin = min(T_vals)
        print("===================")
        for i, v in enumerate(V):
            print(v, T_vals[i], T_vals[i] - tmin, int(value(K[i])))
        print("===================")
        for t in range(II):
            print(" ".join([str(int(value(A[t, i]))) for i in range(len(V))]))

    return T_vals


class RandomGraphGenerator:
    def __init__(
        self,
        num_nodes=8,
        num_resources=2,
        edge_density=0.3,
        backedge_prob=0.2,
        min_cost=1,
        max_cost=4,
        max_iter_dist=2,
        seed=None,
    ):
        self.num_nodes = num_nodes
        self.num_resources = num_resources
        self.edge_density = edge_density
        self.backedge_prob = backedge_prob
        self.min_cost = min_cost
        self.max_cost = max_cost
        self.max_iter_dist = max_iter_dist
        self.rng = random.Random(seed)

    def generate(self):
        V = []
        for i in range(self.num_nodes):
            cost = self.rng.randint(self.min_cost, self.max_cost)
            resource = self.rng.randrange(self.num_resources)
            V.append(Node(f"N{i}", cost, resource))

        E = []
        for i in range(self.num_nodes):
            for j in range(self.num_nodes):
                if i == j:
                    if self.rng.random() < self.backedge_prob:
                        delta = self.rng.randint(1, self.max_iter_dist)
                        E.append(Edge(i, j, (V[i].cost(), delta)))
                elif i < j:
                    if self.rng.random() < self.edge_density:
                        E.append(Edge(i, j, (V[i].cost(), 0)))
                else:
                    if self.rng.random() < self.backedge_prob:
                        delta = self.rng.randint(1, self.max_iter_dist)
                        E.append(Edge(i, j, (V[i].cost(), delta)))
        return V, E

    # Set resource limits to ensure problem is feasible
    def resource_limits(self, V, slack=1):
        usage = [0] * self.num_resources
        for v in V:
            usage[v.resource()] += v.cost()
        return [max(1, u // max(1, self.num_nodes // 2) + slack) for u in usage]


def validate_schedule(G, II, R, T_vals):
    V, E = G
    failures = []
    for edge in E:
        t1 = T_vals[edge.dst]
        t2 = T_vals[edge.src]
        d, delta = edge.dep
        rhs = d - delta * II
        if t1 - t2 < rhs:
            failures.append(
                f"edge {edge.src}->{edge.dst}: "
                f"T[{edge.dst}]-T[{edge.src}] = {t1 - t2} < {d} - {delta}*{II} = {rhs}"
            )

    num_resources = len(R)
    usage = [[0] * num_resources for _ in range(II)]
    for i, v in enumerate(V):
        start = T_vals[i] % II
        for l in range(v.cost()):
            usage[(start + l) % II][v.resource()] += 1
    for t in range(II):
        for s in range(num_resources):
            if usage[t][s] > R[s]:
                failures.append(
                    f"resource overuse at cycle {t}, kind {s}: {usage[t][s]} > {R[s]}"
                )
    return failures


def run_test(seed, **kwargs):
    gen = RandomGraphGenerator(seed=seed, **kwargs)
    V, E = gen.generate()
    R = gen.resource_limits(V)

    II_min = max(1, max((v.cost() for v in V), default=1))
    for II in range(II_min, II_min + 8):
        T_vals = schedule_graph((V, E), II, R)
        if T_vals is None:
            continue
        failures = validate_schedule((V, E), II, R, T_vals)
        return {
            "seed": seed,
            "num_nodes": len(V),
            "num_edges": len(E),
            "II": II,
            "R": R,
            "T": T_vals,
            "failures": failures,
        }
    return {"seed": seed, "num_nodes": len(V), "num_edges": len(E), "II": None, "failures": []}


if __name__ == "__main__":
    import sys

    num_trials = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    base_seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0

    total_failures = 0
    for trial in range(num_trials):
        seed = base_seed + trial
        result = run_test(
            seed=seed,
            num_nodes=random.Random(seed).randint(4, 10),
            num_resources=random.Random(seed + 1).randint(1, 3),
            edge_density=0.3,
            backedge_prob=0.15,
        )
        ok = result["II"] is not None and not result["failures"]
        status = "OK" if ok else ("UNSCHEDULABLE" if result["II"] is None else "FAIL")
        print(
            f"[trial {trial:3d} seed={result['seed']:3d}] "
            f"V={result['num_nodes']} E={result['num_edges']} "
            f"II={result['II']} R={result.get('R')} -> {status}"
        )
        if result["failures"]:
            total_failures += 1
            for f in result["failures"]:
                print(f"  FAIL: {f}")

    print(f"\nTotal validation failures: {total_failures}/{num_trials}")
