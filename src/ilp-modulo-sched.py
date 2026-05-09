from pulp import *
from enum import Enum

class NodeKind(Enum):
    MMA0 = 1
    MMA1 = 2
    SOFTMAX = 3

class ResourceKind(Enum):
    TC = 0
    SIMT = 1

class Node:
    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    def cost(self):
        if self.typ == NodeKind.MMA0 or self.typ == NodeKind.MMA1:
            return 2
        else:
            return 4

    def resource(self):
        if self.typ == NodeKind.MMA0 or self.typ == NodeKind.MMA1:
            return ResourceKind.TC
        else:
            return ResourceKind.SIMT


    def restable(self, II):
        tbl = [[0 for _ in range(len(ResourceKind))] for _ in range(II)]
        for i in range(self.cost()):
            tbl[i % II][self.resource().value] += 1
        return tbl

    def __str__(self):
        return self.name

class Edge:
    def __init__(self, src, dst, dep):
        self.src = src
        self.dst = dst
        # dep[0] = delay
        # dep[1] = iteration distance
        self.dep = dep

    def __str__(self):
        return f"({self.src}, {self.dst}, {self.dep})"

I1 = Node("I1", NodeKind.MMA0)
I2 = Node("I2", NodeKind.SOFTMAX)
I3 = Node("I3", NodeKind.MMA1)

G = (
    # Vertices.
    [I1, I2, I3],
    # Edges.
    [
        Edge(0, 1, (I1.cost(), 0)),
        Edge(1, 2, (I2.cost(), 0)),
        Edge(2, 2, (I3.cost(), 1))
    ]
)

def schedule_graph(G, II, R):
    V, E = G
    # Variables to create:
    # 1) T, start time of each operation.
    # 2) A matrix, entry for each N and II.
    # 3) The K vector? (need to do the floor division here too?)
    # 4) The b vector.
    T = LpVariable.dicts("T", [i for i in range(len(V))], lowBound=0, cat=LpInteger)
    # TODO (rohany): Explain...
    K = LpVariable.dicts("K", [i for i in range(len(V))], lowBound=0, cat=LpInteger)
    A = LpVariable.dicts("A", [(t, i) for t in range(II) for i in range(len(V))], cat=LpBinary)
    B = LpVariable.dicts("buffer_sizes", [i for i in range(len(V))], lowBound=0, cat=LpInteger)

    prob = LpProblem("scheduling", LpMinimize)

    # Minimizing the lifetimes gives a different schedule
    # than minimizing the span, which is a bit interesting.

    # Target: minimize the buffer sizes.
    # prob += lpSum([B[i] for i in range(len(V))])

    # Target option 2: minimize the span of the resulting schedule.
    span = LpVariable("span", lowBound=0, cat=LpInteger)
    prob += span
    for i in range(len(V)):
        prob += T[i] + V[i].cost() <= span

    # Each job can only start once.
    for i in range(0, len(V)):
        prob += (lpSum([A[t,i] for t in range(II)]) == 1)

    # Precedence constraints.
    for i in range(len(V)):
        prob += (T[i] == (II * K[i] + lpSum([A[t, i] * t for t in range(II)])))

    # Dependence constraints.
    for edge in E:
        prob += (T[edge.dst] - T[edge.src] >= edge.dep[0] - II * edge.dep[1])

    # Buffer constraints.
    # for edge in E:
    #     prob += ((II * B[edge.src] + T[edge.src] - T[edge.dst]) >= (II * (edge.dep[1] + 1) - 1))

    # Resource constraints.
    for s in range(len(R)):
        for t in range(II):
            prob += (lpSum([
                A[(t - l) % II, i] * V[i].restable(II)[l][s]
                for i in range(len(V))
                for l in range(II)
            ]) <= R[s])

    # We don't have to encode this in the problem, it's just a logical thing...
    # Floor division constraints for K.
    # for i in range(len(V)):
    #     prob += (T[i] - K[i] * II >= 0)
    #     # Should be T[i] - K[i] * (II + 1) < 0, but pulp only supports <=.
    #     prob += (T[i] - K[i] * (II + 1) <= -1)

    prob.solve()

    tmin = min([value(T[i]) for i in range(len(V))])

    print("===================")

    for i, v in enumerate(V):
        print(v, value(T[i]), value(T[i]) - tmin, value(K[i]), value(B[i]))

    print("===================")

    for t in range(II):
        print(" ".join([str(value(A[t, i])) for i in range(len(V))]))


# Try to schedule with different IIs...
schedule_graph(G, 4, [1, 1])
