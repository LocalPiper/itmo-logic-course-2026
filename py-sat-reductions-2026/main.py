from pysat.solvers import Solver, Glucose4
from pysat.formula import CNF, IDPool
from itertools import product
from time import perf_counter


class Graph:
    def __init__(self, vertices, edges):
        self.vertices = vertices
        self.edges = edges

    def __repr__(self):
        edges = '\n'.join(f"{f} <-> {t}" for f, t in self.edges)
        return f"Vertices: {' '.join(map(str, self.vertices))}\nEdges:\n{edges}"


class Clique(Graph):
    def __init__(self, size):
        vertices = list(range(1, size + 1))
        edges = [(i, j) for i in vertices for j in range(i + 1, size + 1)]
        super().__init__(vertices, edges)


def either(p1, p2):
    return [-p1, -p2]


class EncoderVerbose:
    def __init__(self, graph, total_colours):
        self.graph = graph
        self.vpool = IDPool()
        self.colours = list(range(1, total_colours+1))
        self.total_colours = total_colours

    def v_has_exactly_one_colour(self, v):
        yield [self.v_has_colour(v, colour) for colour in self.colours]
        for colour1 in self.colours:
            for colour2 in self.colours:
                if colour1 < colour2:
                    yield either(self.v_has_colour(v, colour1), self.v_has_colour(v, colour2))

    def verts_have_different_colours(self, v1, v2):
        for colour in self.colours:
            yield either(self.v_has_colour(v1, colour), self.v_has_colour(v2, colour))

    def encode(self):
        clauses = CNF()
        for v in self.graph.vertices:
            clauses.extend(self.v_has_exactly_one_colour(v))
        for v1, v2 in self.graph.edges:
            clauses.extend(self.verts_have_different_colours(v1, v2))
        return clauses

    def v_has_colour(self, v, colour):
        return self.vpool.id(f"vert_{v}_has_colour_{colour}")

    def id2obj(self, i):
        return self.vpool.id2obj[i]

    def lits_to_str(self, lits, joiner):
        return joiner.join(f"{'¬' if i < 0 else ' '}{self.id2obj(abs(i))}" for i in lits)

    def pprint_lits(self, lits, joiner):
        print(self.lits_to_str(lits, joiner))

    def pprint_clauses(self, clauses):
        for clause in clauses:
            self.pprint_lits(clause, ' ∨ ')

    def pprint_model(self, model):
        self.pprint_lits([l for l in model if l > 0], ',')


class BruteForceSolver:
    def __init__(self):
        self.clauses = []
        self.vars = -1
        self.model = None

    def append_formula(self, clauses):
        self.clauses.extend(clauses.clauses)
        self.vars = clauses.nv

    def get_model(self):
        return [(i if v else -i) for i, v in enumerate(self.model, start=1)]

    def solve(self):
        def eval_clause(model, clause):
            for lit in clause:
                if lit < 0:
                    if not model[-lit-1]:
                        return True
                else:
                    if model[lit-1]:
                        return True
            return False
        def eval_clauses(model):
            for clause in self.clauses:
                if not eval_clause(model, clause):
                    return False
            return True
        for model in product([False, True], repeat=self.vars):
            if eval_clauses(model):
                self.model = model
                return True
        return False


def check(clique_size, colours, solver, verbose=False):
    print(f"Colouring clique of size {clique_size} with {colours} colours")
    graph = Clique(size=clique_size)
    if verbose:
        print(graph)
    encoder = EncoderVerbose(graph, total_colours=colours)
    clauses = encoder.encode()
    clauses.to_file(f"{clique_size}_{colours}.cnf")
    print(f"Vars in encoding: {clauses.nv}")
    print(f"Clauses in encoding: {len(clauses.clauses)}")
    if verbose:
        print(f"Clauses:")
        encoder.pprint_clauses(clauses.clauses)
    solver.append_formula(clauses)
    time_before = perf_counter()
    issat = solver.solve()
    time_after = perf_counter()
    print(f"Elapsed {time_after - time_before:.6f} seconds")
    if issat is True:
        print("SATisfiable")
        print("Model:", end='')
        encoder.pprint_model(solver.get_model())
    elif issat is False:
        print("UNSATisfiable")
        proof = solver.get_proof() if hasattr(solver, 'get_proof') else None
        if proof is None:
            print("No proof: solver does not produce proofs (for Glucose4 pass with_proof=True)")
        else:
            print(f"Proof of unsatisfiability ({len(proof)} steps):")
            print(proof)
            formula = [list(c) for c in clauses.clauses]
            derived_at = {}
            for step, line in enumerate(proof, start=1):
                is_deletion, lits = parse_proof_line(line)
                print(f"{step:>4}. ", end='')
                if is_deletion:
                    print("delete ", end='')
                    encoder.pprint_lits(lits, ' ∨ ')
                    formula = [c for c in formula if set(c) != set(lits)]
                    continue
                print("derive " + (encoder.lits_to_str(lits, ' ∨ ') if lits else "⊥"))
                formula.append(lits)
                derived_at[frozenset(lits)] = step
            if verbose:
                print_resolution_refutation(encoder, clauses.clauses, proof)
    else:
        print("UNKNOWN")
    print('*' * 80)


def parse_proof_line(line):
    tokens = line.split()
    is_deletion = tokens[0] == 'd'
    lits = [int(t) for t in tokens[1 if is_deletion else 0:] if t != '0']
    return is_deletion, lits


def rup_trace(formula, clause):
    assignment = {-lit for lit in clause}
    trace = []
    changed = True
    while changed:
        changed = False
        for c in formula:
            if any(lit in assignment for lit in c):
                continue
            free = [lit for lit in c if -lit not in assignment]
            if not free:
                return trace, c
            if len(free) == 1:
                assignment.add(free[0])
                trace.append((free[0], c))
                changed = True
    return trace, None


def relevant_part(trace, conflict):
    needed = {-lit for lit in conflict}
    result = []
    for lit, c in reversed(trace):
        if lit in needed:
            result.append((lit, c))
            needed |= {-other for other in c if other != lit}
    return result[::-1]


def explain_rup_step(encoder, formula, lits, derived_at):
    def clause_str(c):
        step = derived_at.get(frozenset(c))
        text = encoder.lits_to_str(c, ' ∨ ') if c else "⊥"
        return text + (f"   [step {step}]" if step else "")

    trace, conflict = rup_trace(formula, lits)
    indent = ' ' * 13
    if conflict is None:
        print(f"{indent}no contradiction: step is not RUP")
        return
    current = list(conflict)
    print(f"{indent}  {clause_str(current)}")
    for lit, c in reversed(relevant_part(trace, conflict)):
        if -lit not in current:
            continue
        resolvent = [l for l in current if l != -lit]
        resolvent += [l for l in c if l != lit and l not in resolvent]
        print(f"{indent}+ {clause_str(c)}")
        print(f"{indent}= {clause_str(resolvent)}")
        current = resolvent


def resolution_refutation(clauses, proof):
    nodes = []
    node_by_key = {}

    def add_node(clause, parent1=None, parent2=None, var=None):
        key = frozenset(clause)
        if key not in node_by_key:
            node_by_key[key] = len(nodes)
            nodes.append((list(clause), parent1, parent2, var))
        return node_by_key[key]

    active = {}
    for c in clauses:
        active[frozenset(c)] = add_node(c)
    for line in proof:
        is_deletion, lits = parse_proof_line(line)
        if is_deletion:
            active.pop(frozenset(lits), None)
            continue
        formula = [nodes[i][0] for i in active.values()]
        node_of = {id(nodes[i][0]): i for i in active.values()}
        trace, conflict = rup_trace(formula, lits)
        if conflict is None:
            raise ValueError(f"proof step is not RUP: {line}")
        current = node_of[id(conflict)]
        for lit, c in reversed(relevant_part(trace, conflict)):
            clause = nodes[current][0]
            if -lit not in clause:
                continue
            resolvent = [l for l in clause if l != -lit]
            resolvent += [l for l in c if l != lit and l not in resolvent]
            current = add_node(resolvent, current, node_of[id(c)], abs(lit))
        active[frozenset(lits)] = current
        if not lits:
            return nodes, current
    raise ValueError("proof does not derive the empty clause")


def print_resolution_refutation(encoder, clauses, proof):
    nodes, empty = resolution_refutation(clauses, proof)
    used = set()
    stack = [empty]
    while stack:
        i = stack.pop()
        if i not in used:
            used.add(i)
            stack.extend(p for p in nodes[i][1:3] if p is not None)
    order = sorted(used, key=lambda i: (nodes[i][1] is not None, i))
    number = {i: n for n, i in enumerate(order, start=1)}
    texts = {i: encoder.lits_to_str(nodes[i][0], ' ∨ ') if nodes[i][0] else "⊥" for i in order}
    width = max(len(t) for t in texts.values())
    derived = sum(nodes[i][1] is not None for i in order)
    print(f"Resolution refutation ({len(order) - derived} given clauses, {derived} resolution steps):")
    for i in order:
        clause, parent1, parent2, var = nodes[i]
        if parent1 is None:
            origin = "given"
        else:
            origin = f"from {number[parent1]}, {number[parent2]} on {encoder.id2obj(var)}"
        print(f"{number[i]:>5}. {texts[i].ljust(width)}   {origin}")


def checkMany(slow=False):
    check(clique_size=4, colours=4, solver=BruteForceSolver())
    check(clique_size=5, colours=4, solver=BruteForceSolver())
    if slow:
        check(clique_size=6, colours=4, solver=BruteForceSolver())
    limit = 11 if slow else 10
    for colours in range(4, limit):
        check(clique_size=colours, colours=colours - 1, solver=Glucose4(with_proof=True))     # UNSAT
        check(clique_size=colours, colours=colours, solver=Glucose4(with_proof=True))       # SAT
    limit = 5 if slow else 4
    for i in range(1, limit):
        colours = 4 ** i
        check(clique_size=colours, colours=colours, solver=Glucose4(with_proof=True))


if __name__ == '__main__':
    check(clique_size=4, colours=4, solver=Glucose4(with_proof=True), verbose=True)
    # checkMany(slow=True)
