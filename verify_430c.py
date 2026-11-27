"""Rebuild and verify the counterexample to Graffiti.pc 430c. Python 3.8+."""
from itertools import combinations


def graph(n, edges):
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        assert 0 <= u < n and 0 <= v < n and u != v
        adjacency[u].add(v)
        adjacency[v].add(u)
    assert len(components(adjacency, range(n))) == 1
    return adjacency


def components(g, vertices):
    unseen = set(vertices)
    parts = []
    while unseen:
        part = {unseen.pop()}
        queue = list(part)
        for u in queue:
            new = g[u] & unseen
            unseen -= new
            part.update(new)
            queue.extend(new)
        parts.append(sorted(part))
    return parts


def subsets(vertices):
    vertices = sorted(vertices)
    for size in range(len(vertices) + 1):
        for group in combinations(vertices, size):
            yield set(group)


def independence(g, vertices):
    return max(len(s) for s in subsets(vertices) if all(not (g[v] & s) for v in s))


def neighborhood(g, vertices):
    return {w for v in vertices for w in g[v]}


def residue(g):
    degrees = sorted(map(len, g), reverse=True)
    while degrees and degrees[0]:
        d, rest = degrees[0], degrees[1:]
        for j in range(d):
            rest[j] -= 1
        degrees = sorted(rest, reverse=True)
    return len(degrees)


def main():
    k = 3
    base = [(a, b) for a in range(k) for b in range(k, 2*k)]
    base += [(0, 2*k), (k, 2*k + 1)]
    n = len(base)
    g = graph(n, [(i, j) for i, j in combinations(range(n), 2)
                  if set(base[i]) & set(base[j])])
    vertices = set(range(n))
    independent_dom = min(len(s) for s in subsets(vertices)
                          if all(not (g[v] & s) for v in s)
                          and all(g[v] & s for v in vertices - s))
    square = [(ns | neighborhood(g, ns)) - {v} for v, ns in enumerate(g)]
    local = max(independence(g, ns) for ns in g)
    maximum = {v for v in vertices if len(g[v]) == max(map(len, g))}
    induced_degree = max(len(g[v] & maximum) for v in maximum)
    res = residue(square)
    bound = local * res + induced_degree
    assert (n, independent_dom, local, res, induced_degree, bound) == (11, 3, 2, 1, 0, 2)
    print(f"#430c: {n} vertices; independent domination {independent_dom} > {local} * {res} + {induced_degree} = {bound}")


if __name__ == "__main__":
    main()
