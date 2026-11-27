# A counterexample to Written on the Wall II Conjecture 430c

Conjecture 430c states that every finite simple connected graph on more than three vertices satisfies
`i(G) ≤ λ_max(G) res(G²) + Δ(G[M])`. Here `i` is the independent
domination number, `λ_max` is the largest independence number of an open
neighborhood, `res` is the Havel–Hakimi residue, and `M` is the set of
vertices of maximum degree. [Original catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html)

Start from the complete bipartite graph K₃,₃, attach a new leaf at one
original vertex on each side, and take the line graph. Its eleven
vertices correspond to the nine original edges and two pendant edges.
Independent dominating sets in the line graph correspond to maximal
matchings in the bipartite graph. Every maximal matching saturates all
three original vertices on at least one side, and the original K₃,₃ has
a perfect matching. Thus the independent domination number is three.
The graph square is complete and has residue one. The largest independent
subset of an open neighborhood has size two. The graph has a unique
maximum-degree vertex, so its induced maximum-degree subgraph has degree
zero. The proposed upper bound equals two.

## What Lean checks

[Challenge.lean](Challenge.lean) states the catalogue conjecture and
the numerical counterexample. [Solution.lean](Solution.lean) proves all
four numerical invariant values and connectedness, then derives the
negation of the catalogue conjecture. The proof checks the finite graph
with Lean's kernel and uses standard axioms only. The paper also gives
an unbounded-gap family. The Lean submission covers the eleven-vertex
member and the resulting disproof. [Paper source](graffiti-430c.tex)

```sh
lake exe cache get Challenge.lean Solution.lean
lake build +Challenge +Solution
python3 verify_430c.py
```

Yuvulmaster maintains this project. OpenAI Codex assisted with the
construction, proof, write-up, Python verification, and Lean
formalization. Independent human mathematical review has yet to be
reported.
