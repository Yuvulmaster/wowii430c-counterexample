module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Multiset.Sort

@[expose] public section

namespace WOWII430c

open Finset SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- All neighbors of a vertex, regarded as a finite set. -/
def neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  univ.filter (G.Adj v)

/-- An independent set contains no two adjacent vertices. -/
def independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Decidable (independent G S) :=
  inferInstanceAs (Decidable (∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w))

/-- An independent dominating set is independent and meets or neighbors every vertex. -/
def independentDominating (G : SimpleGraph V) (S : Finset V) : Prop :=
  independent G S ∧ ∀ v, v ∈ S ∨ ∃ w ∈ S, G.Adj v w

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Decidable (independentDominating G S) :=
  inferInstanceAs (Decidable (independent G S ∧ ∀ v, v ∈ S ∨ ∃ w ∈ S, G.Adj v w))

/-- A graph's vertex subsets. -/
def subsets : Finset (Finset V) := (univ : Finset V).powerset

/-- The size of a smallest independent dominating set. The fallback is unused
because a maximal independent set is dominating. -/
def independentDominationNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (((subsets.filter (independentDominating G)).image Finset.card).min).getD 0

/-- The largest size of an independent subset of any open neighborhood. -/
def neighborhoodIndependence (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  univ.sup fun v : V =>
    ((neighbors G v).powerset.filter (independent G)).sup Finset.card

/-- Adjacency in the square graph means distinct vertices at distance at most two. -/
def squareAdj (G : SimpleGraph V) (v w : V) : Prop :=
  v ≠ w ∧ (G.Adj v w ∨ ∃ x, G.Adj v x ∧ G.Adj x w)

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (squareAdj G) :=
  fun v w => inferInstanceAs (Decidable (_ ≠ _ ∧ (G.Adj v w ∨
    ∃ x, G.Adj v x ∧ G.Adj x w)))

/-- Insert one degree into a descending list of degrees. -/
def insertDegree (d : ℕ) : List ℕ → List ℕ
  | [] => [d]
  | a :: tail => if a ≤ d then d :: a :: tail else a :: insertDegree d tail

/-- Sort a list of degrees into descending order. -/
def sortDegrees (degrees : List ℕ) : List ℕ :=
  degrees.foldr insertDegree []

/-- A descending Havel–Hakimi step deletes the largest positive degree
and subtracts one from the next that many degrees. The residue counts the zeros
when only zeros remain. Fuel equal to the sequence length suffices. -/
def havelHakimi : ℕ → List ℕ → ℕ
  | 0, ds => ds.length
  | n + 1, ds =>
    match sortDegrees ds with
    | [] => 0
    | 0 :: tail => tail.length + 1
    | (d + 1) :: tail =>
      havelHakimi n (((tail.take (d + 1)).map (· - 1)) ++ tail.drop (d + 1))

/-- The Havel–Hakimi residue of the square graph. -/
def squareResidue (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  let degrees := (Finset.univ : Finset V).val.map (fun v =>
    (univ.filter (squareAdj G v)).card)
  let ds := degrees.sort (· ≥ ·)
  havelHakimi ds.length ds

/-- The maximum degree in the subgraph induced by the maximum-degree vertices. -/
def maximumDegreeInduced (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  let maxDeg := univ.sup fun v : V => (neighbors G v).card
  let M := univ.filter fun v : V => (neighbors G v).card = maxDeg
  M.sup fun v => ((neighbors G v) ∩ M).card

/-- The catalogue's proposed upper bound for the independent domination number. -/
def bound (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  neighborhoodIndependence G * squareResidue G + maximumDegreeInduced G

/-- The exact catalogue statement for finite simple connected graphs of order above three. -/
def catalogueConjecture : Prop :=
  ∀ (V : Type) (F : Fintype V) (E : DecidableEq V)
    (G : SimpleGraph V) (D : DecidableRel G.Adj),
    G.Connected → 3 < @Fintype.card V F →
      @independentDominationNumber V F E G D ≤ @bound V F E G D

/-- A connected graph on eleven vertices has independent domination number
three and catalogue bound two. -/
theorem counterexample :
    ∃ (G : SimpleGraph (Fin 11)) (D : DecidableRel G.Adj),
      G.Connected ∧ @independentDominationNumber _ _ _ G D = 3 ∧
      @neighborhoodIndependence _ _ _ G D = 2 ∧ @squareResidue _ _ _ G D = 1 ∧
      @maximumDegreeInduced _ _ _ G D = 0 := by
  sorry

/-- Written on the Wall II, conjecture 430c, is false. -/
theorem conjecture430c_false : ¬ catalogueConjecture := by
  sorry

end WOWII430c
