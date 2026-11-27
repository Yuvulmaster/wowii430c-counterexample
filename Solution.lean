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

section Witness

/-- The nine edges of K₃,₃, followed by one pendant edge on each side.
The two pendant edges attach at original vertices 0 and 3. -/
private def endpoints (i : Fin 11) : Fin 8 × Fin 8 :=
  if i.val < 9 then
    (⟨i.val / 3, by omega⟩, ⟨3 + i.val % 3, by omega⟩)
  else if i.val = 9 then (0,6) else (3,7)

private def adjacent (i j : Fin 11) : Prop :=
  let (a,b) := endpoints i
  let (c,d) := endpoints j
  i ≠ j ∧ (a = c ∨ a = d ∨ b = c ∨ b = d)

private instance : DecidableRel adjacent := by
  intro i j
  unfold adjacent
  infer_instance

/-- The line graph of K₃,₃ with the two additional pendant edges. -/
private def witness : SimpleGraph (Fin 11) where
  Adj := adjacent
  symm := ⟨by
    intro i j h
    rcases h with ⟨hne,h⟩
    exact ⟨hne.symm, by
      rcases h with h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr (Or.inl h.symm))
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inr h.symm))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance : DecidableRel witness.Adj := by
  change DecidableRel adjacent
  infer_instance

private theorem witness_connected : witness.Connected := by
  have h : ∀ u v : Fin 11, u = v ∨ witness.Adj u v ∨
      ∃ w : Fin 11, witness.Adj u w ∧ witness.Adj w v := by decide
  apply witness.connected_iff_exists_forall_reachable.mpr
  refine ⟨0, fun v => ?_⟩
  rcases h 0 v with he | ha | ⟨w,ha,hb⟩
  · subst v
    exact .rfl
  · exact ha.reachable
  · exact ha.reachable.trans hb.reachable

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
private theorem witness_domination : independentDominationNumber witness = 3 := by
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
private theorem witness_neighborhood : neighborhoodIndependence witness = 2 := by
  decide

set_option maxRecDepth 4000 in
private theorem witness_residue : squareResidue witness = 1 := by
  have hdegree : (fun v : Fin 11 =>
      (univ.filter (squareAdj witness v)).card) = fun _ => 10 := by
    funext v
    exact (by decide : ∀ v : Fin 11, (univ.filter (squareAdj witness v)).card = 10) v
  simp only [squareResidue, hdegree, Multiset.map_const', ← Finset.card_def,
    Finset.card_univ, Fintype.card_fin]
  change havelHakimi
    ((Multiset.sort ((List.replicate 11 10 : Multiset ℕ)) (· ≥ ·)).length)
    (Multiset.sort ((List.replicate 11 10 : Multiset ℕ)) (· ≥ ·)) = 1
  rw [Multiset.coe_sort, List.mergeSort_eq_self (r := (· ≥ ·))]
  · decide +kernel
  · decide

private theorem witness_induced_degree : maximumDegreeInduced witness = 0 := by
  decide

end Witness

/-- A connected graph on eleven vertices has independent domination number
three and catalogue bound two. -/
theorem counterexample :
    ∃ (G : SimpleGraph (Fin 11)) (D : DecidableRel G.Adj),
      G.Connected ∧ @independentDominationNumber _ _ _ G D = 3 ∧
      @neighborhoodIndependence _ _ _ G D = 2 ∧ @squareResidue _ _ _ G D = 1 ∧
      @maximumDegreeInduced _ _ _ G D = 0 := by
  exact ⟨witness, inferInstance, witness_connected, witness_domination,
    witness_neighborhood, witness_residue, witness_induced_degree⟩

/-- Written on the Wall II, conjecture 430c, is false. -/
theorem conjecture430c_false : ¬ catalogueConjecture := by
  intro h
  obtain ⟨G,D,hG,hi,hn,hr,hm⟩ := counterexample
  have hc := h (Fin 11) inferInstance inferInstance G D hG (by decide)
  rw [hi, bound, hn, hr, hm] at hc
  omega

end WOWII430c

#print axioms WOWII430c.counterexample
#print axioms WOWII430c.conjecture430c_false
