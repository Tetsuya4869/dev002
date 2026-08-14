import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Moore57.Degree57Coordinates

/-!
# Bridge from mathlib strongly regular graphs

The hypothetical degree-57 Moore graph is customarily represented by the strongly
regular parameters `(3250,57,0,1)`.  This file translates mathlib's standard
`SimpleGraph.IsSRGWith 3250 57 0 1` structure into the small `MooreRelation` interface
used by the formal rooted reduction.
-/

namespace Moore57

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A mathlib SRG(3250,57,0,1) supplies the Moore local relation axioms. -/
noncomputable def SimpleGraph.IsSRGWith.toMoore57Relation
    (h : G.IsSRGWith 3250 57 0 1) : MooreRelation V where
  adj := G.Adj
  symm := fun ha => G.adj_symm ha
  irrefl := fun v => G.irrefl
  noTriangle := by
    intro x y z hxy hyz hzx
    have hzero : Fintype.card (G.commonNeighbors x y) = 0 := h.of_adj x y hxy
    have hempty : IsEmpty (G.commonNeighbors x y) := Fintype.card_eq_zero_iff.mp hzero
    let zc : G.commonNeighbors x y := ⟨z, by
      exact ⟨G.adj_symm hzx, hyz⟩⟩
    exact isEmptyElim zc
  uniqueCommon := by
    intro x y hxy hnxy
    have hone : Fintype.card (G.commonNeighbors x y) = 1 := h.of_not_adj hxy hnxy
    obtain ⟨c, hc⟩ := Fintype.card_eq_one_iff.mp hone
    refine ⟨c.1, ?_, ?_⟩
    · exact c.2
    · intro z hz
      let zc : G.commonNeighbors x y := ⟨z, hz⟩
      exact congrArg Subtype.val (hc zc)

/-- The SRG regularity field is exactly the degree-57 cardinality hypothesis used downstream. -/
theorem SimpleGraph.IsSRGWith.toMoore57Relation_degree
    (h : G.IsSRGWith 3250 57 0 1) :
    ∀ v : V, Nat.card ((h.toMoore57Relation).Neighbor v) = 57 := by
  intro v
  rw [Nat.card_eq_fintype_card]
  change Fintype.card (G.neighborSet v) = 57
  rw [G.card_neighborSet_eq_degree]
  exact h.regular.degree_eq v

/--
A standard SRG(3250,57,0,1), a root, and a chosen root-neighbour therefore produce
the normalized 56-symbol short-cycle system used by the later Lean development.
-/
noncomputable def SimpleGraph.IsSRGWith.toShortCycleSystem
    (h : G.IsSRGWith 3250 57 0 1) (r : V)
    (b : (h.toMoore57Relation).Branch r) :
    ShortCycleSystem ((h.toMoore57Relation).Branch r) (Fin 56) :=
  (h.toMoore57Relation).toDegree57ShortCycleSystem r h.toMoore57Relation_degree b

end Moore57
