import Mathlib.Data.Fin.Embedding
import Moore57.SRGConsequences
import Moore57.RestrictedSystem

/-!
# Restricted certificates from an SRG(3250,57,0,1)

There are exactly 56 non-base branches in the graph-derived normalized system.  Hence
for every `t ≤ 56` we can select `Fin t` of them.  If the full normalized system is
all-involution on its non-base fibres, restriction then produces the exact abstract
certificate required by the restricted search.
-/

namespace Moore57

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Canonically select `t` non-base branches whenever `t ≤ 56`. -/
noncomputable def SimpleGraph.IsSRGWith.selectNonBase
    (h : G.IsSRGWith 3250 57 0 1) (r : V)
    (b : (SimpleGraph.IsSRGWith.toMoore57Relation h).Branch r)
    {t : ℕ} (ht : t ≤ 56) :
    Fin t ↪ NonBase (SimpleGraph.IsSRGWith.toShortCycleSystem h r b) := by
  let D := SimpleGraph.IsSRGWith.toShortCycleSystem h r b
  have hcard : Nat.card (NonBase D) = 56 := by
    simpa [D] using SimpleGraph.IsSRGWith.nonBase_natCard_eq_56 h r b
  let e : NonBase D ≃ Fin 56 := Finite.equivFinOfCardEq hcard
  exact (Fin.castLEEmb ht).trans e.symm.toEmbedding

/--
A full non-base all-involution SRG-derived system yields a restricted certificate for
every `t ≤ 56`.
-/
theorem SimpleGraph.IsSRGWith.restricted_certificate_exists
    (h : G.IsSRGWith 3250 57 0 1) (r : V)
    (b : (SimpleGraph.IsSRGWith.toMoore57Relation h).Branch r)
    {t : ℕ} (ht : t ≤ 56)
    (hinv : ∀ i j : NonBase (SimpleGraph.IsSRGWith.toShortCycleSystem h r b),
      Function.Involutive
        ((SimpleGraph.IsSRGWith.toShortCycleSystem h r b).phi i.1 j.1)) :
    Nonempty (RestrictedAllInvolutionSystem (Fin t) (Fin 56)) := by
  let D := SimpleGraph.IsSRGWith.toShortCycleSystem h r b
  let e := SimpleGraph.IsSRGWith.selectNonBase h r b ht
  exact ⟨D.restrictAllInvolution hinv e⟩

/--
Solver-independent contrapositive: proving that no restricted certificate exists for
any single `t ≤ 56` rules out the full normalized non-base all-involution SRG-derived
system.
-/
theorem SimpleGraph.IsSRGWith.no_allInvolution_of_no_restricted
    (h : G.IsSRGWith 3250 57 0 1) (r : V)
    (b : (SimpleGraph.IsSRGWith.toMoore57Relation h).Branch r)
    {t : ℕ} (ht : t ≤ 56)
    (hNo : ¬ Nonempty (RestrictedAllInvolutionSystem (Fin t) (Fin 56))) :
    ¬ (∀ i j : NonBase (SimpleGraph.IsSRGWith.toShortCycleSystem h r b),
      Function.Involutive
        ((SimpleGraph.IsSRGWith.toShortCycleSystem h r b).phi i.1 j.1)) := by
  intro hinv
  exact hNo (SimpleGraph.IsSRGWith.restricted_certificate_exists h r b ht hinv)

end Moore57
