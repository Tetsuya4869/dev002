import Moore57.SRGBridge
import Moore57.LatinCubeFinite
import Moore57.RouteExhaustion

/-!
# End-to-end consequences of an SRG(3250,57,0,1)

This file packages the graph-to-permutation reduction together with the downstream
Latin-cube and route-exhaustion theorems.  The statements start directly from
mathlib's `SimpleGraph.IsSRGWith 3250 57 0 1` hypothesis.
-/

namespace Moore57

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The normalized graph-derived system has exactly 56 non-base branches. -/
theorem SimpleGraph.IsSRGWith.nonBase_natCard_eq_56
    (h : G.IsSRGWith 3250 57 0 1) (r : V)
    (b : (SimpleGraph.IsSRGWith.toMoore57Relation h).Branch r) :
    Nat.card (NonBase (SimpleGraph.IsSRGWith.toShortCycleSystem h r b)) = 56 := by
  change Nat.card {i : (SimpleGraph.IsSRGWith.toMoore57Relation h).Branch r // i ≠ b} = 56
  exact (SimpleGraph.IsSRGWith.toMoore57Relation h).card_nonBase_eq_56_of_degree57
    (SimpleGraph.IsSRGWith.toMoore57Relation_degree h) b

/-- Every SRG(3250,57,0,1) yields the 56-symbol Latin cube used in the reduction. -/
theorem SimpleGraph.IsSRGWith.gives_order56_latinCube
    (h : G.IsSRGWith 3250 57 0 1) (r : V)
    (b : (SimpleGraph.IsSRGWith.toMoore57Relation h).Branch r) :
    IsLatinCube (latinEntry (SimpleGraph.IsSRGWith.toShortCycleSystem h r b)) := by
  classical
  let D := SimpleGraph.IsSRGWith.toShortCycleSystem h r b
  letI : Fintype (NonBase D) := Fintype.ofFinite _
  have hBnat : Nat.card (NonBase D) = 56 := by
    simpa [D] using SimpleGraph.IsSRGWith.nonBase_natCard_eq_56 h r b
  have hB : Fintype.card (NonBase D) = 56 := by
    rw [← Nat.card_eq_fintype_card]
    exact hBnat
  have hS : Fintype.card (Fin 56) = 56 := by simp
  exact shortCycles_order56_give_latinCube D hB hS

/--
For every pair of distinct non-base branches and every starting symbol, the 56 route
endpoints form a permutation of all 56 symbols.
-/
theorem SimpleGraph.IsSRGWith.routeEndpoint_bijective
    (h : G.IsSRGWith 3250 57 0 1) (r : V)
    (b : (SimpleGraph.IsSRGWith.toMoore57Relation h).Branch r)
    {i j : NonBase (SimpleGraph.IsSRGWith.toShortCycleSystem h r b)}
    (hij : i ≠ j) (x : Fin 56) :
    Function.Bijective
      (routeEndpoint (SimpleGraph.IsSRGWith.toShortCycleSystem h r b) i j x) := by
  classical
  let D := SimpleGraph.IsSRGWith.toShortCycleSystem h r b
  letI : Fintype (NonBase D) := Fintype.ofFinite _
  have hBnat : Nat.card (NonBase D) = 56 := by
    simpa [D] using SimpleGraph.IsSRGWith.nonBase_natCard_eq_56 h r b
  have hB : Fintype.card (NonBase D) = 56 := by
    rw [← Nat.card_eq_fintype_card]
    exact hBnat
  have hS : Fintype.card (Fin 56) = 56 := by simp
  change Function.Bijective (routeEndpoint D i j x)
  exact routeEndpoint_order56_bijective D hij x hB hS

end Moore57
