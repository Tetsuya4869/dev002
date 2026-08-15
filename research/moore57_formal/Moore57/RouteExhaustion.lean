import Moore57.Holonomy

/-!
# Exhaustion of all symbols by direct and two-step routes

Fix two distinct non-base branches `i,j` and a starting symbol `x`. There are
exactly 56 route labels available: `i` represents the stationary/base route,
`j` the direct edge, and every other non-base branch a genuine two-step route.
The short-cycle constraints force all 56 endpoints to be distinct; equal finite
cardinalities therefore make the route map bijective.
-/

namespace Moore57

universe u v

noncomputable def routeEndpoint {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    (i j : NonBase D) (x : S) (r : NonBase D) : S := by
  classical
  exact if r = i then x
    else if r = j then D.phi i.1 j.1 x
    else twoStep D i j r x

@[simp] theorem routeEndpoint_at_i {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) (i j : NonBase D) (x : S) :
    routeEndpoint D i j x i = x := by
  classical
  simp [routeEndpoint]

@[simp] theorem routeEndpoint_at_j {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j : NonBase D} (hij : i ≠ j) (x : S) :
    routeEndpoint D i j x j = D.phi i.1 j.1 x := by
  classical
  simp [routeEndpoint, Ne.symm hij]

@[simp] theorem routeEndpoint_at_other {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j r : NonBase D}
    (hri : r ≠ i) (hrj : r ≠ j) (x : S) :
    routeEndpoint D i j x r = twoStep D i j r x := by
  classical
  simp [routeEndpoint, hri, hrj]

/-- The full route endpoint map is injective. -/
theorem routeEndpoint_injective {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j : NonBase D} (hij : i ≠ j) (x : S) :
    Function.Injective (routeEndpoint D i j x) := by
  classical
  have hji : j ≠ i := Ne.symm hij
  intro r s hrs
  by_cases hri : r = i
  · by_cases hsi : s = i
    · exact hri.trans hsi.symm
    · by_cases hsj : s = j
      · have heq : x = D.phi i.1 j.1 x := by
          simpa [routeEndpoint, hri, hsi, hsj, hji] using hrs
        exact False.elim ((direct_ne_self D hij x) heq.symm)
      · have heq : x = twoStep D i j s x := by
          simpa [routeEndpoint, hri, hsi, hsj, hji] using hrs
        exact False.elim
          ((twoStep_ne_self D hij (Ne.symm hsi) hsj x) heq.symm)
  · by_cases hrj : r = j
    · by_cases hsi : s = i
      · have heq : D.phi i.1 j.1 x = x := by
          simpa [routeEndpoint, hri, hrj, hsi, hji] using hrs
        exact False.elim ((direct_ne_self D hij x) heq)
      · by_cases hsj : s = j
        · exact hrj.trans hsj.symm
        · have heq : D.phi i.1 j.1 x = twoStep D i j s x := by
            simpa [routeEndpoint, hri, hrj, hsi, hsj, hji] using hrs
          exact False.elim
            ((twoStep_ne_direct D hij (Ne.symm hsi) hsj x) heq.symm)
    · by_cases hsi : s = i
      · have heq : twoStep D i j r x = x := by
          simpa [routeEndpoint, hri, hrj, hsi, hji] using hrs
        exact False.elim
          ((twoStep_ne_self D hij (Ne.symm hri) hrj x) heq)
      · by_cases hsj : s = j
        · have heq : twoStep D i j r x = D.phi i.1 j.1 x := by
            simpa [routeEndpoint, hri, hrj, hsi, hsj, hji] using hrs
          exact False.elim
            ((twoStep_ne_direct D hij (Ne.symm hri) hrj x) heq)
        · by_cases hrsEq : r = s
          · exact hrsEq
          · have heq : twoStep D i j r x = twoStep D i j s x := by
              simpa [routeEndpoint, hri, hrj, hsi, hsj, hji] using hrs
            exact False.elim
              ((twoStep_ne_twoStep D hij
                (Ne.symm hri) hrj (Ne.symm hsi) hsj hrsEq x) heq)

/-- Equal finite cardinalities upgrade route injectivity to route bijectivity. -/
theorem routeEndpoint_bijective_of_card_eq
    {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    {i j : NonBase D} (hij : i ≠ j) (x : S)
    [Fintype (NonBase D)] [Fintype S]
    (hcard : Fintype.card (NonBase D) = Fintype.card S) :
    Function.Bijective (routeEndpoint D i j x) := by
  have hinj := routeEndpoint_injective D hij x
  let e : NonBase D ≃ S := Fintype.equivOfCardEq hcard
  exact ⟨hinj, hinj.surjective_of_finite e⟩

/-- Degree-57 specialization: all 56 symbols occur exactly once among the 56 routes. -/
theorem routeEndpoint_order56_bijective
    {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    {i j : NonBase D} (hij : i ≠ j) (x : S)
    [Fintype (NonBase D)] [Fintype S]
    (hB : Fintype.card (NonBase D) = 56)
    (hS : Fintype.card S = 56) :
    Function.Bijective (routeEndpoint D i j x) := by
  apply routeEndpoint_bijective_of_card_eq D hij x
  rw [hB, hS]

/--
Every symbol other than `x` and the direct endpoint is reached by a unique
proper intermediate branch.
-/
theorem existsUnique_intermediate_for_target
    {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    {i j : NonBase D} (hij : i ≠ j) (x y : S)
    [Fintype (NonBase D)] [Fintype S]
    (hcard : Fintype.card (NonBase D) = Fintype.card S)
    (hyx : y ≠ x) (hyd : y ≠ D.phi i.1 j.1 x) :
    ∃! k : Intermediate D i j, twoStep D i j k.1 x = y := by
  classical
  have hji : j ≠ i := Ne.symm hij
  obtain ⟨r, hr⟩ := (routeEndpoint_bijective_of_card_eq D hij x hcard).2 y
  have hri : r ≠ i := by
    intro hri
    subst r
    simp at hr
    exact hyx hr.symm
  have hrj : r ≠ j := by
    intro hrj
    subst r
    simp [routeEndpoint, hji] at hr
    exact hyd hr.symm
  let k : Intermediate D i j := ⟨r, hri, hrj⟩
  have hk : twoStep D i j k.1 x = y := by
    simpa [k, routeEndpoint, hri, hrj, hji] using hr
  refine ⟨k, hk, ?_⟩
  intro l hl
  apply twoStep_injective_intermediate D hij x
  exact hl.trans hk.symm

end Moore57
