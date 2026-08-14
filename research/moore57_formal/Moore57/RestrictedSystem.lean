import Moore57.RouteExhaustion

/-!
# Restricted all-involution systems

The computational search selects only a subset of the 56 non-base branches.  This
file formalizes the solver-independent logical bridge: every full normalized
all-involution short-cycle system restricts to a system on any injectively selected
branch type, and all of the fixed-point-free, star-distinctness, and route-distinctness
constraints used by the search survive that restriction.
-/

namespace Moore57

universe u v w

/--
An abstract certificate matching the structural constraints imposed by the restricted
all-involution search.  It is deliberately solver-agnostic.
-/
structure RestrictedAllInvolutionSystem (T : Type u) (S : Type v) where
  p : T → T → Equiv.Perm S
  diag : ∀ a, p a a = 1
  symmetric : ∀ a b, p a b = p b a
  involutive : ∀ a b, Function.Involutive (p a b)
  offdiag_fixedPointFree : ∀ {a b}, a ≠ b → ∀ x, p a b x ≠ x
  star_injective : ∀ a x, Function.Injective (fun b => p a b x)
  route : T → T → S → T → S
  route_at_self : ∀ {a b}, a ≠ b → ∀ x, route a b x a = x
  route_at_direct : ∀ {a b}, a ≠ b → ∀ x, route a b x b = p a b x
  route_at_other : ∀ {a b r}, a ≠ b → r ≠ a → r ≠ b → ∀ x,
    route a b x r = p r b (p a r x)
  route_injective : ∀ {a b}, a ≠ b → ∀ x, Function.Injective (route a b x)

/--
Any injectively selected family of non-base branches inherits a restricted
all-involution certificate.  Involutivity is assumed only on non-base fibres,
which is exactly the hypothesis used by the search; diagonal and base fibres are
already identities after normalization.
-/
noncomputable def ShortCycleSystem.restrictAllInvolution
    {I : Type w} {S : Type v} (D : ShortCycleSystem I S)
    (hinv : ∀ i j : NonBase D, Function.Involutive (D.phi i.1 j.1))
    {T : Type u} (e : T ↪ NonBase D) : RestrictedAllInvolutionSystem T S where
  p a b := D.phi (e a).1 (e b).1
  diag := by
    intro a
    exact D.diag (e a).1
  symmetric := by
    intro a b
    symm
    rw [D.rev (e a).1 (e b).1,
      perm_inv_eq_self_of_involutive (D.phi (e a).1 (e b).1) (hinv (e a) (e b))]
  involutive := by
    intro a b
    exact hinv (e a) (e b)
  offdiag_fixedPointFree := by
    intro a b hab x
    apply D.offdiag_fixedPointFree (e a).2 (e b).2
    · intro h
      apply hab
      apply e.injective
      exact Subtype.ext h
  star_injective := by
    intro a x b c hbc
    apply e.injective
    apply latinEntry_injective_second D (e a) x
    simpa [latinEntry] using hbc
  route a b x r := routeEndpoint D (e a) (e b) x (e r)
  route_at_self := by
    intro a b hab x
    exact routeEndpoint_at_i D (e a) (e b) x
  route_at_direct := by
    intro a b hab x
    have heab : e a ≠ e b := fun h => hab (e.injective h)
    exact routeEndpoint_at_j D heab x
  route_at_other := by
    intro a b r hab hra hrb x
    have hera : e r ≠ e a := fun h => hra (e.injective h)
    have herb : e r ≠ e b := fun h => hrb (e.injective h)
    simpa [twoStep] using routeEndpoint_at_other D hera herb x
  route_injective := by
    intro a b hab x r s hrs
    have heab : e a ≠ e b := fun h => hab (e.injective h)
    apply e.injective
    exact routeEndpoint_injective D heab x hrs

/--
Contrapositive wrapper: if no restricted certificate exists on a selected branch type,
then no full non-base all-involution system admitting such a selection can exist.
-/
theorem ShortCycleSystem.no_fullAllInvolution_of_no_restriction
    {I : Type w} {S : Type v} (D : ShortCycleSystem I S)
    {T : Type u} (e : T ↪ NonBase D)
    (hNoRestricted : ¬ Nonempty (RestrictedAllInvolutionSystem T S))
    (hinv : ∀ i j : NonBase D, Function.Involutive (D.phi i.1 j.1)) : False := by
  exact hNoRestricted ⟨D.restrictAllInvolution hinv e⟩

end Moore57
