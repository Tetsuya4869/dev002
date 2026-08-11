import Moore57.LatinCube

/-!
# Finite Latin cubes from the Moore short-cycle system

The previous module proves coordinatewise injectivity without finiteness assumptions.
Here we use equal finite cardinalities to upgrade every coordinate map to a bijection.
For the degree-57 Moore reduction, the non-base branch set and the symbol set both
have cardinality 56, so the resulting ternary array is a genuine Latin cube, i.e. a
ternary quasigroup.
-/

namespace Moore57

universe u v

/-- A coordinatewise-bijective ternary array. -/
structure IsLatinCube {A B C D : Type*} (T : A → B → C → D) : Prop where
  first : ∀ b c, Function.Bijective (fun a => T a b c)
  second : ∀ a c, Function.Bijective (fun b => T a b c)
  third : ∀ a b, Function.Bijective (fun c => T a b c)

/--
For finite coordinate sets of equal size, an injective Latin cube is a genuine
Latin cube.  The equivalence supplied by equal cardinality converts injectivity
into surjectivity in the first two coordinates; the third coordinate is an
endofunction and uses the finite pigeonhole principle directly.
-/
theorem injectiveLatinCube_of_card_eq
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (T : A → B → C → D)
    (hT : IsInjectiveLatinCube T)
    (hAD : Fintype.card A = Fintype.card D)
    (hBD : Fintype.card B = Fintype.card D)
    (hCD : Fintype.card C = Fintype.card D) :
    IsLatinCube T := by
  let eAD : A ≃ D := Fintype.equivOfCardEq hAD
  let eBD : B ≃ D := Fintype.equivOfCardEq hBD
  let eCD : C ≃ D := Fintype.equivOfCardEq hCD
  refine ⟨?_, ?_, ?_⟩
  · intro b c
    have hinj := hT.first b c
    exact ⟨hinj, hinj.surjective_of_finite eAD⟩
  · intro a c
    have hinj := hT.second a c
    exact ⟨hinj, hinj.surjective_of_finite eBD⟩
  · intro a b
    have hinj := hT.third a b
    exact ⟨hinj, hinj.surjective_of_finite eCD⟩

/--
The normalized short-cycle system yields a genuine Latin cube whenever the
non-base branch set and symbol set have the same finite cardinality.
-/
theorem shortCycles_give_latinCube_of_card_eq
    {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    [Fintype (NonBase D)] [Fintype S]
    (hcard : Fintype.card (NonBase D) = Fintype.card S) :
    IsLatinCube (latinEntry D) := by
  exact injectiveLatinCube_of_card_eq (latinEntry D)
    (shortCycles_give_injectiveLatinCube D) hcard hcard rfl

/-- Degree-57 specialization: 56 non-base branches and 56 symbols. -/
theorem shortCycles_order56_give_latinCube
    {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    [Fintype (NonBase D)] [Fintype S]
    (hB : Fintype.card (NonBase D) = 56)
    (hS : Fintype.card S = 56) :
    IsLatinCube (latinEntry D) := by
  apply shortCycles_give_latinCube_of_card_eq D
  rw [hB, hS]

/--
Package the additional all-involution identities that survive the reduction.
This is deliberately weaker than any associativity or group law: it records only
what is forced by the Moore short-cycle constraints and involutivity.
-/
structure IsSymmetricInvolutiveLatinCube
    {A C : Type*} (T : A → A → C → C) : Prop where
  latin : IsLatinCube T
  symmetric : ∀ a b c, T a b c = T b a c
  diagonal : ∀ a c, T a a c = c
  offdiag_fixedPointFree : ∀ {a b}, a ≠ b → ∀ c, T a b c ≠ c
  fibre_involutive : ∀ a b, Function.Involutive (T a b)

/--
In the all-involution case, the degree-57 reduction is a symmetric involutive
Latin cube of order 56 with identity diagonal and fixed-point-free off-diagonal
fibres.
-/
theorem shortCycles_allInvolution_order56
    {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    [Fintype (NonBase D)] [Fintype S]
    (hB : Fintype.card (NonBase D) = 56)
    (hS : Fintype.card S = 56)
    (hinv : ∀ i j, Function.Involutive (D.phi i j)) :
    IsSymmetricInvolutiveLatinCube (latinEntry D) := by
  refine ⟨shortCycles_order56_give_latinCube D hB hS, ?_, ?_, ?_, ?_⟩
  · intro a b c
    exact latinEntry_symm_of_involutive D hinv a b c
  · intro a c
    exact latinEntry_diag D a c
  · intro a b hab c
    exact latinEntry_offdiag_ne D hab c
  · intro a b c
    exact hinv a.1 b.1 c

end Moore57
