import Mathlib

/-!
# Short-cycle constraints force a Latin-cube structure

This file isolates a safe structural consequence of the normalized permutation
construction for a Moore graph of diameter two.  We do not assume that the
permutations form a group.

After choosing a distinguished base branch, the absence of triangles and
4-cycles forces the array

`T(i,r,x) = phi i r x`

on the non-base branches to be injective in each coordinate.  In the finite
Moore-57 situation the three coordinate sets all have cardinality 56, so these
coordinate maps are permutations and `T` is a Latin cube (ternary quasigroup).

The optional all-involution hypothesis adds symmetry in the first two
coordinates and fixed-point-free off-diagonal fibres.
-/

namespace Moore57

universe u v

/--
A normalized system of branch-to-branch matching permutations with the only
short-cycle information needed below.
-/
structure ShortCycleSystem (I : Type u) (S : Type v) where
  base : I
  phi : I → I → Equiv.Perm S
  diag : ∀ i, phi i i = 1
  rev : ∀ i j, phi j i = (phi i j)⁻¹
  normalized : ∀ i, phi base i = 1
  no3 : ∀ {i j k}, i ≠ j → j ≠ k → k ≠ i → ∀ x,
    phi k i (phi j k (phi i j x)) ≠ x
  no4 : ∀ {i j k l},
    i ≠ j → j ≠ k → k ≠ l → l ≠ i → i ≠ k → j ≠ l → ∀ x,
    phi l i (phi k l (phi j k (phi i j x))) ≠ x

/-- The non-base branch type. -/
abbrev NonBase {I : Type u} {S : Type v} (D : ShortCycleSystem I S) :=
  {i : I // i ≠ D.base}

/-- Reverse normalization: every matching into the base is also the identity. -/
theorem ShortCycleSystem.phi_toBase {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) (i : I) : D.phi i D.base = 1 := by
  rw [D.rev D.base i, D.normalized i]
  simp

/--
For two distinct non-base branches, the matching permutation has no fixed
point.  The proof is exactly the forbidden triangle through the base branch.
-/
theorem ShortCycleSystem.offdiag_fixedPointFree {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j : I}
    (hib : i ≠ D.base) (hjb : j ≠ D.base) (hij : i ≠ j) (x : S) :
    D.phi i j x ≠ x := by
  have hcycle := D.no3 (i := D.base) (j := i) (k := j)
    hib.symm hij hjb x
  simpa [D.normalized i, D.phi_toBase j] using hcycle

/-- The ternary array obtained from the branch matching permutations. -/
def latinEntry {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    (i r : NonBase D) (x : S) : S :=
  D.phi i.1 r.1 x

/-- Every symbol-line is injective because each `phi i r` is a permutation. -/
theorem latinEntry_injective_third {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) (i r : NonBase D) :
    Function.Injective (fun x : S => latinEntry D i r x) := by
  exact (D.phi i.1 r.1).injective

/--
For a fixed square index `i` and symbol `x`, the values obtained by varying the
row `r` are all distinct.  A collision either creates an off-diagonal fixed
point or closes a forbidden 4-cycle through the normalized base.
-/
theorem latinEntry_injective_second {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) (i : NonBase D) (x : S) :
    Function.Injective (fun r : NonBase D => latinEntry D i r x) := by
  intro r s hrs
  apply Subtype.ext
  by_contra hrsne
  by_cases hri : r.1 = i.1
  · have his : i.1 ≠ s.1 := by
      intro his
      apply hrsne
      exact hri.trans his
    have hfix : D.phi i.1 s.1 x = x := by
      calc
        D.phi i.1 s.1 x = D.phi i.1 r.1 x := hrs.symm
        _ = D.phi i.1 i.1 x := by rw [hri]
        _ = x := by rw [D.diag]
    exact (D.offdiag_fixedPointFree i.2 s.2 his x) hfix
  · by_cases hsi : s.1 = i.1
    · have hir : i.1 ≠ r.1 := hri.symm
      have hfix : D.phi i.1 r.1 x = x := by
        calc
          D.phi i.1 r.1 x = D.phi i.1 s.1 x := hrs
          _ = D.phi i.1 i.1 x := by rw [hsi]
          _ = x := by rw [D.diag]
      exact (D.offdiag_fixedPointFree i.2 r.2 hir x) hfix
    · have hcycle := D.no4
        (i := i.1) (j := r.1) (k := D.base) (l := s.1)
        hri.symm r.2 s.2.symm hsi i.2 hrsne x
      have hneq : D.phi s.1 i.1 (D.phi i.1 r.1 x) ≠ x := by
        simpa [D.normalized s.1, D.phi_toBase r.1] using hcycle
      have heq : D.phi s.1 i.1 (D.phi i.1 r.1 x) = x := by
        rw [hrs, D.rev i.1 s.1]
        simp
      exact hneq heq

/--
At a fixed cell `(r,x)`, all square indices `i` give different values.  Again,
a collision closes a forbidden 4-cycle through the base branch.
-/
theorem latinEntry_injective_first {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) (r : NonBase D) (x : S) :
    Function.Injective (fun i : NonBase D => latinEntry D i r x) := by
  intro i j hijval
  apply Subtype.ext
  by_contra hij
  by_cases hir : i.1 = r.1
  · have hjr : j.1 ≠ r.1 := by
      intro hjr
      apply hij
      exact hir.trans hjr.symm
    have hfix : D.phi j.1 r.1 x = x := by
      calc
        D.phi j.1 r.1 x = D.phi i.1 r.1 x := hijval.symm
        _ = D.phi r.1 r.1 x := by rw [hir]
        _ = x := by rw [D.diag]
    exact (D.offdiag_fixedPointFree j.2 r.2 hjr x) hfix
  · by_cases hjr : j.1 = r.1
    · have hir' : i.1 ≠ r.1 := hir
      have hfix : D.phi i.1 r.1 x = x := by
        calc
          D.phi i.1 r.1 x = D.phi j.1 r.1 x := hijval
          _ = D.phi r.1 r.1 x := by rw [hjr]
          _ = x := by rw [D.diag]
      exact (D.offdiag_fixedPointFree i.2 r.2 hir' x) hfix
    · have hcycle := D.no4
        (i := D.base) (j := i.1) (k := r.1) (l := j.1)
        i.2.symm hir hjr.symm j.2 r.2.symm hij x
      have hneq : D.phi r.1 j.1 (D.phi i.1 r.1 x) ≠ x := by
        simpa [D.normalized i.1, D.phi_toBase j.1] using hcycle
      have heq : D.phi r.1 j.1 (D.phi i.1 r.1 x) = x := by
        rw [hijval, D.rev j.1 r.1]
        simp
      exact hneq heq

/-- An injective-coordinate formulation of a Latin cube. -/
structure IsInjectiveLatinCube {A B C D : Type*} (T : A → B → C → D) : Prop where
  first : ∀ b c, Function.Injective (fun a => T a b c)
  second : ∀ a c, Function.Injective (fun b => T a b c)
  third : ∀ a b, Function.Injective (fun c => T a b c)

/-- Short-cycle constraints alone produce an injective Latin cube. -/
theorem shortCycles_give_injectiveLatinCube {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) : IsInjectiveLatinCube (latinEntry D) where
  first := latinEntry_injective_first D
  second := latinEntry_injective_second D
  third := latinEntry_injective_third D

/-- An involutive permutation equals its inverse. -/
theorem perm_inv_eq_self_of_involutive {S : Type v} (f : Equiv.Perm S)
    (hf : Function.Involutive f) : f⁻¹ = f := by
  ext x
  apply f.injective
  simp [hf x]

/-- In the all-involution case the Latin cube is symmetric in its first two coordinates. -/
theorem latinEntry_symm_of_involutive {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S)
    (hinv : ∀ i j, Function.Involutive (D.phi i j))
    (i r : NonBase D) (x : S) :
    latinEntry D i r x = latinEntry D r i x := by
  rw [latinEntry, latinEntry, D.rev i.1 r.1,
    perm_inv_eq_self_of_involutive (D.phi i.1 r.1) (hinv i.1 r.1)]

/-- Diagonal fibres of the Latin cube are the identity. -/
theorem latinEntry_diag {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) (i : NonBase D) (x : S) :
    latinEntry D i i x = x := by
  rw [latinEntry, D.diag]
  rfl

/-- Off-diagonal fibres are fixed-point-free, independently of the involution assumption. -/
theorem latinEntry_offdiag_ne {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i r : NonBase D} (hir : i ≠ r) (x : S) :
    latinEntry D i r x ≠ x := by
  apply D.offdiag_fixedPointFree i.2 r.2
  · exact fun h => hir (Subtype.ext h)

end Moore57
