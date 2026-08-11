import Moore57.LatinCubeFinite

/-!
# Residual holonomy constraints

The Latin-cube reduction captures exactly the short cycles that pass through the
normalized base branch.  The genuinely difficult residual constraints are the
triangles and 4-cycles lying entirely among the non-base branches.

For fixed distinct branches `i,j` and a symbol `x`, let

`twoStep i j k x = phi k j (phi i k x)`

be the endpoint reached by the two-step route from `i` to `j` through `k`.
The Moore girth-five constraints imply that, as `k` varies, these endpoints
are pairwise distinct and avoid both `x` and the direct endpoint `phi i j x`.
Thus in the order-56 case the 54 intermediate routes, the stationary endpoint,
and the direct endpoint exhaust all 56 symbols.
-/

namespace Moore57

universe u v

/-- Endpoint of the route `i -> k -> j`. -/
def twoStep {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    (i j k : NonBase D) (x : S) : S :=
  D.phi k.1 j.1 (D.phi i.1 k.1 x)

/-- A two-step route through a third branch cannot return to the original symbol. -/
theorem twoStep_ne_self {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j k : NonBase D}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (x : S) :
    twoStep D i j k x ≠ x := by
  have hcycle := D.no4
    (i := i.1) (j := k.1) (k := j.1) (l := D.base)
    (fun h => hik (Subtype.ext h))
    (fun h => hkj (Subtype.ext h))
    j.2 i.2.symm
    (fun h => hij (Subtype.ext h))
    k.2 x
  simpa [twoStep, D.normalized, D.phi_toBase] using hcycle

/-- A two-step route through a third branch cannot equal the direct matching endpoint. -/
theorem twoStep_ne_direct {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j k : NonBase D}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (x : S) :
    twoStep D i j k x ≠ D.phi i.1 j.1 x := by
  intro heq
  have heq' :
      D.phi k.1 j.1 (D.phi i.1 k.1 x) = D.phi i.1 j.1 x := by
    simpa [twoStep] using heq
  have hcycle := D.no3
    (i := i.1) (j := k.1) (k := j.1)
    (fun h => hik (Subtype.ext h))
    (fun h => hkj (Subtype.ext h))
    (fun h => hij (Subtype.ext h.symm)) x
  apply hcycle
  rw [heq', D.rev i.1 j.1]
  simp

/--
Two distinct intermediate branches give distinct two-step endpoints.  A collision
would close the simple 4-cycle `i -> k -> j -> l -> i`.
-/
theorem twoStep_ne_twoStep {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j k l : NonBase D}
    (hij : i ≠ j)
    (hik : i ≠ k) (hkj : k ≠ j)
    (hil : i ≠ l) (hlj : l ≠ j)
    (hkl : k ≠ l) (x : S) :
    twoStep D i j k x ≠ twoStep D i j l x := by
  intro heq
  have heq' :
      D.phi k.1 j.1 (D.phi i.1 k.1 x) =
        D.phi l.1 j.1 (D.phi i.1 l.1 x) := by
    simpa [twoStep] using heq
  have hcycle := D.no4
    (i := i.1) (j := k.1) (k := j.1) (l := l.1)
    (fun h => hik (Subtype.ext h))
    (fun h => hkj (Subtype.ext h))
    (fun h => hlj (Subtype.ext h.symm))
    (fun h => hil (Subtype.ext h.symm))
    (fun h => hij (Subtype.ext h))
    (fun h => hkl (Subtype.ext h)) x
  apply hcycle
  rw [heq', D.rev l.1 j.1, D.rev i.1 l.1]
  simp

/-- Intermediate non-base branches for an ordered pair `(i,j)`. -/
abbrev Intermediate {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    (i j : NonBase D) :=
  {k : NonBase D // k ≠ i ∧ k ≠ j}

/-- The two-step endpoint map is injective in its intermediate branch. -/
theorem twoStep_injective_intermediate {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j : NonBase D} (hij : i ≠ j) (x : S) :
    Function.Injective (fun k : Intermediate D i j => twoStep D i j k.1 x) := by
  intro k l hval
  apply Subtype.ext
  by_contra hkl
  exact twoStep_ne_twoStep D hij
    (Ne.symm k.2.1) k.2.2
    (Ne.symm l.2.1) l.2.2
    hkl x hval

/--
The direct endpoint is different from the original symbol for distinct branches.
This is the triangle-through-the-base constraint already used by the Latin reduction.
-/
theorem direct_ne_self {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j : NonBase D} (hij : i ≠ j) (x : S) :
    D.phi i.1 j.1 x ≠ x := by
  exact D.offdiag_fixedPointFree i.2 j.2 (fun h => hij (Subtype.ext h)) x

/-- Residual triangle holonomy among three non-base branches is fixed-point-free. -/
def triangleHolonomy {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    (i j k : NonBase D) : Equiv.Perm S :=
  D.phi k.1 i.1 * D.phi j.1 k.1 * D.phi i.1 j.1

/-- Residual 4-cycle holonomy among four non-base branches is fixed-point-free. -/
def quadrilateralHolonomy {I : Type u} {S : Type v} (D : ShortCycleSystem I S)
    (i j k l : NonBase D) : Equiv.Perm S :=
  D.phi l.1 i.1 * D.phi k.1 l.1 * D.phi j.1 k.1 * D.phi i.1 j.1

/-- The triangle holonomy has no fixed point on a simple triangle. -/
theorem triangleHolonomy_ne {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j k : NonBase D}
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) (x : S) :
    triangleHolonomy D i j k x ≠ x := by
  simpa [triangleHolonomy, mul_apply] using
    D.no3
      (fun h => hij (Subtype.ext h))
      (fun h => hjk (Subtype.ext h))
      (fun h => hki (Subtype.ext h)) x

/-- The quadrilateral holonomy has no fixed point on a simple 4-cycle. -/
theorem quadrilateralHolonomy_ne {I : Type u} {S : Type v}
    (D : ShortCycleSystem I S) {i j k l : NonBase D}
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) (hli : l ≠ i)
    (hik : i ≠ k) (hjl : j ≠ l) (x : S) :
    quadrilateralHolonomy D i j k l x ≠ x := by
  simpa [quadrilateralHolonomy, mul_apply] using
    D.no4
      (fun h => hij (Subtype.ext h))
      (fun h => hjk (Subtype.ext h))
      (fun h => hkl (Subtype.ext h))
      (fun h => hli (Subtype.ext h))
      (fun h => hik (Subtype.ext h))
      (fun h => hjl (Subtype.ext h)) x

end Moore57
