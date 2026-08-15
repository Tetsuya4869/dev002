import Moore57.LatinCube

/-!
# Gauge normalization of branch matching systems

A rooted Moore reduction naturally gives one coordinate system on each branch.
Before choosing a distinguished base branch there is no reason for the base-to-branch
matching permutations to be the identity. This file formalizes the standard gauge
change that makes them identities.

Triangle and quadrilateral holonomy are invariant under this branchwise change of
coordinates. The stronger property that every fibre permutation is an involution is
intentionally *not* asserted to be gauge invariant.
-/

namespace Moore57

universe u v

/-- An unnormalized system of branch matching permutations with girth-five holonomy. -/
structure RawShortCycleSystem (I : Type u) (S : Type v) where
  phi : I → I → Equiv.Perm S
  diag : ∀ i, phi i i = 1
  rev : ∀ i j, phi j i = (phi i j)⁻¹
  no3 : ∀ {i j k}, i ≠ j → j ≠ k → k ≠ i → ∀ x,
    phi k i (phi j k (phi i j x)) ≠ x
  no4 : ∀ {i j k l},
    i ≠ j → j ≠ k → k ≠ l → l ≠ i → i ≠ k → j ≠ l → ∀ x,
    phi l i (phi k l (phi j k (phi i j x))) ≠ x

/-- Coordinate change on branch `i`, induced by the matching from base `b` to `i`. -/
def RawShortCycleSystem.gauge
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i : I) :
    Equiv.Perm S := D.phi b i

/-- Gauge-transformed matching: `g_j⁻¹ ∘ phi_ij ∘ g_i`. -/
def RawShortCycleSystem.gaugePhi
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i j : I) :
    Equiv.Perm S :=
  ((D.gauge b i).trans (D.phi i j)).trans (D.gauge b j).symm

@[simp] theorem RawShortCycleSystem.gaugePhi_apply
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S)
    (b i j : I) (x : S) :
    D.gaugePhi b i j x = (D.gauge b j).symm (D.phi i j (D.gauge b i x)) := by
  rfl

/-- Gauge normalization preserves the diagonal identity. -/
theorem RawShortCycleSystem.gaugePhi_diag
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i : I) :
    D.gaugePhi b i i = 1 := by
  ext x
  simp [RawShortCycleSystem.gaugePhi, RawShortCycleSystem.gauge, D.diag]

/-- Gauge normalization preserves reversal of oriented matchings. -/
theorem RawShortCycleSystem.gaugePhi_rev
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i j : I) :
    D.gaugePhi b j i = (D.gaugePhi b i j)⁻¹ := by
  ext x
  change (D.gauge b i).symm (D.phi j i (D.gauge b j x)) =
    (D.gauge b i).symm ((D.phi i j).symm (D.gauge b j x))
  rw [D.rev i j]
  rfl

/-- Every base-to-branch matching becomes the identity. -/
theorem RawShortCycleSystem.gaugePhi_base
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i : I) :
    D.gaugePhi b b i = 1 := by
  ext x
  simp [RawShortCycleSystem.gaugePhi, RawShortCycleSystem.gauge, D.diag]

/-- Triangle holonomy is invariant under branchwise gauge normalization. -/
theorem RawShortCycleSystem.gaugePhi_no3
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b : I)
    {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) (x : S) :
    D.gaugePhi b k i (D.gaugePhi b j k (D.gaugePhi b i j x)) ≠ x := by
  intro h
  have hg := congrArg (D.gauge b i) h
  have hraw := D.no3 hij hjk hki (D.gauge b i x)
  apply hraw
  simpa [RawShortCycleSystem.gaugePhi, RawShortCycleSystem.gauge] using hg

/-- Quadrilateral holonomy is invariant under branchwise gauge normalization. -/
theorem RawShortCycleSystem.gaugePhi_no4
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b : I)
    {i j k l : I}
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) (hli : l ≠ i)
    (hik : i ≠ k) (hjl : j ≠ l) (x : S) :
    D.gaugePhi b l i
      (D.gaugePhi b k l (D.gaugePhi b j k (D.gaugePhi b i j x))) ≠ x := by
  intro h
  have hg := congrArg (D.gauge b i) h
  have hraw := D.no4 hij hjk hkl hli hik hjl (D.gauge b i x)
  apply hraw
  simpa [RawShortCycleSystem.gaugePhi, RawShortCycleSystem.gauge] using hg

/-- Every raw short-cycle system can be normalized at an arbitrary base branch. -/
noncomputable def RawShortCycleSystem.normalize
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b : I) :
    ShortCycleSystem I S where
  base := b
  phi := D.gaugePhi b
  diag := D.gaugePhi_diag b
  rev := D.gaugePhi_rev b
  normalized := D.gaugePhi_base b
  no3 := D.gaugePhi_no3 b
  no4 := D.gaugePhi_no4 b

@[simp] theorem RawShortCycleSystem.normalize_phi
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i j : I) :
    (D.normalize b).phi i j = D.gaugePhi b i j := rfl

end Moore57
