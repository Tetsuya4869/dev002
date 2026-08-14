import Moore57.LatinCube

namespace Moore57

universe u v

structure RawShortCycleSystem (I : Type u) (S : Type v) where
  phi : I → I → Equiv.Perm S
  diag : ∀ i, phi i i = 1
  rev : ∀ i j, phi j i = (phi i j)⁻¹
  no3 : ∀ {i j k}, i ≠ j → j ≠ k → k ≠ i → ∀ x,
    phi k i (phi j k (phi i j x)) ≠ x
  no4 : ∀ {i j k l},
    i ≠ j → j ≠ k → k ≠ l → l ≠ i → i ≠ k → j ≠ l → ∀ x,
    phi l i (phi k l (phi j k (phi i j x))) ≠ x

def RawShortCycleSystem.gauge
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i : I) :
    Equiv.Perm S := D.phi b i

def RawShortCycleSystem.gaugePhi
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S) (b i j : I) :
    Equiv.Perm S :=
  ((D.gauge b i).trans (D.phi i j)).trans (D.gauge b j).symm

@[simp] theorem RawShortCycleSystem.gaugePhi_apply
    {I : Type u} {S : Type v} (D : RawShortCycleSystem I S)
    (b i j : I) (x : S) :
    D.gaugePhi b i j x = (D.gauge b j).symm (D.phi i j (D.gauge b i x)) := by
  rfl

end Moore57
