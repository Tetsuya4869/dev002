import Moore57.RestrictedSystem

/-!
# Dual matchings in a full restricted certificate

When the selected branch type `T` and symbol type `S` have the same finite
cardinality, star injectivity upgrades to a bijection: for each fixed branch `a` and
symbol `x`, the map `b ↦ p a b x` is a permutation from branches to symbols.
Consequently every ordered pair of distinct symbols `(x,y)` determines a unique
partner branch for every branch. Symmetry of `p` makes this partner map a
fixed-point-free involution. Thus the matching structure is genuinely dual: branch
edges select perfect matchings of symbols and symbol edges select perfect matchings of
branches.
-/

namespace Moore57

universe u v

/-- Equal finite cardinalities turn every star map into a bijection. -/
theorem RestrictedAllInvolutionSystem.star_bijective_of_card_eq
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    (a : T) (x : S) :
    Function.Bijective (fun b => R.p a b x) := by
  have hinj := R.star_injective a x
  let e : T ≃ S := Fintype.equivOfCardEq hcard
  exact ⟨hinj, hinj.surjective_of_finite e⟩

/-- The star bijection as an actual equivalence. -/
noncomputable def RestrictedAllInvolutionSystem.starEquiv
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    (a : T) (x : S) : T ≃ S :=
  Equiv.ofBijective (fun b => R.p a b x) (R.star_bijective_of_card_eq hcard a x)

/-- For fixed symbols `x,y`, the unique branch partner of `a` whose matching sends `x` to `y`. -/
noncomputable def RestrictedAllInvolutionSystem.dualPartner
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    (x y : S) (a : T) : T :=
  (R.starEquiv hcard a x).symm y

@[simp] theorem RestrictedAllInvolutionSystem.p_dualPartner
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    (x y : S) (a : T) :
    R.p a (R.dualPartner hcard x y a) x = y := by
  exact (R.starEquiv hcard a x).apply_symm_apply y

/-- Distinct symbols give a partner branch distinct from the starting branch. -/
theorem RestrictedAllInvolutionSystem.dualPartner_ne
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    {x y : S} (hxy : x ≠ y) (a : T) :
    R.dualPartner hcard x y a ≠ a := by
  intro h
  have hp := R.p_dualPartner hcard x y a
  rw [h, R.diag a] at hp
  have hxy' : x = y := by simpa using hp
  exact hxy hxy'

/-- The dual partner operation is involutive on branches. -/
theorem RestrictedAllInvolutionSystem.dualPartner_involutive
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    (x y : S) : Function.Involutive (R.dualPartner hcard x y) := by
  intro a
  let b := R.dualPartner hcard x y a
  have hab : R.p a b x = y := by
    exact R.p_dualPartner hcard x y a
  have hba : R.p b a x = y := by
    rw [R.symmetric b a]
    exact hab
  apply (R.starEquiv hcard b x).injective
  change R.p b (R.dualPartner hcard x y b) x = R.p b a x
  rw [R.p_dualPartner hcard x y b, hba]

/-- Every distinct symbol pair induces a fixed-point-free involution of the branch set. -/
noncomputable def RestrictedAllInvolutionSystem.dualMatching
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    {x y : S} (_hxy : x ≠ y) : Equiv.Perm T where
  toFun := R.dualPartner hcard x y
  invFun := R.dualPartner hcard x y
  left_inv := R.dualPartner_involutive hcard x y
  right_inv := R.dualPartner_involutive hcard x y

/-- The dual matching has no fixed points when the two symbols are distinct. -/
theorem RestrictedAllInvolutionSystem.dualMatching_fixedPointFree
    {T : Type u} {S : Type v} (R : RestrictedAllInvolutionSystem T S)
    [Fintype T] [Fintype S] (hcard : Fintype.card T = Fintype.card S)
    {x y : S} (hxy : x ≠ y) (a : T) :
    R.dualMatching hcard hxy a ≠ a := by
  exact R.dualPartner_ne hcard hxy a

end Moore57
