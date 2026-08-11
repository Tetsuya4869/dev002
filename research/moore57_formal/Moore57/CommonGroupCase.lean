import Moore57.GroupMatching

/-!
# The common derangement-group numerical reduction

This module isolates the final numerical bridge used in the paper. Smith--Montemanni's
semiregularity argument gives `Nat.card G ∣ 56`, while their fixed-row distinctness
condition gives `56 ≤ Nat.card G`. These two facts force `Nat.card G = 56`, after which
the kernel-checked involution obstruction from `GroupMatching` applies.
-/

namespace Moore57

universe u v

/--
The two numerical consequences of the common derangement-group case already force a
nontrivial involutive relation automorphism of the regular-coordinate matching model.
-/
theorem commonGroupBounds_force_involution
    {B : Type u} {G : Type v} [Group G] [Finite G] [Nonempty B]
    (D : MatchingData B G)
    (hdvd : Nat.card G ∣ 56) (hge : 56 ≤ Nat.card G) :
    Nonempty (InvolutiveRelAut (Adj D)) := by
  have hcard : Nat.card G = 56 := eq_56_of_dvd_56_of_ge_56 hdvd hge
  exact groupMatching_has_involution_of_card_eq_56 D hcard

/--
A no-involution hypothesis is inconsistent with the two numerical consequences of the
common derangement-group case.
-/
theorem no_commonGroupCase_of_no_involution
    {B : Type u} {G : Type v} [Group G] [Finite G] [Nonempty B]
    (D : MatchingData B G)
    (hdvd : Nat.card G ∣ 56) (hge : 56 ≤ Nat.card G)
    (hNoInv : ¬ Nonempty (InvolutiveRelAut (Adj D))) : False := by
  exact hNoInv (commonGroupBounds_force_involution D hdvd hge)

end Moore57
