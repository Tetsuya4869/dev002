import Moore57.CommonGroupCase

/-!
# Fixed points of the right-translation involution

For a nonidentity group element `h`, simultaneous right multiplication fixes exactly
the root and the branch vertices of the rooted matching model. Hence, when there are
57 branches, the constructed involution has exactly 58 fixed vertices.
-/

namespace Moore57

universe u v

/-- A nonidentity right translation fixes no leaf. -/
theorem rightTranslate_leaf_ne
    {B : Type u} {G : Type v} [Group G] {h : G} (hne : h ≠ 1)
    (i : B) (x : G) :
    rightTranslate h (.leaf i x) ≠ (.leaf i x : Vertex B G) := by
  intro hfix
  have hx : x * h = x := by
    simpa [rightTranslate] using hfix
  apply hne
  have hx' : x * h = x * 1 := by simpa using hx
  exact mul_left_cancel hx'

/--
The fixed-point subtype of a nonidentity simultaneous right translation is equivalent
to `Option B`: `none` represents the root and `some i` the branch vertex `i`.
-/
noncomputable def rightTranslateFixedEquivOption
    {B : Type u} {G : Type v} [Group G] {h : G} (hne : h ≠ 1) :
    {z : Vertex B G // rightTranslate h z = z} ≃ Option B where
  toFun z :=
    match z with
    | ⟨.root, _⟩ => none
    | ⟨.branch i, _⟩ => some i
    | ⟨.leaf i x, hfix⟩ => False.elim (rightTranslate_leaf_ne hne i x hfix)
  invFun o :=
    match o with
    | none => ⟨.root, rfl⟩
    | some i => ⟨.branch i, rfl⟩
  left_inv := by
    rintro ⟨z, hfix⟩
    cases z with
    | root => rfl
    | branch i => rfl
    | leaf i x => exact False.elim (rightTranslate_leaf_ne hne i x hfix)
  right_inv := by
    intro o
    cases o <;> rfl

/-- A nonidentity right translation has one more fixed point than there are branches. -/
theorem natCard_fixedPoints_rightTranslate
    {B : Type u} {G : Type v} [Group G] [Finite B] [Finite G]
    {h : G} (hne : h ≠ 1) :
    Nat.card {z : Vertex B G // rightTranslate h z = z} = Nat.card B + 1 := by
  rw [Nat.card_congr (rightTranslateFixedEquivOption hne)]
  simp

/-- In the degree-57 rooted model, the constructed right translation fixes exactly 58 vertices. -/
theorem natCard_fixedPoints_rightTranslate_eq_58
    {B : Type u} {G : Type v} [Group G] [Finite B] [Finite G]
    {h : G} (hne : h ≠ 1) (hB : Nat.card B = 57) :
    Nat.card {z : Vertex B G // rightTranslate h z = z} = 58 := by
  rw [natCard_fixedPoints_rightTranslate hne, hB]

/--
From a group of cardinality 56 and 57 branches, one obtains an involutive relation
automorphism whose underlying map has exactly 58 fixed vertices.
-/
theorem groupMatching_has_involution_with_58_fixedPoints
    {B : Type u} {G : Type v} [Group G] [Finite B] [Finite G] [Nonempty B]
    (D : MatchingData B G) (hB : Nat.card B = 57) (hG : Nat.card G = 56) :
    ∃ a : InvolutiveRelAut (Adj D),
      Nat.card {z : Vertex B G // a.toFun z = z} = 58 := by
  obtain ⟨h, hne, h2⟩ := exists_involution_element_of_card_eq_56 (G := G) hG
  let a : InvolutiveRelAut (Adj D) := {
    toFun := rightTranslate h
    map_rel_iff := adj_rightTranslate_iff D h
    involutive := rightTranslate_involutive h2
    nontrivial := rightTranslate_nontrivial hne
  }
  refine ⟨a, ?_⟩
  change Nat.card {z : Vertex B G // rightTranslate h z = z} = 58
  exact natCard_fixedPoints_rightTranslate_eq_58 hne hB

/--
An abstract fixed-point theorem saying that every involutive relation automorphism has
56 fixed vertices contradicts the order-56 group-matching construction on 57 branches.
This is the formal trust boundary for importing the Higman--Makhnev--Paduchikh theorem.
-/
theorem no_groupMatching_of_fixedPointCount_56
    {B : Type u} {G : Type v} [Group G] [Finite B] [Finite G] [Nonempty B]
    (D : MatchingData B G) (hB : Nat.card B = 57) (hG : Nat.card G = 56)
    (hFixed56 : ∀ a : InvolutiveRelAut (Adj D),
      Nat.card {z : Vertex B G // a.toFun z = z} = 56) : False := by
  obtain ⟨a, h58⟩ := groupMatching_has_involution_with_58_fixedPoints D hB hG
  have h56 := hFixed56 a
  omega

/--
Combining the common-group numerical bounds with an external 56-fixed-point theorem gives
a contradiction. This packages the full new bridge used by the paper.
-/
theorem no_commonGroupCase_of_fixedPointCount_56
    {B : Type u} {G : Type v} [Group G] [Finite B] [Finite G] [Nonempty B]
    (D : MatchingData B G) (hB : Nat.card B = 57)
    (hdvd : Nat.card G ∣ 56) (hge : 56 ≤ Nat.card G)
    (hFixed56 : ∀ a : InvolutiveRelAut (Adj D),
      Nat.card {z : Vertex B G // a.toFun z = z} = 56) : False := by
  have hG : Nat.card G = 56 := eq_56_of_dvd_56_of_ge_56 hdvd hge
  exact no_groupMatching_of_fixedPointCount_56 D hB hG hFixed56

end Moore57
