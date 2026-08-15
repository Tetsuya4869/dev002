import Mathlib

/-!
# Group-based matching systems and involutions

This file formalizes the algebraic core of the obstruction used in the accompanying
research note.  Once a semiregular derangement group of order 56 is identified with
its regular action, each inter-branch matching is left multiplication by a group
element.  A right multiplication commutes with every such matching.

The main theorem `groupMatching_has_involution_of_card_eq_56` says that a finite group
of cardinality 56 forces a nontrivial involutive automorphism of the resulting
three-level matching relation.
-/

namespace Moore57

universe u v

/-- Vertices in the rooted three-level model: the root, a branch vertex, or a leaf. -/
inductive Vertex (B : Type u) (G : Type v) where
  | root : Vertex B G
  | branch : B → Vertex B G
  | leaf : B → G → Vertex B G

/--
Coefficients for the group-based inter-branch matchings.

In regular coordinates, the matching from branch `i` to branch `j` is left
multiplication by `coeff i j`.  The reverse coefficient condition is the usual
orientation compatibility.
-/
structure MatchingData (B : Type u) (G : Type v) [Group G] where
  coeff : B → B → G
  coeff_rev : ∀ i j, coeff j i = (coeff i j)⁻¹

/--
The adjacency relation of the rooted matching model.

For leaves `x` in branch `i` and `y` in branch `j`, the equation
`y * x⁻¹ = coeff i j` is exactly `y = coeff i j * x`.
-/
def Adj {B : Type u} {G : Type v} [Group G] (D : MatchingData B G) :
    Vertex B G → Vertex B G → Prop
  | .root, .branch _ => True
  | .branch _, .root => True
  | .branch i, .leaf j _ => i = j
  | .leaf j _, .branch i => i = j
  | .leaf i x, .leaf j y => i ≠ j ∧ y * x⁻¹ = D.coeff i j
  | _, _ => False

/-- The matching relation is symmetric when reverse coefficients are inverses. -/
theorem adj_symm {B : Type u} {G : Type v} [Group G]
    (D : MatchingData B G) {v w : Vertex B G} : Adj D v w → Adj D w v := by
  intro h
  cases v <;> cases w <;> simp [Adj] at h ⊢
  case branch.leaf => exact h
  case leaf.branch => exact h
  case leaf.leaf i x j y =>
    rcases h with ⟨hij, hxy⟩
    refine ⟨Ne.symm hij, ?_⟩
    rw [D.coeff_rev i j]
    have hinv := congrArg (fun z : G => z⁻¹) hxy
    simpa using hinv

/-- The matching relation has no loops. -/
theorem adj_irrefl {B : Type u} {G : Type v} [Group G]
    (D : MatchingData B G) (v : Vertex B G) : ¬ Adj D v v := by
  cases v <;> simp [Adj]

/-- Simultaneous right multiplication on every leaf; the root and branch vertices are fixed. -/
def rightTranslate {B : Type u} {G : Type v} [Group G] (h : G) :
    Vertex B G → Vertex B G
  | .root => .root
  | .branch i => .branch i
  | .leaf i x => .leaf i (x * h)

/-- The quotient `y*x⁻¹` is invariant under simultaneous right translation. -/
@[simp] theorem quotient_rightTranslate {G : Type v} [Group G] (x y h : G) :
    (y * h) * (x * h)⁻¹ = y * x⁻¹ := by
  group

/-- Simultaneous right translation preserves all edges, in both directions. -/
theorem adj_rightTranslate_iff {B : Type u} {G : Type v} [Group G]
    (D : MatchingData B G) (h : G) (v w : Vertex B G) :
    Adj D (rightTranslate h v) (rightTranslate h w) ↔ Adj D v w := by
  cases v <;> cases w <;> simp [Adj, rightTranslate]

/-- A relation automorphism which is nontrivial and squares to the identity. -/
structure InvolutiveRelAut {V : Type*} (R : V → V → Prop) where
  toFun : V → V
  map_rel_iff : ∀ v w, R (toFun v) (toFun w) ↔ R v w
  involutive : Function.Involutive toFun
  nontrivial : ∃ v, toFun v ≠ v

/-- Right translation by an element whose square is one is an involution on vertices. -/
theorem rightTranslate_involutive {B : Type u} {G : Type v} [Group G]
    {h : G} (h2 : h * h = 1) : Function.Involutive (rightTranslate (B := B) h) := by
  intro v
  cases v <;> simp [rightTranslate, mul_assoc, h2]

/-- A nonidentity right multiplier acts nontrivially on the leaf set. -/
theorem rightTranslate_nontrivial {B : Type u} {G : Type v} [Group G]
    [Nonempty B] {h : G} (hne : h ≠ 1) :
    ∃ v : Vertex B G, rightTranslate h v ≠ v := by
  let i : B := Classical.choice (inferInstance : Nonempty B)
  refine ⟨.leaf i 1, ?_⟩
  simpa [rightTranslate] using hne

/--
Cauchy's theorem specialized to order 56: every finite group of cardinality 56
contains a nonidentity element of square one.
-/
theorem exists_involution_element_of_card_eq_56 {G : Type v} [Group G] [Finite G]
    (hcard : Nat.card G = 56) : ∃ h : G, h ≠ 1 ∧ h * h = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : 2 ∣ Nat.card G := by
    rw [hcard]
    norm_num
  obtain ⟨h, hord⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hdiv
  refine ⟨h, ?_, ?_⟩
  · intro h1
    subst h
    have hbad : (1 : Nat) = 2 := by simpa using hord
    omega
  · have hp := pow_orderOf_eq_one h
    rw [hord] at hp
    simpa [pow_two] using hp

/--
The formal core obstruction: every group-based matching model over a group of
cardinality 56 has a nontrivial involutive relation automorphism.
-/
theorem groupMatching_has_involution_of_card_eq_56
    {B : Type u} {G : Type v} [Group G] [Finite G] [Nonempty B]
    (D : MatchingData B G) (hcard : Nat.card G = 56) :
    Nonempty (InvolutiveRelAut (Adj D)) := by
  obtain ⟨h, hne, h2⟩ := exists_involution_element_of_card_eq_56 (G := G) hcard
  refine ⟨{
    toFun := rightTranslate h
    map_rel_iff := adj_rightTranslate_iff D h
    involutive := rightTranslate_involutive h2
    nontrivial := rightTranslate_nontrivial hne
  }⟩

/--
A convenient contradiction wrapper: a no-involution hypothesis is incompatible with
a group-based matching model of cardinality 56.
-/
theorem no_groupMatching_of_no_involution
    {B : Type u} {G : Type v} [Group G] [Finite G] [Nonempty B]
    (D : MatchingData B G) (hcard : Nat.card G = 56)
    (hNoInv : ¬ Nonempty (InvolutiveRelAut (Adj D))) : False := by
  exact hNoInv (groupMatching_has_involution_of_card_eq_56 D hcard)

/--
The elementary cardinality step used after Smith--Montemanni's semiregularity and
distinctness bounds: a divisor of 56 which is at least 56 is exactly 56.
-/
theorem eq_56_of_dvd_56_of_ge_56 {n : Nat} (hdvd : n ∣ 56) (hge : 56 ≤ n) :
    n = 56 := by
  have hle : n ≤ 56 := Nat.le_of_dvd (by norm_num) hdvd
  exact Nat.le_antisymm hle hge

end Moore57
