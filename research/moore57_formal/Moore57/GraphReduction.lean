import Moore57.GaugeNormalization

/-!
# From Moore local graph axioms to branch matchings

This module moves the formal trust boundary back to the graph itself.  The relation
axioms are the local strongly-regular conditions relevant to a diameter-two Moore
graph: no triangles, and a unique common neighbour for every distinct nonadjacent
pair.  After fixing a root, its neighbours are branches and the non-root neighbours
of each branch are its leaf fibre.

A `RootedCoordinates` value supplies only a common label type for these fibres.  The
cross-branch perfect matchings are then *derived* from the graph axioms rather than
assumed as permutations.
-/

namespace Moore57

universe u v

/-- The graph-theoretic Moore conditions used by the rooted permutation reduction. -/
structure MooreRelation (V : Type u) where
  adj : V → V → Prop
  symm : ∀ {x y}, adj x y → adj y x
  irrefl : ∀ x, ¬ adj x x
  noTriangle : ∀ {x y z}, adj x y → adj y z → adj z x → False
  uniqueCommon : ∀ {x y}, x ≠ y → ¬ adj x y →
    ∃! z, adj x z ∧ adj y z

/-- Neighbours of a fixed root, used as the branch index type. -/
abbrev MooreRelation.Branch {V : Type u} (M : MooreRelation V) (r : V) :=
  {v : V // M.adj r v}

/-- Non-root neighbours of a branch vertex. -/
abbrev MooreRelation.Leaf {V : Type u} (M : MooreRelation V) (r : V)
    (i : M.Branch r) :=
  {v : V // M.adj i.1 v ∧ v ≠ r}

/-- A common label set for all leaf fibres.  No matching permutations are assumed. -/
structure RootedCoordinates {V : Type u} (M : MooreRelation V) (r : V) (S : Type v) where
  coord : ∀ i : M.Branch r, S ≃ M.Leaf r i

/-- Distinct branches cannot be adjacent, otherwise they form a triangle with the root. -/
theorem MooreRelation.branch_not_adj
    {V : Type u} (M : MooreRelation V) {r : V}
    {i j : M.Branch r} (hij : i ≠ j) : ¬ M.adj i.1 j.1 := by
  intro h
  exact M.noTriangle i.2 h (M.symm j.2)

/-- A leaf is not adjacent to the root, otherwise root--branch--leaf is a triangle. -/
theorem MooreRelation.leaf_not_adj_root
    {V : Type u} (M : MooreRelation V) {r : V}
    (i : M.Branch r) (x : M.Leaf r i) : ¬ M.adj x.1 r := by
  intro h
  exact M.noTriangle i.2 x.2.1 h

/-- A leaf in branch `i` cannot itself be the distinct branch vertex `j`. -/
theorem MooreRelation.leaf_ne_branch
    {V : Type u} (M : MooreRelation V) {r : V}
    {i j : M.Branch r} (hij : i ≠ j) (x : M.Leaf r i) : x.1 ≠ j.1 := by
  intro hx
  apply M.branch_not_adj hij
  simpa [hx] using x.2.1

/-- A leaf in branch `i` is not adjacent to a distinct branch vertex `j`. -/
theorem MooreRelation.leaf_not_adj_other_branch
    {V : Type u} (M : MooreRelation V) {r : V}
    {i j : M.Branch r} (hij : i ≠ j) (x : M.Leaf r i) : ¬ M.adj x.1 j.1 := by
  intro hxj
  have hbranches : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  have hnadj := M.branch_not_adj hij
  obtain ⟨c, hc, huniq⟩ := M.uniqueCommon hbranches hnadj
  have hr : M.adj i.1 r ∧ M.adj j.1 r := ⟨M.symm i.2, M.symm j.2⟩
  have hx : M.adj i.1 x.1 ∧ M.adj j.1 x.1 := ⟨x.2.1, M.symm hxj⟩
  have hxc : x.1 = c := huniq x.1 hx
  have hrc : r = c := huniq r hr
  exact x.2.2 (hxc.trans hrc.symm)

/-- Distinct branches have disjoint leaf fibres. -/
theorem MooreRelation.leaf_vertices_ne
    {V : Type u} (M : MooreRelation V) {r : V}
    {i j : M.Branch r} (hij : i ≠ j)
    (x : M.Leaf r i) (y : M.Leaf r j) : x.1 ≠ y.1 := by
  intro hxy
  have hbranches : i.1 ≠ j.1 := by
    intro h
    exact hij (Subtype.ext h)
  have hnadj := M.branch_not_adj hij
  obtain ⟨c, hc, huniq⟩ := M.uniqueCommon hbranches hnadj
  have hr : M.adj i.1 r ∧ M.adj j.1 r := ⟨M.symm i.2, M.symm j.2⟩
  have hx : M.adj i.1 x.1 ∧ M.adj j.1 x.1 := by
    refine ⟨x.2.1, ?_⟩
    rw [hxy]
    exact y.2.1
  have hxc : x.1 = c := huniq x.1 hx
  have hrc : r = c := huniq r hr
  exact x.2.2 (hxc.trans hrc.symm)

/-- The unique common neighbour used to move a leaf from branch `i` to branch `j`. -/
noncomputable def RootedCoordinates.crossVertex
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) : V :=
  Classical.choose (M.uniqueCommon
    (M.leaf_ne_branch hij (C.coord i x))
    (M.leaf_not_adj_other_branch hij (C.coord i x)))

/-- The cross vertex is adjacent to the starting leaf. -/
theorem RootedCoordinates.adj_leaf_crossVertex
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) :
    M.adj (C.coord i x).1 (C.crossVertex hij x) := by
  exact (Classical.choose_spec (M.uniqueCommon
    (M.leaf_ne_branch hij (C.coord i x))
    (M.leaf_not_adj_other_branch hij (C.coord i x)))).1.1

/-- The cross vertex is adjacent to the target branch. -/
theorem RootedCoordinates.adj_branch_crossVertex
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) :
    M.adj j.1 (C.crossVertex hij x) := by
  exact (Classical.choose_spec (M.uniqueCommon
    (M.leaf_ne_branch hij (C.coord i x))
    (M.leaf_not_adj_other_branch hij (C.coord i x)))).1.2

/-- The cross vertex is not the root, so it lies in the target leaf fibre. -/
theorem RootedCoordinates.crossVertex_ne_root
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) :
    C.crossVertex hij x ≠ r := by
  intro h
  have hxroot : M.adj (C.coord i x).1 r := by
    simpa [h] using C.adj_leaf_crossVertex hij x
  exact M.leaf_not_adj_root i (C.coord i x) hxroot

/-- The graph-derived cross neighbour as an element of the target leaf fibre. -/
noncomputable def RootedCoordinates.crossLeaf
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) :
    M.Leaf r j :=
  ⟨C.crossVertex hij x, C.adj_branch_crossVertex hij x, C.crossVertex_ne_root hij x⟩

/-- The graph-derived cross neighbour in common `S` coordinates. -/
noncomputable def RootedCoordinates.crossLabel
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) : S :=
  (C.coord j).symm (C.crossLeaf hij x)

/-- Crossing from `i` to `j` and back returns the original label. -/
theorem RootedCoordinates.crossLabel_rev
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) :
    C.crossLabel (Ne.symm hij) (C.crossLabel hij x) = x := by
  apply (C.coord i).injective
  simp only [RootedCoordinates.crossLabel, Equiv.apply_symm_apply]
  apply Subtype.ext
  let y : M.Leaf r j := C.crossLeaf hij x
  have hycoord : C.coord j ((C.coord j).symm y) = y := (C.coord j).apply_symm_apply y
  have hyx : M.adj y.1 (C.coord i x).1 := by
    exact M.symm (C.adj_leaf_crossVertex hij x)
  have hix : M.adj i.1 (C.coord i x).1 := (C.coord i x).2.1
  have hpair_ne : y.1 ≠ i.1 := by
    rw [← hycoord]
    exact M.leaf_ne_branch (Ne.symm hij) (C.coord j ((C.coord j).symm y))
  have hpair_nadj : ¬ M.adj y.1 i.1 := by
    rw [← hycoord]
    exact M.leaf_not_adj_other_branch (Ne.symm hij) (C.coord j ((C.coord j).symm y))
  obtain ⟨c, hc, huniq⟩ := M.uniqueCommon hpair_ne hpair_nadj
  have hxcommon : M.adj y.1 (C.coord i x).1 ∧ M.adj i.1 (C.coord i x).1 := ⟨hyx, hix⟩
  have hchosen : C.crossVertex (Ne.symm hij) (C.crossLabel hij x) = c := by
    apply huniq
    constructor
    · rw [← hycoord]
      exact C.adj_leaf_crossVertex (Ne.symm hij) (C.crossLabel hij x)
    · exact C.adj_branch_crossVertex (Ne.symm hij) (C.crossLabel hij x)
  have hx : (C.coord i x).1 = c := huniq (C.coord i x).1 hxcommon
  change C.crossVertex (Ne.symm hij) (C.crossLabel hij x) = (C.coord i x).1
  exact hchosen.trans hx.symm

/-- The graph-derived matching between two distinct branches is a permutation. -/
noncomputable def RootedCoordinates.crossEquiv
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) :
    Equiv.Perm S where
  toFun := C.crossLabel hij
  invFun := C.crossLabel (Ne.symm hij)
  left_inv := C.crossLabel_rev hij
  right_inv := C.crossLabel_rev (Ne.symm hij)

/-- Reversing a graph-derived matching gives its inverse permutation. -/
theorem RootedCoordinates.crossEquiv_rev
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) :
    C.crossEquiv (Ne.symm hij) = (C.crossEquiv hij)⁻¹ := by
  ext x
  rfl

end Moore57
