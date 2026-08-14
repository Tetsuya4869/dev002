import Moore57.GraphToRaw

/-!
# Degree 57 supplies the 56-symbol fibre coordinates

For a fixed root, every branch vertex is adjacent to the root.  Hence its full
neighbourhood splits as the root plus the non-root leaf fibre.  In a 57-regular
finite Moore relation this proves that every leaf fibre has cardinality 56 and
therefore admits canonical noncomputable coordinates by `Fin 56`.
-/

namespace Moore57

universe u

/-- The neighbourhood type of a vertex. -/
abbrev MooreRelation.Neighbor {V : Type u} (M : MooreRelation V) (v : V) :=
  {w : V // M.adj v w}

/-- A branch neighbourhood is the root plus its leaf fibre. -/
noncomputable def MooreRelation.neighborEquivOptionLeaf
    {V : Type u} (M : MooreRelation V) {r : V} (i : M.Branch r) :
    M.Neighbor i.1 ≃ Option (M.Leaf r i) where
  toFun n := if h : n.1 = r then none else some ⟨n.1, n.2, h⟩
  invFun o := match o with
    | none => ⟨r, M.symm i.2⟩
    | some x => ⟨x.1, x.2.1⟩
  left_inv := by
    intro n
    by_cases h : n.1 = r
    · apply Subtype.ext
      simpa [h]
    · apply Subtype.ext
      simp [h]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some x => simp [x.2.2]

/-- Cardinality form of the neighbourhood split. -/
theorem MooreRelation.card_neighbor_eq_card_leaf_add_one
    {V : Type u} [Finite V] (M : MooreRelation V) {r : V} (i : M.Branch r) :
    Nat.card (M.Neighbor i.1) = Nat.card (M.Leaf r i) + 1 := by
  rw [Nat.card_congr (M.neighborEquivOptionLeaf i)]
  exact Finite.card_option

/-- Degree 57 forces every rooted leaf fibre to have 56 elements. -/
theorem MooreRelation.card_leaf_eq_56_of_degree57
    {V : Type u} [Finite V] (M : MooreRelation V) {r : V}
    (hdeg : ∀ v : V, Nat.card (M.Neighbor v) = 57)
    (i : M.Branch r) : Nat.card (M.Leaf r i) = 56 := by
  have hsplit := M.card_neighbor_eq_card_leaf_add_one i
  rw [hdeg i.1] at hsplit
  omega

/-- Degree 57 also says that the root has exactly 57 branches. -/
theorem MooreRelation.card_branch_eq_57_of_degree57
    {V : Type u} [Finite V] (M : MooreRelation V) {r : V}
    (hdeg : ∀ v : V, Nat.card (M.Neighbor v) = 57) :
    Nat.card (M.Branch r) = 57 := by
  exact hdeg r

/-- Construct common `Fin 56` coordinates on every leaf fibre from regular degree 57. -/
noncomputable def MooreRelation.rootedCoordinatesFin56
    {V : Type u} [Finite V] (M : MooreRelation V) (r : V)
    (hdeg : ∀ v : V, Nat.card (M.Neighbor v) = 57) :
    RootedCoordinates M r (Fin 56) where
  coord i := (Finite.equivFinOfCardEq (M.card_leaf_eq_56_of_degree57 hdeg i)).symm

/-- Removing a chosen base branch leaves 56 non-base branches. -/
noncomputable def MooreRelation.branchEquivOptionNonBase
    {V : Type u} (M : MooreRelation V) {r : V} (b : M.Branch r) :
    M.Branch r ≃ Option {i : M.Branch r // i ≠ b} where
  toFun i := if h : i = b then none else some ⟨i, h⟩
  invFun o := match o with
    | none => b
    | some i => i.1
  left_inv := by
    intro i
    by_cases h : i = b <;> simp [h]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some i => simp [i.2]

/-- In degree 57, the normalized system has exactly 56 non-base branch indices. -/
theorem MooreRelation.card_nonBase_eq_56_of_degree57
    {V : Type u} [Finite V] (M : MooreRelation V) {r : V}
    (hdeg : ∀ v : V, Nat.card (M.Neighbor v) = 57)
    (b : M.Branch r) :
    Nat.card {i : M.Branch r // i ≠ b} = 56 := by
  have hbranch := M.card_branch_eq_57_of_degree57 hdeg (r := r)
  have hsplit : Nat.card (M.Branch r) = Nat.card {i : M.Branch r // i ≠ b} + 1 := by
    rw [Nat.card_congr (M.branchEquivOptionNonBase b)]
    exact Finite.card_option
  rw [hbranch] at hsplit
  omega

/--
The full graph-level pipeline: a finite 57-regular Moore relation, a root, and a
chosen root-neighbour produce the normalized short-cycle system on 56 symbols.
-/
noncomputable def MooreRelation.toDegree57ShortCycleSystem
    {V : Type u} [Finite V] (M : MooreRelation V) (r : V)
    (hdeg : ∀ v : V, Nat.card (M.Neighbor v) = 57)
    (b : M.Branch r) :
    ShortCycleSystem (M.Branch r) (Fin 56) :=
  (M.rootedCoordinatesFin56 r hdeg).toShortCycleSystem b

end Moore57
