import Moore57.GraphReduction

/-!
# The graph-derived raw permutation system

This module turns the cross-branch equivalences constructed in `GraphReduction` into
an unnormalized permutation system.  Its short-cycle holonomy is proved directly from
the Moore relation axioms, rather than assumed.
-/

namespace Moore57

universe u v

/-- Graph-derived matching permutation, with the diagonal defined as the identity. -/
noncomputable def RootedCoordinates.rawPhi
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) (i j : M.Branch r) : Equiv.Perm S := by
  classical
  exact if h : i = j then 1 else C.crossEquiv h

@[simp] theorem RootedCoordinates.rawPhi_diag
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) (i : M.Branch r) : C.rawPhi i i = 1 := by
  classical
  simp [RootedCoordinates.rawPhi]

/-- Reverse orientation is the inverse matching. -/
theorem RootedCoordinates.rawPhi_rev
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) (i j : M.Branch r) :
    C.rawPhi j i = (C.rawPhi i j)⁻¹ := by
  classical
  by_cases h : i = j
  · subst j
    simp
  · rw [RootedCoordinates.rawPhi, dif_neg h,
      RootedCoordinates.rawPhi, dif_neg (Ne.symm h), C.crossEquiv_rev h]

/-- In off-diagonal fibres the raw permutation is exactly the graph-derived cross matching. -/
theorem RootedCoordinates.rawPhi_eq_crossEquiv
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) :
    C.rawPhi i j = C.crossEquiv hij := by
  classical
  simp [RootedCoordinates.rawPhi, hij]

/-- Applying a graph-derived raw matching really gives an edge between the two leaves. -/
theorem RootedCoordinates.rawPhi_edge
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) {i j : M.Branch r} (hij : i ≠ j) (x : S) :
    M.adj (C.coord i x).1 (C.coord j (C.rawPhi i j x)).1 := by
  rw [C.rawPhi_eq_crossEquiv hij]
  change M.adj (C.coord i x).1 (C.coord j (C.crossLabel hij x)).1
  simp only [RootedCoordinates.crossLabel, Equiv.apply_symm_apply]
  exact C.adj_leaf_crossVertex hij x

/-- A three-step return would be a triangle, hence is impossible. -/
theorem RootedCoordinates.rawPhi_no3
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S)
    {i j k : M.Branch r} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) (x : S) :
    C.rawPhi k i (C.rawPhi j k (C.rawPhi i j x)) ≠ x := by
  intro hreturn
  let y : S := C.rawPhi i j x
  let z : S := C.rawPhi j k y
  have e1 : M.adj (C.coord i x).1 (C.coord j y).1 := by
    exact C.rawPhi_edge hij x
  have e2 : M.adj (C.coord j y).1 (C.coord k z).1 := by
    exact C.rawPhi_edge hjk y
  have e3 : M.adj (C.coord k z).1 (C.coord i x).1 := by
    have e := C.rawPhi_edge hki z
    simpa [y, z, hreturn] using e
  exact M.noTriangle e1 e2 e3

/-- A four-step return would give two common neighbours to an opposite pair. -/
theorem RootedCoordinates.rawPhi_no4
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S)
    {i j k l : M.Branch r}
    (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l) (hli : l ≠ i)
    (hik : i ≠ k) (hjl : j ≠ l) (x : S) :
    C.rawPhi l i
      (C.rawPhi k l (C.rawPhi j k (C.rawPhi i j x))) ≠ x := by
  intro hreturn
  let y : S := C.rawPhi i j x
  let z : S := C.rawPhi j k y
  let w : S := C.rawPhi k l z
  let xv := C.coord i x
  let yv := C.coord j y
  let zv := C.coord k z
  let wv := C.coord l w
  have e1 : M.adj xv.1 yv.1 := by
    exact C.rawPhi_edge hij x
  have e2 : M.adj yv.1 zv.1 := by
    exact C.rawPhi_edge hjk y
  have e3 : M.adj zv.1 wv.1 := by
    exact C.rawPhi_edge hkl z
  have e4 : M.adj wv.1 xv.1 := by
    have e := C.rawPhi_edge hli w
    simpa [xv, wv, y, z, w, hreturn] using e
  have hxz_ne : xv.1 ≠ zv.1 := by
    exact M.leaf_vertices_ne hik xv zv
  have hxz_nadj : ¬ M.adj xv.1 zv.1 := by
    intro hxz
    exact M.noTriangle e1 e2 (M.symm hxz)
  obtain ⟨c, hc, huniq⟩ := M.uniqueCommon hxz_ne hxz_nadj
  have hy_common : M.adj xv.1 yv.1 ∧ M.adj zv.1 yv.1 :=
    ⟨e1, M.symm e2⟩
  have hw_common : M.adj xv.1 wv.1 ∧ M.adj zv.1 wv.1 :=
    ⟨M.symm e4, e3⟩
  have hyc : yv.1 = c := huniq yv.1 hy_common
  have hwc : wv.1 = c := huniq wv.1 hw_common
  have hyw : yv.1 = wv.1 := hyc.trans hwc.symm
  exact (M.leaf_vertices_ne hjl yv wv) hyw

/-- The Moore graph axioms plus common fibre coordinates produce a raw short-cycle system. -/
noncomputable def RootedCoordinates.toRawShortCycleSystem
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) :
    RawShortCycleSystem (M.Branch r) S where
  phi := C.rawPhi
  diag := C.rawPhi_diag
  rev := C.rawPhi_rev
  no3 := C.rawPhi_no3
  no4 := C.rawPhi_no4

/-- Choosing any branch as base now gives the normalized system used downstream. -/
noncomputable def RootedCoordinates.toShortCycleSystem
    {V : Type u} {M : MooreRelation V} {r : V} {S : Type v}
    (C : RootedCoordinates M r S) (b : M.Branch r) :
    ShortCycleSystem (M.Branch r) S :=
  C.toRawShortCycleSystem.normalize b

end Moore57
