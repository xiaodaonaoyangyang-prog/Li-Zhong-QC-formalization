import LiZhongQC.Lemmas.SchottkyClosedSurface10

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC

/-- **Square lemma.**  The boundary of a square, read along the two possible routes, gives homotopic
paths. -/
theorem s78dg_square {Z : Type*} [TopologicalSpace Z] (F : C(I × I, Z)) {a b c d : Z}
    (left : Path a b) (top : Path b c) (bottom : Path a d) (right : Path d c)
    (hl : ∀ s, left s = F (s, 0)) (ht : ∀ t, top t = F (1, t))
    (hb : ∀ t, bottom t = F (0, t)) (hr : ∀ s, right s = F (s, 1)) :
    (left.trans top).Homotopic (bottom.trans right) := by
  have ha : a = F (0, 0) := left.source.symm.trans (hl 0)
  have hb' : b = F (1, 0) := left.target.symm.trans (hl 1)
  have hc : c = F (1, 1) := top.target.symm.trans (ht 1)
  have hd : d = F (0, 1) := bottom.target.symm.trans (hb 1)
  subst ha hb' hc hd
  let pl : Path ((0 : I), (0 : I)) ((1 : I), (0 : I)) :=
    { toFun := fun s => (s, 0)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let pt : Path ((1 : I), (0 : I)) ((1 : I), (1 : I)) :=
    { toFun := fun t => (1, t)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let pb : Path ((0 : I), (0 : I)) ((0 : I), (1 : I)) :=
    { toFun := fun t => (0, t)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let pr : Path ((0 : I), (1 : I)) ((1 : I), (1 : I)) :=
    { toFun := fun s => (s, 1)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  haveI : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have h := (SimplyConnectedSpace.paths_homotopic (pl.trans pt) (pb.trans pr)).map F
  have e1 : left = pl.map F.continuous := Path.ext (funext hl)
  have e2 : top = pt.map F.continuous := Path.ext (funext ht)
  have e3 : bottom = pb.map F.continuous := Path.ext (funext hb)
  have e4 : right = pr.map F.continuous := Path.ext (funext hr)
  rw [e1, e2, e3, e4]
  rw [Path.map_trans, Path.map_trans] at h
  exact h


open FundamentalGroup in
/-- Change of base point along `r` sends the loop `c` to the loop `b` when `r · b ≃ c · r`. -/
theorem s78dg_pi1_conj {Z : Type*} [TopologicalSpace Z] {x y : Z} (r : Path x y) (c : Path x x)
    (b : Path y y) (h : (r.trans b).Homotopic (c.trans r)) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath r
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk b) := by
  unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
  rw [CategoryTheory.Iso.conj_apply, CategoryTheory.Iso.inv_comp_eq]
  exact (Quotient.sound h).symm


theorem s78dg_seg_val {Z : Type*} [TopologicalSpace Z] (f : ℝ → Z) (hf : Continuous f) (a c : ℝ)
    (t : I) : ((Path.segment a c).map hf) t = f (a + (t : ℝ) * (c - a)) := by
  show f (AffineMap.lineMap a c (t : ℝ)) = _
  rw [AffineMap.lineMap_apply]
  congr 1
  simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
  ring

theorem s78dg_seg_split {Z : Type*} [TopologicalSpace Z] (f : ℝ → Z) (hf : Continuous f)
    (a m c : ℝ) :
    ((Path.segment a c).map hf).Homotopic
      (((Path.segment a m).map hf).trans ((Path.segment m c).map hf)) := by
  have h := (SimplyConnectedSpace.paths_homotopic (Path.segment a c)
    ((Path.segment a m).trans (Path.segment m c))).map (⟨f, hf⟩ : C(ℝ, Z))
  rw [Path.map_trans] at h
  exact h

/-- One more unit of boundary: if `β` is the boundary loop of length `N` and `ε` the next edge loop, the
boundary loop of length `N+1` is the product. -/
theorem s78dg_loop_step {Z : Type*} [TopologicalSpace Z] (f : ℝ → Z) (hf : Continuous f) {v : Z}
    (hv : ∀ x : ℝ, (∃ n : ℤ, x = n) → f x = v) (N : ℕ) (β ε : Path v v)
    (hβ : ∀ t : I, β t = f (N * (t : ℝ))) (hε : ∀ t : I, ε t = f (N + (t : ℝ))) :
    ∃ β' : Path v v, (∀ t : I, β' t = f (((N + 1 : ℕ) : ℝ) * (t : ℝ))) ∧
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β') =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε) *
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β) := by
  have hx : v = f 0 := (hv 0 ⟨0, by simp⟩).symm
  have hy : v = f (N : ℝ) := (hv N ⟨N, by simp⟩).symm
  have hz : v = f ((N : ℝ) + 1) := (hv (N + 1) ⟨N + 1, by simp⟩).symm
  let S := (Path.segment (0 : ℝ) ((N : ℝ) + 1)).map hf
  let S1 := (Path.segment (0 : ℝ) (N : ℝ)).map hf
  let S2 := (Path.segment (N : ℝ) ((N : ℝ) + 1)).map hf
  have eβ : β = S1.cast hx hy := Path.ext (funext fun t => by
    rw [hβ t]
    exact (congrArg f (by ring)).trans (s78dg_seg_val f hf 0 N t).symm)
  have eε : ε = S2.cast hy hz := Path.ext (funext fun t => by
    rw [hε t]
    exact (congrArg f (by ring)).trans (s78dg_seg_val f hf N (N + 1) t).symm)
  refine ⟨S.cast hx hz, fun t => ?_, ?_⟩
  · exact (s78dg_seg_val f hf 0 (N + 1) t).trans (congrArg f (by push_cast; ring))
  · have hh : (S.cast hx hz).Homotopic (β.trans ε) := by
      have h1 := (s78dg_seg_split f hf 0 N ((N : ℝ) + 1)).pathCast hx hz
      have h2 : β.trans ε = (S1.trans S2).cast hx hz := by
        rw [eβ, eε]
        exact Path.ext rfl
      rw [h2]
      exact h1
    exact Quotient.sound hh

theorem s78dg_exists_edge_loop {Z : Type*} [TopologicalSpace Z] (f : ℝ → Z) (hf : Continuous f) {v : Z}
    (hv : ∀ x : ℝ, (∃ n : ℤ, x = n) → f x = v) (N : ℕ) :
    ∃ ε : Path v v, ∀ t : I, ε t = f ((N : ℝ) + (t : ℝ)) := by
  have hy : v = f (N : ℝ) := (hv N ⟨N, by simp⟩).symm
  have hz : v = f ((N : ℝ) + 1) := (hv (N + 1) ⟨N + 1, by simp⟩).symm
  refine ⟨((Path.segment (N : ℝ) ((N : ℝ) + 1)).map hf).cast hy hz, fun t => ?_⟩
  exact (s78dg_seg_val f hf N (N + 1) t).trans (congrArg f (by ring))


theorem s78dg_cs_edge_gen (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)))
    (hL : ∀ t : I, L t = s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩ := by
  refine he j hj L (fun t => ?_)
  by_cases ht : (t : ℝ) < 1
  · rw [hL t, Int.fract_eq_self.2 ⟨t.2.1, ht⟩]
  · have h1 : (t : ℝ) = 1 := le_antisymm t.2.2 (not_lt.1 ht)
    rw [hL t, h1, Int.fract_one]
    exact congrArg Subtype.val (s78dg_cs_Psi_E_end p hp j one hone).symm

theorem s78dg_cs_E_even (n : ℕ) : s78dg_cs_E (2 * n) = 4 * (n : ℝ) := by
  unfold s78dg_cs_E
  have h : 4 * (2 * n / 2) + 2 * n % 2 = 4 * n := by omega
  rw [h]; push_cast; ring

theorem s78dg_cs_E_odd (n : ℕ) : s78dg_cs_E (2 * n + 1) = 4 * (n : ℝ) + 1 := by
  unfold s78dg_cs_E
  have h : 4 * ((2 * n + 1) / 2) + (2 * n + 1) % 2 = 4 * n + 1 := by omega
  rw [h]; push_cast; ring

theorem s78dg_cs_edge0 (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p) (ε : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)))
    (hε : ∀ t : I, ε t = s78dg_cs_Psi_fun p hp (one, 4 * (n : ℝ) + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε)) = FreeGroup.of ⟨2 * n, by omega⟩ :=
  s78dg_cs_edge_gen p hp one hone e he (2 * n) (by omega) ε (fun t => by
    rw [hε t, s78dg_cs_E_even])

theorem s78dg_cs_edge1 (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p) (ε : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)))
    (hε : ∀ t : I, ε t = s78dg_cs_Psi_fun p hp (one, 4 * (n : ℝ) + 1 + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε)) = FreeGroup.of ⟨2 * n + 1, by omega⟩ :=
  s78dg_cs_edge_gen p hp one hone e he (2 * n + 1) (by omega) ε (fun t => by
    rw [hε t, s78dg_cs_E_odd])

theorem s78dg_cs_edge2 (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p) (ε : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)))
    (hε : ∀ t : I, ε t = s78dg_cs_Psi_fun p hp (one, 4 * (n : ℝ) + 2 + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε)) =
      (FreeGroup.of ⟨2 * n, by omega⟩)⁻¹ := by
  have h := s78dg_cs_edge0 p hp one hone e he n hn ε.symm (fun t => by
    have h1 := s78dg_cs_Psi_rel_a p hp one hone ⟨n, hn⟩ (t : ℝ) t.2.1 t.2.2
    simp only [Fin.val_mk] at h1
    show ε (unitInterval.symm t) = _
    rw [hε, h1]
    congr 2
    rw [unitInterval.coe_symm_eq]; ring)
  have h2 : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε.symm) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε))⁻¹ := rfl
  rw [h2, map_inv] at h
  exact inv_eq_iff_eq_inv.1 h

theorem s78dg_cs_edge3 (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p) (ε : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)))
    (hε : ∀ t : I, ε t = s78dg_cs_Psi_fun p hp (one, 4 * (n : ℝ) + 3 + (t : ℝ))) :
    e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε)) =
      (FreeGroup.of ⟨2 * n + 1, by omega⟩)⁻¹ := by
  have h := s78dg_cs_edge1 p hp one hone e he n hn ε.symm (fun t => by
    have h1 := s78dg_cs_Psi_rel_b p hp one hone ⟨n, hn⟩ (t : ℝ) t.2.1 t.2.2
    simp only [Fin.val_mk] at h1
    show ε (unitInterval.symm t) = _
    rw [hε, h1]
    congr 2
    rw [unitInterval.coe_symm_eq]; ring)
  have h2 : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε.symm) =
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ε))⁻¹ := rfl
  rw [h2, map_inv] at h
  exact inv_eq_iff_eq_inv.1 h


theorem s78dg_cs_vertex_all (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1) :
    ∀ x : ℝ, (∃ n : ℤ, x = n) → (fun u : ℝ => s78dg_cs_Psi_fun p hp (one, u)) x =
      s78dg_cs_Psi_fun p hp (one, 0) := by
  rintro x ⟨n, rfl⟩
  exact s78dg_cs_Psi_vertex p hp one hone n

theorem s78dg_cs_Psi_cont (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) :
    Continuous (fun u : ℝ => s78dg_cs_Psi_fun p hp (one, u)) :=
  (s78dg_cs_Psi_quot p hp).continuous.comp (continuous_const.prodMk continuous_id)

/-- **One handle of the boundary.**  Going once around a block of four edges multiplies the class by
the commutator word. -/
theorem s78dg_cs_block (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n < p)
    (β : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)))
    (hβ : ∀ t : I, β t = s78dg_cs_Psi_fun p hp (one, ((4 * n : ℕ) : ℝ) * (t : ℝ))) :
    ∃ β' : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)),
      (∀ t : I, β' t = s78dg_cs_Psi_fun p hp (one, ((4 * (n + 1) : ℕ) : ℝ) * (t : ℝ))) ∧
      (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β')))⁻¹ =
        (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹ *
          ((FreeGroup.of ⟨2 * n, by omega⟩)⁻¹ * (FreeGroup.of ⟨2 * n + 1, by omega⟩)⁻¹ *
            FreeGroup.of ⟨2 * n, by omega⟩ * FreeGroup.of ⟨2 * n + 1, by omega⟩) := by
  have hf := s78dg_cs_Psi_cont p hp one
  have hv := s78dg_cs_vertex_all p hp one hone
  obtain ⟨ε0, hε0⟩ := s78dg_exists_edge_loop _ hf hv (4 * n)
  obtain ⟨ε1, hε1⟩ := s78dg_exists_edge_loop _ hf hv (4 * n + 1)
  obtain ⟨ε2, hε2⟩ := s78dg_exists_edge_loop _ hf hv (4 * n + 2)
  obtain ⟨ε3, hε3⟩ := s78dg_exists_edge_loop _ hf hv (4 * n + 3)
  obtain ⟨β1, hβ1, hc0⟩ := s78dg_loop_step _ hf hv (4 * n) β ε0 hβ hε0
  obtain ⟨β2, hβ2, hc1⟩ := s78dg_loop_step _ hf hv (4 * n + 1) β1 ε1 hβ1 hε1
  obtain ⟨β3, hβ3, hc2⟩ := s78dg_loop_step _ hf hv (4 * n + 1 + 1) β2 ε2 hβ2 hε2
  obtain ⟨β4, hβ4, hc3⟩ := s78dg_loop_step _ hf hv (4 * n + 1 + 1 + 1) β3 ε3 hβ3 hε3
  refine ⟨β4, fun t => ?_, ?_⟩
  · rw [hβ4 t]
    congr 2
  · have c0 := s78dg_cs_edge0 p hp one hone e he n hn ε0 (fun t => by
      rw [hε0 t]; congr 2; push_cast; ring)
    have c1 := s78dg_cs_edge1 p hp one hone e he n hn ε1 (fun t => by
      rw [hε1 t]; congr 2; push_cast; ring)
    have c2 := s78dg_cs_edge2 p hp one hone e he n hn ε2 (fun t => by
      rw [hε2 t]; congr 2; push_cast; ring)
    have c3 := s78dg_cs_edge3 p hp one hone e he n hn ε3 (fun t => by
      rw [hε3 t]; congr 2; push_cast; ring)
    rw [hc3, map_mul, hc2, map_mul, hc1, map_mul, hc0, map_mul, c0, c1, c2, c3]
    group


theorem s78dg_cs_boundary_induction (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    (n : ℕ) (hn : n ≤ p) :
    ∃ β : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)),
      (∀ t : I, β t = s78dg_cs_Psi_fun p hp (one, ((4 * n : ℕ) : ℝ) * (t : ℝ))) ∧
      (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹ =
        (List.ofFn fun i : Fin n =>
          ((FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ : FreeGroup (Fin (2 * p)))⁻¹ *
            (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)⁻¹ * FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ *
              FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)).prod := by
  induction n with
  | zero =>
    have hv := s78dg_cs_vertex_all p hp one hone
    refine ⟨Path.refl _, fun t => ?_, ?_⟩
    · show _ = _
      simp only [Path.refl_apply, Nat.mul_zero, Nat.cast_zero, zero_mul]
    · have : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (Path.refl (s78dg_cs_Psi_fun p hp (one, 0)))) = 1 := rfl
      rw [this, map_one]
      simp
  | succ n ih =>
    obtain ⟨β, hβ, hc⟩ := ih (by omega)
    obtain ⟨β', hβ', hc'⟩ := s78dg_cs_block p hp one hone e he n (by omega) β hβ
    refine ⟨β', hβ', ?_⟩
    rw [hc', hc, List.ofFn_succ', List.prod_concat]
    simp

/-- **The boundary word.**  The boundary loop of the polygon, read in the free generators of
`π₁` of the punctured chart, has inverse `∏ᵢ aᵢ⁻¹ bᵢ⁻¹ aᵢ bᵢ`. -/
theorem s78dg_cs_boundary_word (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)))
    (he : ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩)
    :
    ∃ β : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)),
      (∀ t : I, β t = s78dg_cs_Psi_fun p hp (one, 4 * (p : ℝ) * (t : ℝ))) ∧
      (e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹ =
        (List.ofFn fun i : Fin p =>
          ((FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ : FreeGroup (Fin (2 * p)))⁻¹ *
            (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)⁻¹ * FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ *
              FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)).prod := by
  obtain ⟨β, hβ, hc⟩ := s78dg_cs_boundary_induction p hp one hone e he p le_rfl
  refine ⟨β, fun t => ?_, hc⟩
  rw [hβ t]
  congr 2
  push_cast; ring


/-- **The circle of radius `1/2` is conjugate to the boundary loop.**  Changing the base point along the
radial path turns the loop `t ↦ Ψ(1/2, 4p t)` into the boundary loop. -/
theorem s78dg_cs_circle_conj (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (half : Set.Ioc (0 : ℝ) 1) (hhalf : (half : ℝ) = 1 / 2)
    (x₁ : ↥(s78dg_cs_U p 0)) (c : Path x₁ x₁)
    (hc : ∀ t : I, c t = s78dg_cs_Psi_fun p hp (half, 4 * (p : ℝ) * (t : ℝ)))
    (β : Path (s78dg_cs_Psi_fun p hp (one, 0)) (s78dg_cs_Psi_fun p hp (one, 0)))
    (hβ : ∀ t : I, β t = s78dg_cs_Psi_fun p hp (one, 4 * (p : ℝ) * (t : ℝ))) :
    ∃ r : Path x₁ (s78dg_cs_Psi_fun p hp (one, 0)),
      FundamentalGroup.fundamentalGroupMulEquivOfPath r
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β) := by
  let ρ : I → Set.Ioc (0 : ℝ) 1 := fun s =>
    ⟨1 / 2 + (s : ℝ) / 2, by have := s.2.1; positivity, by have := s.2.2; linarith⟩
  have hρc : Continuous ρ :=
    Continuous.subtype_mk (continuous_const.add (continuous_subtype_val.div_const 2)) _
  have hρ0 : ρ 0 = half := Subtype.ext (by simp [ρ, hhalf])
  have hρ1 : ρ 1 = one := Subtype.ext (by simp [ρ, hone]; norm_num)
  let F : C(I × I, ↥(s78dg_cs_U p 0)) :=
    ⟨fun q => s78dg_cs_Psi_fun p hp (ρ q.1, 4 * (p : ℝ) * (q.2 : ℝ)),
      (s78dg_cs_Psi_quot p hp).continuous.comp
        ((hρc.comp continuous_fst).prodMk
          (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))⟩
  have hx₁ : x₁ = s78dg_cs_Psi_fun p hp (half, 0) := by
    have := hc 0
    rw [c.source] at this
    rw [this]; simp
  let r : Path x₁ (s78dg_cs_Psi_fun p hp (one, 0)) :=
    { toFun := fun s => s78dg_cs_Psi_fun p hp (ρ s, 0)
      continuous_toFun := (s78dg_cs_Psi_quot p hp).continuous.comp (hρc.prodMk continuous_const)
      source' := by
        show s78dg_cs_Psi_fun p hp (ρ 0, 0) = x₁
        rw [hρ0, hx₁]
      target' := by
        show s78dg_cs_Psi_fun p hp (ρ 1, 0) = _
        rw [hρ1] }
  refine ⟨r, s78dg_pi1_conj r c β ?_⟩
  refine s78dg_square F r β c r (fun s => ?_) (fun t => ?_) (fun t => ?_) (fun s => ?_)
  · show _ = s78dg_cs_Psi_fun p hp (ρ s, 4 * (p : ℝ) * ((0 : I) : ℝ))
    simp
    rfl
  · rw [hβ t]
    show _ = s78dg_cs_Psi_fun p hp (ρ 1, 4 * (p : ℝ) * (t : ℝ))
    rw [hρ1]
  · rw [hc t]
    show _ = s78dg_cs_Psi_fun p hp (ρ 0, 4 * (p : ℝ) * (t : ℝ))
    rw [hρ0]
  · show s78dg_cs_Psi_fun p hp (ρ s, 0) = s78dg_cs_Psi_fun p hp (ρ s, 4 * (p : ℝ) * ((1 : I) : ℝ))
    have := s78dg_cs_Psi_periodic p hp (ρ s) 0
    simp only [zero_add] at this
    rw [← this]
    simp


end LiZhongQC
