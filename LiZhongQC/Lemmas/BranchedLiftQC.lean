import LiZhongQC.Lemmas.BranchedLiftCore
import LiZhongQC.Lemmas.SchottkyClosedGenus
import LiZhongQC.Lemmas.LowGenusQC
import LiZhongQC.Lemmas.QDReflectionHolInverse
import LiZhongQC.Lemmas.UniformizedUniqueness

open Complex Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff Real

noncomputable section

namespace LiZhongQC

universe u

/-- On a closed Riemann surface of genus `0` every holomorphic quadratic differential vanishes (Riemann–Roch:
`Q(S) ≅ L(2K)` with `deg 2K = -4`). -/
theorem s82lc_hqd_genus_zero {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (hS : HasGenus S 0) {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) : q = 0 := by
  have : CompactSpace S := hS.1
  obtain ⟨K, hK⟩ := k22q_canonical_exists (S := S)
  obtain ⟨e⟩ := k22q_canonical_equiv hK
  have hdeg := deg_canonical hS hK
  have hdeg2 : Jacobians.Divisor.deg S (2 • K) < 0 := by
    have : Jacobians.Divisor.deg S (2 • K) = 2 * Jacobians.Divisor.deg S K := by
      simpa only [nsmul_eq_mul, Nat.cast_ofNat] using (map_nsmul (Jacobians.Divisor.deg S) 2 K)
    rw [this, k22rr_degree_eq, hdeg]
    norm_num
  have hl : ellDim (2 • K) = 0 := by
    rw [k22rr_ellDim_eq_lDim]
    exact Jacobians.lDim_eq_zero_of_deg_neg _ hdeg2
  have : FiniteDimensional ℂ (holQuadDiffSubmodule S) := k22q_finite_quadratic (S := S)
  have hfr : Module.finrank ℂ (holQuadDiffSubmodule S) = 0 := by
    rw [← e.finrank_eq]; exact hl
  have hbot : holQuadDiffSubmodule S = ⊥ := Submodule.finrank_eq_zero.1 hfr
  have : q ∈ holQuadDiffSubmodule S := hq
  rw [hbot] at this
  exact (Submodule.mem_bot ℂ).1 this

/-- The complement of a closed discrete subset of a connected surface is connected. -/
theorem s82lc_isPreconnected_compl {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T1Space X]
    [ConnectedSpace X] {D : Set X} (hDc : IsClosed D) (hDd : ∀ b ∈ D, ∃ U ∈ 𝓝 b, U ∩ D ⊆ {b}) :
    IsPreconnected Dᶜ := by
  classical
  intro u v hu hv hcov ⟨a, haD, hau⟩ ⟨c, hcD, hcv⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have huv : ∀ x, x ∉ D → x ∈ u → x ∈ v → False := fun x hx hxu hxv => by
    have : x ∈ Dᶜ ∩ (u ∩ v) := ⟨hx, hxu, hxv⟩
    rw [hne] at this
    exact this
  -- each point of `D` has a punctured connected neighbourhood inside `u` or inside `v`
  have hside : ∀ b ∈ D, ∃ B : Set X, B ⊆ Dᶜ ∧ insert b B ∈ 𝓝 b ∧ (B ⊆ u ∨ B ⊆ v) := by
    intro b hb
    obtain ⟨W, hW, hWD⟩ := hDd b hb
    obtain ⟨B, hBW, hBc, hbB, -, hBn⟩ := s82lc_punctured_nhds b hW
    have hBD : B ⊆ Dᶜ := fun x hx hxD => hbB (by
      have := hWD ⟨hBW hx, hxD⟩
      rw [mem_singleton_iff] at this
      exact this ▸ hx)
    refine ⟨B, hBD, hBn, ?_⟩
    by_contra h
    push Not at h
    obtain ⟨x, hxB, hxu⟩ := Set.not_subset.1 h.1
    obtain ⟨y, hyB, hyv⟩ := Set.not_subset.1 h.2
    obtain ⟨z, hzB, hzu, hzv⟩ := hBc u v hu hv (fun w hw => hcov (hBD hw))
      ⟨y, hyB, (hcov (hBD hyB)).resolve_right hyv⟩ ⟨x, hxB, (hcov (hBD hxB)).resolve_left hxu⟩
    exact huv z (hBD hzB) hzu hzv
  set U' : Set X := {x | (x ∉ D ∧ x ∈ u) ∨ (x ∈ D ∧ ∃ B ⊆ Dᶜ, insert x B ∈ 𝓝 x ∧ B ⊆ u)} with hU'
  set V' : Set X := {x | (x ∉ D ∧ x ∈ v) ∨ (x ∈ D ∧ ∃ B ⊆ Dᶜ, insert x B ∈ 𝓝 x ∧ B ⊆ v)} with hV'
  have hopen : ∀ w : Set X, IsOpen w →
      IsOpen {x | (x ∉ D ∧ x ∈ w) ∨ (x ∈ D ∧ ∃ B ⊆ Dᶜ, insert x B ∈ 𝓝 x ∧ B ⊆ w)} := by
    intro w hw
    rw [isOpen_iff_mem_nhds]
    rintro x (⟨hxD, hxw⟩ | ⟨hxD, B, hBD, hBn, hBw⟩)
    · exact Filter.mem_of_superset (Filter.inter_mem (hDc.isOpen_compl.mem_nhds hxD) (hw.mem_nhds hxw))
        fun y hy => Or.inl hy
    · refine Filter.mem_of_superset hBn ?_
      rintro y (rfl | hy)
      · exact Or.inr ⟨hxD, B, hBD, hBn, hBw⟩
      · exact Or.inl ⟨hBD hy, hBw hy⟩
  obtain ⟨x, -, hxU, hxV⟩ := isPreconnected_univ (α := X) U' V' (hopen u hu) (hopen v hv)
    (fun x _ => by
      by_cases hxD : x ∈ D
      · obtain ⟨B, hBD, hBn, hB | hB⟩ := hside x hxD
        · exact Or.inl (Or.inr ⟨hxD, B, hBD, hBn, hB⟩)
        · exact Or.inr (Or.inr ⟨hxD, B, hBD, hBn, hB⟩)
      · rcases hcov hxD with h | h
        · exact Or.inl (Or.inl ⟨hxD, h⟩)
        · exact Or.inr (Or.inl ⟨hxD, h⟩))
    ⟨a, trivial, Or.inl ⟨haD, hau⟩⟩ ⟨c, trivial, Or.inl ⟨hcD, hcv⟩⟩
  rcases hxU with ⟨hxD, hxu⟩ | ⟨hxD, B, hBD, hBn, hBu⟩
  · rcases hxV with ⟨-, hxv⟩ | ⟨hxD', -⟩
    · exact huv x hxD hxu hxv
    · exact hxD hxD'
  · rcases hxV with ⟨hxD', -⟩ | ⟨-, B', hB'D, hB'n, hB'v⟩
    · exact hxD' hxD
    · have hne := s82lc_nhdsWithin_compl_neBot (P := ({x} : Set X)) (Set.finite_singleton x) x
      obtain ⟨y, hyx, hyB, hyB'⟩ := hne.nonempty_of_mem
        (inter_mem_nhdsWithin _ (Filter.inter_mem hBn hB'n))
      rcases hyB with rfl | hyB
      · exact hyx rfl
      rcases hyB' with rfl | hyB'
      · exact hyx rfl
      exact huv y (hBD hyB) (hBu hyB) (hB'v hyB')

/-- The complement of a discrete subset of a surface is dense. -/
theorem s82lc_dense_compl {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [T1Space X] {D : Set X}
    (hDd : ∀ b ∈ D, ∃ U ∈ 𝓝 b, U ∩ D ⊆ {b}) : Dense Dᶜ := by
  intro x
  rw [mem_closure_iff_nhds]
  intro N hN
  by_cases hxD : x ∈ D
  · obtain ⟨U, hU, hUD⟩ := hDd x hxD
    obtain ⟨B, hBW, -, hxB, ⟨y, hy⟩, -⟩ := s82lc_punctured_nhds x (Filter.inter_mem hN hU)
    refine ⟨y, (hBW hy).1, fun hyD => hxB ?_⟩
    have := hUD ⟨(hBW hy).2, hyD⟩
    rw [mem_singleton_iff] at this
    exact this ▸ hy
  · exact ⟨x, mem_of_mem_nhds hN, hxD⟩

/-- **Equivariance of the lift.**  Let `p : E → Y` be a covering of a surface with deck maps `G` acting transitively
on the fibres, `F : Y → Y` homotopic to the identity on `Y ∖ B` (`B` finite, as maps into `Y`) and `F̃` a lift of
`F`.  Then some deck map `δ` makes `δ ∘ F̃` commute with every deck map. -/
theorem s82lc_lift_equivariant {E Y : Type*} [TopologicalSpace E] [ChartedSpace ℂ E] [T2Space E] [ConnectedSpace E]
    [TopologicalSpace Y] [T1Space Y] {p : E → Y} (hp : IsCoveringMap p) {B : Set Y} (hB : B.Finite)
    {F : Y → Y} (L : C(unitInterval × (Bᶜ : Set Y), Y)) (hL0 : ∀ y, L (0, y) = y) (hL1 : ∀ y, L (1, y) = F y)
    {F' : E → E} (hF'c : Continuous F') (hF' : ∀ e, p (F' e) = F (p e)) (G : Set (E → E))
    (hGc : ∀ g ∈ G, Continuous g) (hG : ∀ g ∈ G, ∀ e, p (g e) = p e)
    (htr : ∀ a b, p a = p b → ∃ g ∈ G, g a = b) :
    ∃ δ ∈ G, ∀ g ∈ G, ∀ e, δ (F' (g e)) = g (δ (F' e)) := by
  set D := p ⁻¹' B with hD
  have hDc : IsClosed D := hB.isClosed.preimage hp.continuous
  have hDd : ∀ b ∈ D, ∃ U ∈ 𝓝 b, U ∩ D ⊆ {b} := by
    intro b hb
    obtain ⟨φ, hbφ, hpφ⟩ := hp.isLocalHomeomorph b
    refine ⟨φ.source ∩ p ⁻¹' (B \ {p b})ᶜ, Filter.inter_mem (φ.open_source.mem_nhds hbφ)
      (hp.continuous.continuousAt.preimage_mem_nhds ((hB.sdiff).isClosed.isOpen_compl.mem_nhds
        fun h => h.2 rfl)), ?_⟩
    rintro x ⟨⟨hxφ, hxB⟩, hxD⟩
    have hpx : p x = p b := by
      by_contra h
      exact hxB ⟨hxD, h⟩
    rw [hpφ] at hpx
    exact φ.injOn hxφ hbφ hpx
  have hΩ : IsPreconnected Dᶜ := s82lc_isPreconnected_compl hDc hDd
  have : PreconnectedSpace (Dᶜ : Set E) := Subtype.preconnectedSpace hΩ
  have hdense : Dense Dᶜ := s82lc_dense_compl hDd
  -- the lifted homotopy on `E ∖ D`
  set M : C(unitInterval × (Dᶜ : Set E), Y) :=
    ⟨fun te => L (te.1, ⟨p te.2, te.2.2⟩), L.continuous.comp (continuous_fst.prodMk
      ((hp.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _))⟩ with hM
  have hM0 : ∀ e, M (0, e) = p ((⟨Subtype.val, continuous_subtype_val⟩ : C((Dᶜ : Set E), E)) e) :=
    fun e => hL0 _
  set M' := hp.liftHomotopy M ⟨Subtype.val, continuous_subtype_val⟩ hM0 with hM'
  have hM'p : ∀ t e, p (M' (t, e)) = M (t, e) := fun t e =>
    congrFun (hp.liftHomotopy_lifts M ⟨Subtype.val, continuous_subtype_val⟩ hM0) (t, e)
  have hM'0 : ∀ e, M' (0, e) = e := hp.liftHomotopy_zero M ⟨Subtype.val, continuous_subtype_val⟩ hM0
  set Ê : (Dᶜ : Set E) → E := fun e => M' (1, e) with hÊ
  have hÊc : Continuous Ê := M'.continuous.comp (continuous_const.prodMk continuous_id)
  have hÊp : ∀ e, p (Ê e) = F (p e) := fun e => by
    show p (M' (1, e)) = _
    rw [hM'p]; exact hL1 _
  have hgD : ∀ g ∈ G, ∀ e ∈ Dᶜ, g e ∈ Dᶜ := fun g hg e he => by
    show p (g e) ∉ B
    rw [hG g hg]; exact he
  -- equivariance of `Ê` by uniqueness of path lifting
  have hÊg : ∀ g (hg : g ∈ G) (e : (Dᶜ : Set E)), Ê ⟨g e, hgD g hg e e.2⟩ = g (Ê e) := by
    intro g hg e
    have := hp.eq_of_comp_eq (g₁ := fun t : unitInterval => M' (t, ⟨g e, hgD g hg e e.2⟩))
      (g₂ := fun t => g (M' (t, e))) (M'.continuous.comp (continuous_id.prodMk continuous_const))
      ((hGc g hg).comp (M'.continuous.comp (continuous_id.prodMk continuous_const)))
      (funext fun t => by
        show p (M' (t, ⟨g e, hgD g hg e e.2⟩)) = p (g (M' (t, e)))
        rw [hM'p, hG g hg, hM'p]
        exact congrArg (fun z : (Bᶜ : Set Y) => L (t, z)) (Subtype.ext (hG g hg e)))
      0 (by show M' (0, ⟨g e, hgD g hg e e.2⟩) = g (M' (0, e)); rw [hM'0, hM'0])
    exact congrFun this 1
  -- normalize `F'` by a deck map at one point; then `Ê = δ ∘ F'` on `E ∖ D`
  obtain ⟨e₀, he₀⟩ := hdense.nonempty
  obtain ⟨δ, hδG, hδ⟩ := htr (F' e₀) (Ê ⟨e₀, he₀⟩) (by rw [hÊp, hF'])
  have hEq : Ê = fun e : (Dᶜ : Set E) => δ (F' e) :=
    hp.eq_of_comp_eq hÊc ((hGc δ hδG).comp (hF'c.comp continuous_subtype_val))
      (funext fun e => by
        show p (Ê e) = p (δ (F' e))
        rw [hÊp, hG δ hδG, hF']) ⟨e₀, he₀⟩ hδ.symm
  refine ⟨δ, hδG, fun g hg => ?_⟩
  have hc1 : Continuous fun e => δ (F' (g e)) := (hGc δ hδG).comp (hF'c.comp (hGc g hg))
  have hc2 : Continuous fun e => g (δ (F' e)) := (hGc g hg).comp ((hGc δ hδG).comp hF'c)
  have := Continuous.ext_on hdense hc1 hc2 (fun e he => by
    have h1 := hÊg g hg ⟨e, he⟩
    rw [hEq] at h1
    exact h1)
  exact fun e => congrFun this e

/-- W7 in genus `> 1`, through the uniformization `ℍ → Y` and Theorem 23.1. -/
theorem s82lc_homotopic_hyperbolic {Y : ClosedRS.{u}} {g : ℕ} (hg : 1 < g) (hY : HasGenus Y.carrier g)
    {B : Set Y.carrier} (hB : B.Finite) (F : Y.carrier ≃ₜ Y.carrier)
    (L : C(unitInterval × (Bᶜ : Set Y.carrier), Y.carrier)) (hL0 : ∀ y, L (0, y) = y) (hL1 : ∀ y, L (1, y) = F y) :
    ContinuousMap.Homotopic (ContinuousMap.id Y.carrier) (F : C(Y.carrier, Y.carrier)) := by
  obtain ⟨Γ, p, -, -, hp⟩ := s22hg_exists_fuchsian_uniformization hg hY
  obtain ⟨τ₁, hτ₁⟩ := hp.2.2.1 (F (p UpperHalfPlane.I))
  obtain ⟨F', hF', -⟩ := exists_lift hp hp F UpperHalfPlane.I τ₁ hτ₁
  set G : Set (UpperHalfPlane → UpperHalfPlane) := {f | ∃ γ ∈ Γ, f = fun τ => γ • τ} with hGdef
  obtain ⟨δ, ⟨d, hd, rfl⟩, hδ⟩ := s82lc_lift_equivariant hp.1 hB L hL0 hL1 F'.continuous hF' G
    (fun f hf => by obtain ⟨γ, -, rfl⟩ := hf; exact continuous_const_smul γ)
    (fun f hf τ => by
      obtain ⟨γ, hγ, rfl⟩ := hf
      exact ((hp.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩).symm)
    (fun a b hab => by
      obtain ⟨γ, hγ, h⟩ := (hp.2.2.2 a b).1 hab
      exact ⟨fun τ => γ • τ, ⟨γ, hγ, rfl⟩, h⟩)
  have hrefl : IsLift p p (Homeomorph.refl Y.carrier) (Homeomorph.refl UpperHalfPlane) := fun τ => rfl
  have h := (thm23_1_homotopy_iff hp hp (Homeomorph.refl Y.carrier) F hrefl hF').2 ⟨d, hd, fun γ hγ τ => by
    have := hδ (fun τ => γ • τ) ⟨γ, hγ, rfl⟩ (F'.symm (d⁻¹ • τ))
    simp only [Homeomorph.apply_symm_apply, smul_inv_smul] at this
    simp only [Homeomorph.refl_apply, Homeomorph.refl_symm, id]
    exact this.symm⟩
  exact h

/-- W7 in genus `1`, through the torus model `ℂ → Y` and an equivariant affine homotopy. -/
theorem s82lc_homotopic_torus {Y : ClosedRS.{u}} (hY : HasGenus Y.carrier 1)
    {B : Set Y.carrier} (hB : B.Finite) (F : Y.carrier ≃ₜ Y.carrier)
    (L : C(unitInterval × (Bᶜ : Set Y.carrier), Y.carrier)) (hL0 : ∀ y, L (0, y) = y) (hL1 : ∀ y, L (1, y) = F y) :
    ContinuousMap.Homotopic (ContinuousMap.id Y.carrier) (F : C(Y.carrier, Y.carrier)) := by
  classical
  obtain ⟨Λ, p, hcov, -, hsurj, hfib⟩ := s24q_torus_cover hY
  -- a lift of `F ∘ p` to `ℂ`
  obtain ⟨z₁, hz₁⟩ := hsurj (F (p 0))
  obtain ⟨F'c, ⟨-, hF'p⟩, -⟩ := hcov.existsUnique_continuousMap_lifts
    ((F : C(Y.carrier, Y.carrier)).comp ⟨p, hcov.continuous⟩) 0 z₁ hz₁
  set F' : ℂ → ℂ := ⇑F'c with hF'
  have hF'p' : ∀ z, p (F' z) = F (p z) := fun z => congrFun hF'p z
  set G : Set (ℂ → ℂ) := {f | ∃ l ∈ Λ.lattice, f = fun z => z + l} with hGdef
  obtain ⟨δ, ⟨c, hc, rfl⟩, hδ⟩ := s82lc_lift_equivariant hcov hB L hL0 hL1 F'c.continuous hF'p' G
    (fun f hf => by obtain ⟨l, -, rfl⟩ := hf; fun_prop)
    (fun f hf z => by
      obtain ⟨l, hl, rfl⟩ := hf
      exact (hfib _ _).2 (by simpa using hl))
    (fun a b hab => ⟨fun z => z + (b - a), ⟨b - a, (hfib b a).1 hab.symm, rfl⟩, by ring⟩)
  -- `F̂ = F' + c` commutes with the lattice translations
  set Fh : ℂ → ℂ := fun z => F' z + c with hFh
  have hFh : ∀ l ∈ Λ.lattice, ∀ z, Fh (z + l) = Fh z + l := fun l hl z => by
    have := hδ (fun z => z + l) ⟨l, hl, rfl⟩ z
    simp only at this
    rw [hFh]; simp only; rw [this]
  set H : unitInterval × ℂ → ℂ := fun tz => tz.2 + (tz.1 : ℂ) * (Fh tz.2 - tz.2) with hH
  have hHc : Continuous H := by
    have : Continuous Fh := F'c.continuous.add continuous_const
    fun_prop
  have hHl : ∀ t (z w : ℂ), p z = p w → p (H (t, z)) = p (H (t, w)) := by
    intro t z w hzw
    have hl : z - w ∈ Λ.lattice := (hfib z w).1 hzw
    have hz : z = w + (z - w) := by ring
    rw [hz]
    have : H (t, w + (z - w)) = H (t, w) + (z - w) := by
      simp only [hH]
      rw [hFh _ hl]
      ring
    rw [this]
    exact (hfib _ _).2 (by simpa using hl)
  have hq : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) p) :=
    IsOpenQuotientMap.id.prodMap ⟨hsurj, hcov.continuous, hcov.isOpenMap⟩
  set K : unitInterval × Y.carrier → Y.carrier := fun ty => p (H (ty.1, Function.surjInv hsurj ty.2)) with hK
  have hKq : K ∘ Prod.map id p = p ∘ H := by
    funext tz
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id, hK]
    exact hHl _ _ _ (Function.surjInv_eq hsurj _)
  have hKc : Continuous K := by
    rw [hq.isQuotientMap.continuous_iff, hKq]
    exact hcov.continuous.comp hHc
  refine ⟨⟨⟨K, hKc⟩, fun y => ?_, fun y => ?_⟩⟩
  · show p (H (0, Function.surjInv hsurj y)) = y
    simp only [hH, Set.Icc.coe_zero, Complex.ofReal_zero, zero_mul, add_zero]
    exact Function.surjInv_eq hsurj y
  · show p (H (1, Function.surjInv hsurj y)) = F y
    simp only [hH, Set.Icc.coe_one, Complex.ofReal_one, one_mul, add_sub_cancel]
    have h1 : p (Fh (Function.surjInv hsurj y)) = p (F' (Function.surjInv hsurj y)) :=
      (hfib _ _).2 (by
        show F' (Function.surjInv hsurj y) + c - F' (Function.surjInv hsurj y) ∈ Λ.lattice
        rw [add_sub_cancel_left]; exact hc)
    rw [h1, hF'p', Function.surjInv_eq hsurj y]

/-- **W7.** -/
theorem s82lc_homotopic_of_punctured {Y : ClosedRS.{u}} (hY : ∃ q : Y.carrier → ℂ → ℂ, IsHolQuadDiff q ∧ q ≠ 0)
    {B : Set Y.carrier} (hB : B.Finite) (F : Y.carrier ≃ₜ Y.carrier)
    (L : C(unitInterval × (Bᶜ : Set Y.carrier), Y.carrier)) (hL0 : ∀ y, L (0, y) = y) (hL1 : ∀ y, L (1, y) = F y) :
    ContinuousMap.Homotopic (ContinuousMap.id Y.carrier) (F : C(Y.carrier, Y.carrier)) := by
  obtain ⟨q, hq, hq0⟩ := hY
  obtain ⟨g, hg⟩ := closed_surface_has_genus (S := Y.carrier)
  rcases Nat.lt_or_ge g 2 with h | h
  · interval_cases g
    · exact absurd (s82lc_hqd_genus_zero hg hq) hq0
    · exact s82lc_homotopic_torus hg hB F L hL0 hL1
  · exact s82lc_homotopic_hyperbolic h hg hB F L hL0 hL1

/-- A continuous injective map on an open subset of `ℂ` has open image (invariance of domain). -/
theorem s82lc_image_open {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn f U) (hi : InjOn f U) :
    IsOpen (f '' U) :=
  LiZhongExternal.Topology.invariance_of_domain_finiteDimensional f U hU hc hi

/-- **Local conjugation.**  An injective continuous map on an open set which, off a finite set, is near every
point a conformal conjugate `β ∘ h ∘ α` of a `K`-q.c. map `h` is `K`-q.c. -/
theorem s82lc_isKQC_of_local {g : ℂ → ℂ} {D L : Set ℂ} {K : ℝ} (hD : IsOpen D) (hK : 1 ≤ K)
    (hc : ContinuousOn g D) (hi : InjOn g D) (hL : L.Finite)
    (hloc : ∀ z ∈ D \ L, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ D ∧ ∃ (α β h : ℂ → ℂ) (V W : Set ℂ),
      IsKQC h V K ∧ α '' U ⊆ V ∧ DifferentiableOn ℂ α U ∧ InjOn α U ∧ IsOpen W ∧ h '' (α '' U) ⊆ W ∧
      DifferentiableOn ℂ β W ∧ InjOn β W ∧ EqOn g (β ∘ h ∘ α) U) :
    IsKQC g D K := by
  have hsec : ∀ (u : ℂ) (v : ℂ) (hv : v ≠ 0), {y : ℝ | u + (y : ℂ) * v ∈ L}.Countable := by
    intro u v hv
    refine (hL.preimage ?_).countable
    intro y₁ _ y₂ _ h
    have : ((y₁ : ℂ) - y₂) * v = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · exact_mod_cast sub_eq_zero.1 h1
    · exact absurd h1 hv
  refine s13x_removable hD hK (qcl_f_isHomeomorphOnto_of_injOn hD hc hi) (hL.measure_zero volume)
    (Filter.Eventually.of_forall fun x => hsec x I I_ne_zero)
    (Filter.Eventually.of_forall fun y => by
      have := hsec ((y : ℂ) * I) 1 one_ne_zero
      simpa [add_comm] using this) fun z hz => ?_
  obtain ⟨U, hUo, hzU, hUD, α, β, h, V, W, hh, hαV, hαd, hαi, hWo, hhW, hβd, hβi, heq⟩ := hloc z hz
  refine ⟨U, hUo, hzU, hUD, ?_⟩
  have hα : IsKQC α U 1 := isKQC_one_of_conformal hUo ⟨hαd, hαi, rfl⟩
  have hαUo : IsOpen (α '' U) := s82lc_image_open hUo hαd.continuousOn hαi
  have hh' : IsKQC h (α '' U) K := ac_t_isKQC_restrict hh hαUo hαV
  have hhUo : IsOpen (h '' (α '' U)) := s82lc_image_open hαUo hh'.2.2.1.1 hh'.2.2.1.2.1
  have hβ : IsKQC β (h '' (α '' U)) 1 := isKQC_one_of_conformal hhUo ⟨hβd.mono hhW, hβi.mono hhW, rfl⟩
  have h1 := thm7_1_comp hα hh' subset_rfl
  have h2 := thm7_1_comp h1 hβ (by rw [Set.image_comp])
  rw [one_mul, mul_one] at h2
  exact ad_isKQC_congr h2 heq

section Conjugation

variable {M₀ N₀ M₁ N₁ : Type*} [TopologicalSpace M₀] [ChartedSpace ℂ M₀] [IsManifold 𝓘(ℂ) ω M₀]
  [TopologicalSpace N₀] [ChartedSpace ℂ N₀] [IsManifold 𝓘(ℂ) ω N₀]
  [TopologicalSpace M₁] [ChartedSpace ℂ M₁] [IsManifold 𝓘(ℂ) ω M₁]
  [TopologicalSpace N₁] [ChartedSpace ℂ N₁] [IsManifold 𝓘(ℂ) ω N₁]

/-- **Chart-level conjugation.**  If `τ ∘ A = B ∘ σ` near `m` for local biholomorphisms `σ`, `τ`, then near the
chart point of `m` the local expression of `A` (at any base point `a`) is a conformal conjugate of the local
expression of `B` at `σ m`. -/
theorem s82lc_conj_data {A : M₀ → N₀} {B : M₁ → N₁} (hA : Continuous A) (hB : Continuous B) {K : ℝ}
    (hBK : ∀ b, IsKQC (localMapExpr B b) (localMapDomain B b) K)
    {σ : OpenPartialHomeomorph M₀ M₁} {τ : OpenPartialHomeomorph N₀ N₁}
    (hσ : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ σ.source) (hτ' : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) τ.symm τ.target)
    {m : M₀} (hm : m ∈ σ.source) (hAm : A m ∈ τ.source)
    (hcomm : ∀ x ∈ σ.source, A x ∈ τ.source → τ (A x) = B (σ x)) (a : M₀) {z : ℂ}
    (hz : z ∈ localMapDomain A a) (hzm : (chartAt ℂ a).symm z = m) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ localMapDomain A a ∧ ∃ (α β h : ℂ → ℂ) (V W : Set ℂ),
      IsKQC h V K ∧ α '' U ⊆ V ∧ DifferentiableOn ℂ α U ∧ InjOn α U ∧ IsOpen W ∧ h '' (α '' U) ⊆ W ∧
      DifferentiableOn ℂ β W ∧ InjOn β W ∧ EqOn (localMapExpr A a) (β ∘ h ∘ α) U := by
  set b := σ m with hb
  set φ := chartAt ℂ a with hφ
  set ψ := chartAt ℂ (A a) with hψ
  set χ := chartAt ℂ b with hχ
  set χ' := chartAt ℂ (B b) with hχ'
  set O := σ.source ∩ σ ⁻¹' (χ.source ∩ B ⁻¹' χ'.source) with hO
  have hOo : IsOpen O := σ.isOpen_inter_preimage (χ.open_source.inter (χ'.open_source.preimage hB))
  set O' := O ∩ A ⁻¹' (τ.source ∩ ψ.source) with hO'
  have hO'o : IsOpen O' := hOo.inter ((τ.open_source.inter ψ.open_source).preimage hA)
  set U := φ.target ∩ φ.symm ⁻¹' O' with hU
  have hUo : IsOpen U := φ.isOpen_inter_preimage_symm hO'o
  have hzU : z ∈ U := by
    refine ⟨hz.1, ?_⟩
    show φ.symm z ∈ O'
    rw [hzm]
    exact ⟨⟨hm, mem_chart_source ℂ b, mem_chart_source ℂ _⟩, hAm, by rw [← hzm]; exact hz.2⟩
  set α : ℂ → ℂ := fun w => χ (σ (φ.symm w)) with hα
  set h : ℂ → ℂ := localMapExpr B b with hh
  set β : ℂ → ℂ := fun u => ψ (τ.symm (χ'.symm u)) with hβ
  set W := χ'.target ∩ χ'.symm ⁻¹' (τ.target ∩ τ.symm ⁻¹' ψ.source) with hW
  have hWo : IsOpen W := χ'.isOpen_inter_preimage_symm (τ.isOpen_inter_preimage_symm ψ.open_source)
  refine ⟨U, hUo, hzU, fun w hw => ⟨hw.1, hw.2.2.2⟩, α, β, h, localMapDomain B b, W, hBK b, ?_, ?_, ?_, hWo,
    ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hx := hw.2.1
    refine ⟨χ.map_source hx.2.1, ?_⟩
    show B (χ.symm (χ (σ (φ.symm w)))) ∈ χ'.source
    rw [χ.left_inv hx.2.1]
    exact hx.2.2
  · intro w hw
    have hx := hw.2
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ.symm w := mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ a) hw.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) σ (φ.symm w) := hσ.mdifferentiableAt (σ.open_source.mem_nhds hx.1.1)
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ (σ (φ.symm w)) := mdifferentiableAt_atlas (chart_mem_atlas ℂ b) hx.1.2.1
    exact (mdifferentiableAt_iff_differentiableAt.1 (h3.comp w (h2.comp w h1))).differentiableWithinAt
  · intro w₁ hw₁ w₂ hw₂ heq
    have h1 := χ.injOn hw₁.2.1.2.1 hw₂.2.1.2.1 heq
    have h2 := σ.injOn hw₁.2.1.1 hw₂.2.1.1 h1
    exact φ.symm.injOn hw₁.1 hw₂.1 h2
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hx := hw.2
    set x := φ.symm w
    have hBσ : h (α w) = χ' (B (σ x)) := by
      show χ' (B (χ.symm (χ (σ x)))) = _
      rw [χ.left_inv hx.1.2.1]
    rw [hBσ]
    refine ⟨χ'.map_source hx.1.2.2, ?_⟩
    show χ'.symm (χ' (B (σ x))) ∈ τ.target ∩ τ.symm ⁻¹' ψ.source
    rw [χ'.left_inv hx.1.2.2, ← hcomm x hx.1.1 hx.2.1]
    exact ⟨τ.map_source hx.2.1, show τ.symm (τ (A x)) ∈ ψ.source by rw [τ.left_inv hx.2.1]; exact hx.2.2⟩
  · intro u hu
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) χ'.symm u := mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ _) hu.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) τ.symm (χ'.symm u) :=
      hτ'.mdifferentiableAt (τ.open_target.mem_nhds hu.2.1)
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (τ.symm (χ'.symm u)) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ _) hu.2.2
    exact (mdifferentiableAt_iff_differentiableAt.1 (h3.comp u (h2.comp u h1))).differentiableWithinAt
  · intro u₁ hu₁ u₂ hu₂ heq
    have h1 := ψ.injOn hu₁.2.2 hu₂.2.2 heq
    have h2 := τ.symm.injOn hu₁.2.1 hu₂.2.1 h1
    exact χ'.symm.injOn hu₁.1 hu₂.1 h2
  · intro w hw
    have hx := hw.2
    set x := φ.symm w
    show ψ (A x) = ψ (τ.symm (χ'.symm (χ' (B (χ.symm (χ (σ x)))))))
    rw [χ.left_inv hx.1.2.1, χ'.left_inv hx.1.2.2, ← hcomm x hx.1.1 hx.2.1, τ.left_inv hx.2.1]

end Conjugation

/-- **The minimal dilatation is attained**: a quasiconformal map with `K[f] ≤ K` (`K ≥ 1`) is `K`-q.c. -/
theorem s82lc_isKQCRS_of_maxDil {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace N] [ChartedSpace ℂ N] {f : M ≃ₜ N} (hf : IsQCRS f) {K : ℝ} (hK : 1 ≤ K)
    (hle : maxDilatationRS f ≤ ENNReal.ofReal K) : IsKQCRS f K := by
  obtain ⟨K₀, hK₀⟩ := hf
  refine ⟨hK, fun x => ?_⟩
  have h0 := hK₀.2 x
  have hD := h0.1
  have hhom : IsHomeomorphOnto (localMapExpr f x) (localMapDomain f x)
      (localMapExpr f x '' localMapDomain f x) := h0.2.2.1
  obtain ⟨hacl, hineq₀⟩ := (thm10_1_isKQC_iff hD hK₀.1 hhom).1 h0
  refine (thm10_1_isKQC_iff hD hK hhom).2 ⟨hacl, ?_⟩
  have hloc : maxDilatation (localMapExpr f x) (localMapDomain f x) ≤ ENNReal.ofReal K :=
    (le_iSup (fun x => maxDilatation (localMapExpr f x) (localMapDomain f x)) x).trans hle
  have hae : ∀ᵐ w ∂(volume.restrict (localMapDomain f x)), ENNReal.ofReal ((‖dz (localMapExpr f x) w‖ +
      ‖dzbar (localMapExpr f x) w‖) / (‖dz (localMapExpr f x) w‖ - ‖dzbar (localMapExpr f x) w‖)) ≤ ENNReal.ofReal K :=
    (ENNReal.ae_le_essSup _).mono fun w hw => hw.trans hloc
  filter_upwards [hae, hineq₀] with w hw hw₀
  set a := ‖dz (localMapExpr f x) w‖
  set b := ‖dzbar (localMapExpr f x) w‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  rcases lt_or_eq_of_le (show b ≤ a by nlinarith [hK₀.1]) with hab | hab
  · have hq : (a + b) / (a - b) ≤ K :=
      (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hw
    rw [div_le_iff₀ (by linarith)] at hq
    linarith
  · have : a + b ≤ 0 := by rw [hab] at hw₀ ⊢; nlinarith
    rw [hab]
    nlinarith

section LiftQC

variable {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [ConnectedSpace S₀]
  [IsManifold 𝓘(ℂ) ω S₀] [TopologicalSpace S] [ChartedSpace ℂ S] [ConnectedSpace S]
  [IsManifold 𝓘(ℂ) ω S]

/-- The embedding `ι : S → X` as an open partial homeomorphism, holomorphic in both directions. -/
theorem s82lc_iota_oph {g n : ℕ} (F : FiniteTypeStructure S g n 0) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F.embedding.toOpenPartialHomeomorph F.ι)
        (F.embedding.toOpenPartialHomeomorph F.ι).source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (F.embedding.toOpenPartialHomeomorph F.ι).symm
        (F.embedding.toOpenPartialHomeomorph F.ι).target ∧
      (F.embedding.toOpenPartialHomeomorph F.ι).target = (↑F.P)ᶜ := by
  have hrange : range F.ι = (↑F.P : Set F.X.carrier)ᶜ := by rw [F.range_ι]; simp
  refine ⟨F.holomorphic.mdifferentiableOn, ?_, ?_⟩
  · have := s31inv_symm_mdifferentiableOn F.embedding.injective F.holomorphic
    simpa using this
  · simpa using hrange

/-- The points of a cover over the finite set `P` form a finite set. -/
theorem s82lc_branch_finite {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1) :
    (pr ⁻¹' (↑P : Set X.carrier)).Finite := by
  rw [← Set.biUnion_preimage_singleton]
  exact P.finite_toSet.biUnion fun x hx =>
    Set.finite_of_ncard_ne_zero (by rw [hpr.2.2.2 x hx]; exact one_ne_zero)

/-- Continuity of a local expression on its domain. -/
theorem s82lc_localMapExpr_continuousOn {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace N] [ChartedSpace ℂ N] {A : M → N} (hA : Continuous A) (a : M) :
    ContinuousOn (localMapExpr A a) (localMapDomain A a) :=
  (chartAt ℂ (A a)).continuousOn.comp (hA.comp_continuousOn ((chartAt ℂ a).continuousOn_symm.mono
    fun _ hz => hz.1)) fun _ hz => hz.2

/-- `K`-quasiconformality transfers from `f` to a lift `Φ`. -/
theorem s82lc_lift_isKQCRS {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {Y₀ Y₁ : ClosedRS.{u}} {pr₀ : Y₀.carrier → F₀.X.carrier} {pr₁ : Y₁.carrier → F₁.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    (hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1)
    {f : S₀ ≃ₜ S} {Φ : Y₀.carrier ≃ₜ Y₁.carrier}
    (hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (Φ y) = F₁.ι (f s)) {K : ℝ} (hfK : IsKQCRS f K) : IsKQCRS Φ K := by
  classical
  obtain ⟨-, hreg₀, -⟩ := s82lc_local_form hpr₀
  obtain ⟨-, hreg₁, -⟩ := s82lc_local_form hpr₁
  obtain ⟨hι₀, hι₀', hι₀t⟩ := s82lc_iota_oph F₀
  obtain ⟨hι₁, hι₁', hι₁t⟩ := s82lc_iota_oph F₁
  set I₀ := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hI₀
  set I₁ := F₁.embedding.toOpenPartialHomeomorph F₁.ι with hI₁
  have hrange₀ : range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by rw [F₀.range_ι]; simp
  have hrange₁ : range F₁.ι = (↑F₁.P : Set F₁.X.carrier)ᶜ := by rw [F₁.range_ι]; simp
  refine ⟨hfK.1, fun y => ?_⟩
  set φ := chartAt ℂ y
  refine s82lc_isKQC_of_local (L := φ '' (φ.source ∩ pr₀ ⁻¹' ↑F₀.P)) (s23_localMapDomain_isOpen Φ.continuous y)
    hfK.1 (s82lc_localMapExpr_continuousOn Φ.continuous y) (s23_c1_injOn_localMapExpr Φ.injective y)
    (((s82lc_branch_finite hpr₀).subset inter_subset_right).image _) fun z hz => ?_
  set m := φ.symm z
  have hmφ : m ∈ φ.source := φ.map_target hz.1.1
  have hmP : pr₀ m ∉ F₀.P := fun h => hz.2 ⟨m, ⟨hmφ, h⟩, φ.right_inv hz.1.1⟩
  obtain ⟨s, hs⟩ : pr₀ m ∈ range F₀.ι := by rw [hrange₀]; exact hmP
  have hΦm : pr₁ (Φ m) = F₁.ι (f s) := hΦ m s hs.symm
  have hΦmP : pr₁ (Φ m) ∉ F₁.P := by
    rw [hΦm]
    have : F₁.ι (f s) ∈ range F₁.ι := ⟨_, rfl⟩
    rw [hrange₁] at this
    exact this
  obtain ⟨e₀, hme₀, heq₀, -⟩ := hreg₀ m hmP
  obtain ⟨e₁, hme₁, heq₁, he₁'⟩ := hreg₁ (Φ m) hΦmP
  set σ := e₀.trans I₀.symm with hσ
  set τ := e₁.trans I₁.symm with hτ
  have hσm : m ∈ σ.source := ⟨hme₀, by
    show e₀ m ∈ I₀.target
    rw [hι₀t, ← heq₀ hme₀]; exact hmP⟩
  have hτm : Φ m ∈ τ.source := ⟨hme₁, by
    show e₁ (Φ m) ∈ I₁.target
    rw [hι₁t, ← heq₁ hme₁]; exact hΦmP⟩
  have hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ σ.source := by
    intro x hx
    have h1 : MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) e₀ e₀.source x :=
      (hpr₀.1 x).mdifferentiableWithinAt.congr (fun w hw => (heq₀ hw).symm) (heq₀ hx.1).symm
    have h2 := hι₀' (e₀ x) hx.2
    exact (h2.comp x (h1.mono inter_subset_left) fun w hw => hw.2)
  have hτd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) τ.symm τ.target := by
    intro u hu
    have hu' : u ∈ I₁.source ∧ I₁ u ∈ e₁.target := by simpa [hτ] using hu
    have h1 := hι₁ u hu'.1
    have h2 := he₁' (I₁ u) hu'.2
    exact h2.comp u (h1.mono (fun w hw => by simpa [hτ] using hw.1)) fun w hw =>
      (by simpa [hτ] using hw : w ∈ I₁.source ∧ I₁ w ∈ e₁.target).2
  refine s82lc_conj_data Φ.continuous f.continuous (fun b => hfK.2 b) hσd hτd hσm hτm ?_ y hz.1 rfl
  intro x hx hxτ
  have hx0 : e₀ x = pr₀ x := (heq₀ hx.1).symm
  have hs' : F₀.ι (σ x) = pr₀ x := by
    show F₀.ι (I₀.symm (e₀ x)) = pr₀ x
    have := I₀.right_inv hx.2
    rw [← hx0]
    exact this
  have hΦx : pr₁ (Φ x) = F₁.ι (f (σ x)) := hΦ x (σ x) hs'.symm
  show I₁.symm (e₁ (Φ x)) = f (σ x)
  rw [← heq₁ hxτ.1, hΦx]
  exact I₁.left_inv (mem_univ _)

/-- `K`-quasiconformality transfers from a lift `Φ` back to `f`. -/
theorem s82lc_isKQCRS_of_lift {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {Y₀ Y₁ : ClosedRS.{u}} {pr₀ : Y₀.carrier → F₀.X.carrier} {pr₁ : Y₁.carrier → F₁.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    (hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1)
    {f : S₀ ≃ₜ S} {Φ : Y₀.carrier ≃ₜ Y₁.carrier}
    (hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (Φ y) = F₁.ι (f s)) {K : ℝ} (hΦK : IsKQCRS Φ K) : IsKQCRS f K := by
  classical
  obtain ⟨-, hreg₀, -⟩ := s82lc_local_form hpr₀
  obtain ⟨-, hreg₁, -⟩ := s82lc_local_form hpr₁
  obtain ⟨hι₀, hι₀', hι₀t⟩ := s82lc_iota_oph F₀
  obtain ⟨hι₁, hι₁', hι₁t⟩ := s82lc_iota_oph F₁
  set I₀ := F₀.embedding.toOpenPartialHomeomorph F₀.ι with hI₀
  set I₁ := F₁.embedding.toOpenPartialHomeomorph F₁.ι with hI₁
  have hrange₀ : range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by rw [F₀.range_ι]; simp
  have hrange₁ : range F₁.ι = (↑F₁.P : Set F₁.X.carrier)ᶜ := by rw [F₁.range_ι]; simp
  have hιP₀ : ∀ s, F₀.ι s ∉ F₀.P := fun s => by
    have : F₀.ι s ∈ range F₀.ι := ⟨_, rfl⟩
    rw [hrange₀] at this; exact this
  have hιP₁ : ∀ s, F₁.ι s ∉ F₁.P := fun s => by
    have : F₁.ι s ∈ range F₁.ι := ⟨_, rfl⟩
    rw [hrange₁] at this; exact this
  refine ⟨hΦK.1, fun s₁ => ?_⟩
  set χ := chartAt ℂ s₁
  refine s82lc_isKQC_of_local (L := ∅) (s23_localMapDomain_isOpen f.continuous s₁) hΦK.1
    (s82lc_localMapExpr_continuousOn f.continuous s₁) (s23_c1_injOn_localMapExpr f.injective s₁)
    finite_empty fun z hz => ?_
  set s := χ.symm z
  obtain ⟨t, ht⟩ := hpr₀.2.1 (F₀.ι s)
  have htP : pr₀ t ∉ F₀.P := by rw [ht]; exact hιP₀ s
  have hΦt : pr₁ (Φ t) = F₁.ι (f s) := hΦ t s ht
  have hΦtP : pr₁ (Φ t) ∉ F₁.P := by rw [hΦt]; exact hιP₁ _
  obtain ⟨e₀, hte₀, heq₀, he₀'⟩ := hreg₀ t htP
  obtain ⟨e₁, hte₁, heq₁, he₁'⟩ := hreg₁ (Φ t) hΦtP
  set σ₀ := I₀.trans e₀.symm with hσ₀
  have hσ₀o : IsOpen (σ₀.source ∩ σ₀ ⁻¹' (Φ ⁻¹' e₁.source)) :=
    σ₀.isOpen_inter_preimage (e₁.open_source.preimage Φ.continuous)
  set σ := σ₀.restrOpen _ hσ₀o with hσ
  set τ := I₁.trans e₁.symm with hτ
  have he₀t : e₀ t = F₀.ι s := by rw [← heq₀ hte₀]; exact ht
  have he₁t : e₁ (Φ t) = F₁.ι (f s) := by rw [← heq₁ hte₁]; exact hΦt
  have hσ₀s : σ₀ s = t := by
    show e₀.symm (F₀.ι s) = t
    rw [← he₀t, e₀.left_inv hte₀]
  have hsσ₀ : s ∈ σ₀.source := ⟨mem_univ _, by
    show F₀.ι s ∈ e₀.target
    rw [← he₀t]; exact e₀.map_source hte₀⟩
  have hsσ : s ∈ σ.source := ⟨hsσ₀, hsσ₀, by
    show Φ (σ₀ s) ∈ e₁.source
    rw [hσ₀s]; exact hte₁⟩
  have hfsτ : f s ∈ τ.source := ⟨mem_univ _, by
    show F₁.ι (f s) ∈ e₁.target
    rw [← he₁t]; exact e₁.map_source hte₁⟩
  have hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ σ.source := by
    intro x hx
    have h1 := hι₀ x (mem_univ x)
    have h2 := he₀' (F₀.ι x) hx.1.2
    exact h2.comp x (h1.mono (subset_univ _)) fun w hw => hw.1.2
  have hτd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) τ.symm τ.target := by
    intro u hu
    have hu' : u ∈ e₁.source ∧ e₁ u ∈ I₁.target := by simpa [hτ] using hu
    have h1 : MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) e₁ e₁.source u :=
      (hpr₁.1 u).mdifferentiableWithinAt.congr (fun w hw => (heq₁ hw).symm) (heq₁ hu'.1).symm
    have h2 := hι₁' (e₁ u) hu'.2
    exact h2.comp u (h1.mono fun w hw => by simpa [hτ] using hw.1) fun w hw =>
      (by simpa [hτ] using hw : w ∈ e₁.source ∧ e₁ w ∈ I₁.target).2
  refine s82lc_conj_data f.continuous Φ.continuous (fun b => hΦK.2 b) hσd hτd hsσ hfsτ ?_ s₁ hz.1 rfl
  intro x hx hxτ
  have hx1 : Φ (σ x) ∈ e₁.source := hx.2.2
  have hpr0 : pr₀ (σ x) = F₀.ι x := by
    have h1 : σ x ∈ e₀.source := e₀.map_target hx.1.2
    rw [heq₀ h1]
    exact e₀.right_inv hx.1.2
  show e₁.symm (I₁ (f x)) = Φ (σ x)
  rw [show I₁ (f x) = F₁.ι (f x) from rfl, ← hΦ (σ x) x hpr0, heq₁ hx1, e₁.left_inv hx1]

end LiftQC

/-- **W5.** -/
theorem s82lc_lift_qc {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀] [ConnectedSpace S₀]
    [IsManifold 𝓘(ℂ) ω S₀] [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {Y₀ Y₁ : ClosedRS.{u}} {pr₀ : Y₀.carrier → F₀.X.carrier} {pr₁ : Y₁.carrier → F₁.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    (hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1)
    {f : S₀ ≃ₜ S} (hf : IsQCRS f) {Φ : Y₀.carrier ≃ₜ Y₁.carrier}
    (hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (Φ y) = F₁.ι (f s)) :
    IsQCRS Φ ∧ maxDilatationRS Φ = maxDilatationRS f := by
  obtain ⟨K, hK⟩ := hf
  have hΦqc : IsQCRS Φ := ⟨K, s82lc_lift_isKQCRS F₀ F₁ hpr₀ hpr₁ hΦ hK⟩
  refine ⟨hΦqc, le_antisymm ?_ ?_⟩
  · -- `K[Φ] ≤ K[f]`
    have h1 : 1 ≤ maxDilatationRS f := s29_m_one_le_maxDilatationRS ⟨K, hK⟩
    have hfin : maxDilatationRS f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (maxDilatationRS_le hK)
    have hK' : 1 ≤ (maxDilatationRS f).toReal := by
      have := ENNReal.toReal_mono hfin h1
      simpa using this
    have hfK := s82lc_isKQCRS_of_maxDil ⟨K, hK⟩ hK' (by rw [ENNReal.ofReal_toReal hfin])
    have := maxDilatationRS_le (s82lc_lift_isKQCRS F₀ F₁ hpr₀ hpr₁ hΦ hfK)
    rwa [ENNReal.ofReal_toReal hfin] at this
  · -- `K[f] ≤ K[Φ]`
    have h1 : 1 ≤ maxDilatationRS Φ := s29_m_one_le_maxDilatationRS hΦqc
    obtain ⟨KΦ, hKΦ⟩ := hΦqc
    have hfin : maxDilatationRS Φ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (maxDilatationRS_le hKΦ)
    have hK' : 1 ≤ (maxDilatationRS Φ).toReal := by
      have := ENNReal.toReal_mono hfin h1
      simpa using this
    have hΦK := s82lc_isKQCRS_of_maxDil ⟨KΦ, hKΦ⟩ hK' (by rw [ENNReal.ofReal_toReal hfin])
    have := maxDilatationRS_le (s82lc_isKQCRS_of_lift F₀ F₁ hpr₀ hpr₁ hΦ hΦK)
    rwa [ENNReal.ofReal_toReal hfin] at this


end LiZhongQC
