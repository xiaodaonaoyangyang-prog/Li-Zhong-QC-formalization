import LiZhongQC.Lemmas.Winding
import LiZhongQC.Lemmas.JordanBridge

/-!
# Invariance of domain in the plane

Munkres §62 transcribed to `ℂ`: Borsuk's lemma (a point in a bounded component of the complement of a compact
set is "essential"), the non-separation of a topological closed disc, and invariance of domain, assembled with
the Jordan curve theorem from `Lemmas/JordanBridge` and the winding-number lifts of `Lemmas/Winding`.
Consumers: `lemma9_1_menchoff` (S09), `lemma12_1` (S12).
-/

open Complex Set Metric Filter Topology Bornology Function
open scoped Real Classical

noncomputable section

namespace LiZhongQC

/-- A frontier point of a component of the open set `Kᶜ` cannot itself lie in `Kᶜ` (else its
own component, being an open neighbourhood contained in `Kᶜ`, would meet `W` and hence coincide
with `W`, contradicting that the point is a frontier point of `W`). -/
theorem iod_frontier_connectedComponentIn_subset {K : Set ℂ} (hK : IsClosed K) (a : ℂ) :
    frontier (connectedComponentIn Kᶜ a) ⊆ K := by
  set W : Set ℂ := connectedComponentIn Kᶜ a with hWdef
  have hKcOpen : IsOpen Kᶜ := isOpen_compl_iff.mpr hK
  have hWopen : IsOpen W := hKcOpen.connectedComponentIn
  intro z hz
  by_contra hzK
  have hzKc : z ∈ Kᶜ := hzK
  set V : Set ℂ := connectedComponentIn Kᶜ z with hVdef
  have hVopen : IsOpen V := hKcOpen.connectedComponentIn
  have hzV : z ∈ V := mem_connectedComponentIn hzKc
  rw [hWopen.frontier_eq] at hz
  have hzclosure : z ∈ closure W := hz.1
  have hzWc : z ∉ W := hz.2
  have hVnhds : V ∈ 𝓝 z := hVopen.mem_nhds hzV
  obtain ⟨y, hyV, hyW⟩ := mem_closure_iff_nhds.mp hzclosure V hVnhds
  have h1 : V = connectedComponentIn Kᶜ y := connectedComponentIn_eq hyV
  have h2 : W = connectedComponentIn Kᶜ y := connectedComponentIn_eq hyW
  have hVeqW : V = W := h1.trans h2.symm
  rw [hVeqW] at hzV
  exact hzWc hzV

/-- Tietze extension, specialised to `ℂ`-valued functions continuous on a closed set. -/
theorem iod_tietze_extension {K : Set ℂ} (hK : IsClosed K) {θ : ℂ → ℂ} (hθ : ContinuousOn θ K) :
    ∃ Θ : ℂ → ℂ, Continuous Θ ∧ ∀ z ∈ K, Θ z = θ z := by
  have hf : Continuous (K.restrict θ) := continuousOn_iff_continuous_restrict.mp hθ
  obtain ⟨g, hg⟩ := (ContinuousMap.mk (K.restrict θ) hf).exists_restrict_eq hK
  refine ⟨g, g.continuous, fun z hz => ?_⟩
  have hgz := DFunLike.congr_fun hg (⟨z, hz⟩ : K)
  rwa [ContinuousMap.restrict_apply] at hgz

/-- Pasting continuity across the closure of an open set `W`: if `f` and `g` agree on
`frontier W` and are each continuous on all of `ℂ`, the function equal to `f` on `closure W`
and `g` elsewhere is continuous. -/
theorem iod_continuous_if_closure {W : Set ℂ} (hW : IsOpen W) {f g : ℂ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ z ∈ frontier W, f z = g z) :
    Continuous (fun z => if z ∈ closure W then f z else g z) := by
  have hWsubinterior : W ⊆ interior (closure W) := interior_maximal subset_closure hW
  have hp : ∀ z ∈ frontier (closure W), f z = g z := by
    intro z hz
    apply hfg
    rw [hW.frontier_eq]
    refine ⟨?_, fun hzW => hz.2 (hWsubinterior hzW)⟩
    have := hz.1
    rwa [closure_closure] at this
  exact Continuous.if hp hf hg

/-- **Borsuk's lemma in the plane**: if `a` lies outside a compact `K` and its component `W` of
`Kᶜ` is bounded, then `z ↦ z - a` has no continuous logarithm on `K`. -/
theorem not_exists_continuousOn_log_of_isBounded_connectedComponentIn {K : Set ℂ} (hK : IsCompact K)
    {a : ℂ} (ha : a ∉ K) (hbdd : Bornology.IsBounded (connectedComponentIn Kᶜ a)) :
    ¬ ∃ θ : ℂ → ℂ, ContinuousOn θ K ∧ ∀ z ∈ K, Complex.exp (θ z) = z - a := by
  rintro ⟨θ, hθcont, hθexp⟩
  have hKclosed : IsClosed K := hK.isClosed
  set W : Set ℂ := connectedComponentIn Kᶜ a with hWdef
  have hKcOpen : IsOpen Kᶜ := isOpen_compl_iff.mpr hKclosed
  have hWopen : IsOpen W := hKcOpen.connectedComponentIn
  have haKc : a ∈ Kᶜ := ha
  have haW : a ∈ W := mem_connectedComponentIn haKc
  have hWfr : frontier W ⊆ K := iod_frontier_connectedComponentIn_subset hKclosed a
  have haclosureW : a ∈ closure W := subset_closure haW
  -- a ball around `a` containing `closure W`
  have hbddclosure : Bornology.IsBounded (closure W) := hbdd.closure
  obtain ⟨R, hR0, hWsub⟩ := hbddclosure.subset_ball_lt 0 a
  -- Tietze extension of `θ`
  obtain ⟨Θ, hΘcont, hΘeq⟩ := iod_tietze_extension hKclosed hθcont
  -- the pasted, nowhere-vanishing map `m`
  set m : ℂ → ℂ := fun z => if z ∈ closure W then Complex.exp (Θ z) else z - a with hmdef
  have hmcont : Continuous m := by
    apply iod_continuous_if_closure hWopen
    · exact Complex.continuous_exp.comp hΘcont
    · exact continuous_id.sub continuous_const
    · intro z hz
      have hzK : z ∈ K := hWfr hz
      show Complex.exp (Θ z) = z - a
      rw [hΘeq z hzK]
      exact hθexp z hzK
  have hmne : ∀ z, m z ≠ 0 := by
    intro z
    by_cases hzc : z ∈ closure W
    · show (if z ∈ closure W then Complex.exp (Θ z) else z - a) ≠ 0
      rw [if_pos hzc]
      exact Complex.exp_ne_zero _
    · show (if z ∈ closure W then Complex.exp (Θ z) else z - a) ≠ 0
      rw [if_neg hzc]
      intro hz0
      apply hzc
      rw [sub_eq_zero] at hz0
      rw [hz0]
      exact haclosureW
  have hcircle_notin : ∀ t : ℝ,
      (a + (R : ℂ) * Complex.exp (2 * π * I * (t : ℂ))) ∉ closure W := by
    intro t hmem
    have hlt := hWsub hmem
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul] at hlt
    have hexpnorm : ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
      have heq : (2 : ℂ) * π * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [heq]
      exact Complex.norm_exp_ofReal_mul_I (2 * π * t)
    rw [hexpnorm, mul_one, Complex.norm_real, Real.norm_of_nonneg hR0.le] at hlt
    exact lt_irrefl R hlt
  have hmcircle : ∀ t : ℝ,
      m (a + (R : ℂ) * Complex.exp (2 * π * I * (t : ℂ))) =
        (R : ℂ) * Complex.exp (2 * π * I * (t : ℂ)) := by
    intro t
    show (if (a + (R:ℂ) * Complex.exp (2 * π * I * (t : ℂ))) ∈ closure W
        then Complex.exp (Θ (a + (R:ℂ) * Complex.exp (2 * π * I * (t : ℂ))))
        else (a + (R:ℂ) * Complex.exp (2 * π * I * (t : ℂ))) - a) =
          (R : ℂ) * Complex.exp (2 * π * I * (t : ℂ))
    rw [if_neg (hcircle_notin t), add_sub_cancel_left]
  -- the homotopy contracting the circle of radius `R` to the point `a`
  set H : ℝ → ℝ → ℂ := fun s t => m (a + (s : ℂ) * (R : ℂ) * Complex.exp (2 * π * I * (t : ℂ)))
    with hHdef
  have hHcont : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1) := by
    apply Continuous.continuousOn
    have : Function.uncurry H = fun p : ℝ × ℝ =>
        m (a + (p.1 : ℂ) * (R : ℂ) * Complex.exp (2 * π * I * (p.2 : ℂ))) := rfl
    rw [this]
    apply hmcont.comp
    fun_prop
  have hHper : ∀ s ∈ Icc (0 : ℝ) 1, H s 1 = H s 0 := by
    intro s _
    show m (a + (s:ℂ) * (R:ℂ) * Complex.exp (2 * π * I * ((1:ℝ):ℂ))) =
      m (a + (s:ℂ) * (R:ℂ) * Complex.exp (2 * π * I * ((0:ℝ):ℂ)))
    norm_num
  have hHne : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, H s t ≠ 0 := fun s _ t _ => hmne _
  -- lift at `s = 0`: the constant loop `m a`
  have hma : m a ≠ 0 := hmne a
  set L₀ : ℝ → ℂ := fun _ => Complex.log (m a) with hL₀def
  have hL₀cont : ContinuousOn L₀ (Icc 0 1) := continuousOn_const
  have hL₀e : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₀ t) = H 0 t - 0 := by
    intro t _
    show Complex.exp (Complex.log (m a)) = m (a + (0:ℂ) * (R:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) - 0
    rw [Complex.exp_log hma]
    norm_num
  -- lift at `s = 1`: the loop `R exp(2π I t)`, with change `2π I`
  have hRexp : Complex.exp ((Real.log R : ℝ) : ℂ) = (R : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hR0]
  set L₁ : ℝ → ℂ := fun t => (Real.log R : ℂ) + 2 * π * I * (t : ℂ) with hL₁def
  have hL₁cont : ContinuousOn L₁ (Icc 0 1) := by
    apply Continuous.continuousOn
    fun_prop
  have hL₁e : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₁ t) = H 1 t - 0 := by
    intro t _
    show Complex.exp ((Real.log R : ℂ) + 2 * π * I * (t : ℂ)) =
      m (a + (1:ℂ) * (R:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) - 0
    rw [Complex.exp_add, hRexp]
    have h1 : (a + (1:ℂ) * (R:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) =
        a + (R:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) := by ring_nf
    rw [h1, hmcircle t]
    ring
  have hkey := lift_change_eq_of_homotopy hHcont hHper hHne hL₀cont hL₁cont hL₀e hL₁e
  have hL₀diff : L₀ 1 - L₀ 0 = 0 := by
    show Complex.log (m a) - Complex.log (m a) = 0
    ring
  have hL₁diff : L₁ 1 - L₁ 0 = 2 * π * I := by
    show ((Real.log R : ℂ) + 2 * π * I * ((1:ℝ):ℂ)) -
      ((Real.log R : ℂ) + 2 * π * I * ((0:ℝ):ℂ)) = 2 * π * I
    norm_num
  rw [hL₀diff, hL₁diff] at hkey
  have hπne : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hcontra : (2:ℂ) * π * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hπne) Complex.I_ne_zero
  exact hcontra hkey.symm

/-- General topology helper: a continuous injection on a compact set has a continuous inverse
on the image (compact-to-Hausdorff). -/
theorem iod_continuousOn_invFunOn_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [Nonempty X]
    {K : Set X} (hK : IsCompact K) {f : X → Y} (hc : ContinuousOn f K) (hi : InjOn f K) :
    ContinuousOn (Function.invFunOn f K) (f '' K) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨f '' (K ∩ t), (hK.inter_right ht).image_of_continuousOn (hc.mono inter_subset_left)
    |>.isClosed, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_preimage, mem_image]
  constructor
  · rintro ⟨hxy, x, hx, rfl⟩
    have heq : invFunOn f K (f x) = x := hi.leftInvOn_invFunOn hx
    rw [heq] at hxy
    exact ⟨⟨x, ⟨hx, hxy⟩, rfl⟩, x, hx, rfl⟩
  · rintro ⟨⟨x, ⟨hxK, hxt⟩, rfl⟩, x', hx'K, hx'eq⟩
    have hxx' : x = x' := hi hxK hx'K hx'eq.symm
    have heq : invFunOn f K (f x') = x' := hi.leftInvOn_invFunOn hx'K
    rw [← hx'eq, heq, ← hxx']
    exact ⟨hxt, x, hxK, rfl⟩

/-- A continuous nonvanishing function on a closed ball has a continuous logarithm there
(the closed ball is simply connected and locally path connected, being convex). -/
theorem iod_exists_log_on_closedBall {c : ℂ} {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hgc : ContinuousOn g (closedBall c r)) (hgne : ∀ x ∈ closedBall c r, g x ≠ 0) :
    ∃ L : ℂ → ℂ, ContinuousOn L (closedBall c r) ∧
      ∀ x ∈ closedBall c r, Complex.exp (L x) = g x := by
  classical
  have hconv : Convex ℝ (closedBall c r) := convex_closedBall c r
  have hne : (closedBall c r).Nonempty := ⟨c, mem_closedBall_self hr.le⟩
  haveI := hconv.contractibleSpace hne
  haveI : SimplyConnectedSpace ↥(closedBall c r) := SimplyConnectedSpace.ofContractible _
  haveI : LocallyPathConnectedSpace ↥(closedBall c r) := hconv.locallyPathConnectedSpace
  set A := ↥(closedBall c r)
  set a₀ : A := ⟨c, mem_closedBall_self hr.le⟩ with ha₀def
  have hgca0 : g a₀.1 ≠ 0 := hgne a₀.1 a₀.2
  set e₀ : ℂ := Complex.log (g a₀.1) with he₀def
  have hgcont : Continuous (fun x : A => g x.1) := hgc.restrict
  set fmap : C(A, ℂ) := ⟨fun x => g x.1, hgcont⟩ with hfmapdef
  have he : Complex.exp e₀ = fmap a₀ := Complex.exp_log hgca0
  have hs : ∀ x : A, fmap x ∈ ({0}ᶜ : Set ℂ) := fun x => hgne x.1 x.2
  obtain ⟨F, ⟨hFa₀, hFexp⟩, -⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts isCoveringMapOn_exp fmap he hs
  set L : ℂ → ℂ := fun z => if h : z ∈ closedBall c r then F ⟨z, h⟩ else 0 with hLdef
  have hLrestrict : (closedBall c r).domRestrict L = fun x : A => F x := by
    funext x
    show L x.1 = F x
    rw [hLdef]
    simp only [dif_pos x.2]
  refine ⟨L, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, hLrestrict]
    exact F.continuous
  · intro x hx
    have hLx : L x = F ⟨x, hx⟩ := dif_pos hx
    rw [hLx]
    have := congrFun hFexp ⟨x, hx⟩
    simpa [fmap] using this

/-- A continuous logarithm of `y - a` on the image of a closed ball under an injective
continuous map, built by transporting `iod_exists_log_on_closedBall` through the continuous
inverse `iod_continuousOn_invFunOn_of_isCompact` supplies. -/
theorem iod_exists_continuousOn_log_of_image_closedBall {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn f (closedBall c r)) (hi : InjOn f (closedBall c r))
    {a : ℂ} (ha : a ∉ f '' closedBall c r) :
    ∃ θ : ℂ → ℂ, ContinuousOn θ (f '' closedBall c r) ∧
      ∀ y ∈ f '' closedBall c r, Complex.exp (θ y) = y - a := by
  have hgc : ContinuousOn (fun x => f x - a) (closedBall c r) := hc.sub continuousOn_const
  have hgne : ∀ x ∈ closedBall c r, f x - a ≠ 0 := by
    intro x hx hcontra
    apply ha
    have hfx : f x = a := by linear_combination hcontra
    exact ⟨x, hx, hfx⟩
  obtain ⟨L, hLc, hLexp⟩ := iod_exists_log_on_closedBall hr hgc hgne
  have hK : IsCompact (closedBall c r) := isCompact_closedBall c r
  have hinvc : ContinuousOn (invFunOn f (closedBall c r)) (f '' closedBall c r) :=
    iod_continuousOn_invFunOn_of_isCompact hK hc hi
  have hinvmem : ∀ y ∈ f '' closedBall c r, invFunOn f (closedBall c r) y ∈ closedBall c r :=
    fun y hy => invFunOn_mem hy
  have hinveq : ∀ y ∈ f '' closedBall c r, f (invFunOn f (closedBall c r) y) = y :=
    fun y hy => invFunOn_eq hy
  refine ⟨L ∘ invFunOn f (closedBall c r), ?_, ?_⟩
  · exact hLc.comp hinvc hinvmem
  · intro y hy
    show Complex.exp (L (invFunOn f (closedBall c r) y)) = y - a
    rw [hLexp _ (hinvmem y hy), hinveq y hy]

/-- **W2.** A topological closed disc does not separate the plane: the complement of the
continuous injective image of a closed ball is connected. The unbounded exterior
`{R < ‖z‖}` sits inside a single component `E`; any other component of `Kᶜ` would have to
avoid that exterior (hence be bounded), giving a continuous logarithm of `z - a` on `K` and
contradicting W1. -/
theorem isConnected_compl_image_closedBall {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn f (closedBall c r)) (hi : Set.InjOn f (closedBall c r)) :
    IsConnected (f '' Metric.closedBall c r)ᶜ := by
  set K := f '' closedBall c r with hKdef
  have hK : IsCompact K := (isCompact_closedBall c r).image_of_continuousOn hc
  have hKbdd : Bornology.IsBounded K := hK.isBounded
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp hKbdd
  have hR0 : 0 ≤ R := by
    have hp : f c ∈ K := mem_image_of_mem f (mem_closedBall_self hr.le)
    have hpR := hR hp
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hpR
    exact le_trans (norm_nonneg _) hpR
  set z₀ : ℂ := ((R + 1 : ℝ) : ℂ) with hz₀def
  have hz₀norm : R < ‖z₀‖ := by
    rw [hz₀def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hExtSub : {z : ℂ | R < ‖z‖} ⊆ Kᶜ := by
    intro z hz hzK
    have hzR : dist z (0:ℂ) ≤ R := hR hzK
    rw [dist_eq_norm, sub_zero] at hzR
    simp only [mem_setOf_eq] at hz
    exact absurd hzR (not_le.mpr hz)
  have hExtPre : IsPreconnected {z : ℂ | R < ‖z‖} := isPreconnected_setOf_lt_norm hR0
  have hz₀mem : z₀ ∈ Kᶜ := hExtSub hz₀norm
  set E := connectedComponentIn Kᶜ z₀ with hEdef
  have hExtE : {z : ℂ | R < ‖z‖} ⊆ E :=
    hExtPre.subset_connectedComponentIn hz₀norm hExtSub
  have hsub : Kᶜ ⊆ E := by
    intro a ha
    by_contra haE
    have haCa : a ∈ connectedComponentIn Kᶜ a := mem_connectedComponentIn ha
    have hCaBdd : connectedComponentIn Kᶜ a ⊆ closedBall (0:ℂ) R := by
      intro z hz
      by_contra hzout
      rw [mem_closedBall, dist_eq_norm, sub_zero, not_le] at hzout
      have hzE : z ∈ E := hExtE hzout
      have h1 : connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ z :=
        connectedComponentIn_eq hz
      have h2 : E = connectedComponentIn Kᶜ z :=
        connectedComponentIn_eq hzE
      apply haE
      rw [h2, ← h1]
      exact haCa
    have hCaBounded : Bornology.IsBounded (connectedComponentIn Kᶜ a) :=
      isBounded_closedBall.subset hCaBdd
    have haK : a ∉ K := ha
    refine (not_exists_continuousOn_log_of_isBounded_connectedComponentIn hK haK hCaBounded) ?_
    exact iod_exists_continuousOn_log_of_image_closedBall hr hc hi ha
  have hKcE : Kᶜ = E := Subset.antisymm hsub (connectedComponentIn_subset Kᶜ z₀)
  refine ⟨⟨z₀, hz₀mem⟩, ?_⟩
  rw [hKcE]
  exact isPreconnected_connectedComponentIn

/-- The image of a circle under a continuous injective map is a Jordan curve. -/
theorem iod_isJordanCurve_image_sphere {f : ℂ → ℂ} {p : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn f (Metric.sphere p r)) (hi : Set.InjOn f (Metric.sphere p r)) :
    IsJordanCurve (toExt (f '' Metric.sphere p r)) := by
  have hparam_mem : ∀ ζ : Circle, p + (r : ℂ) * (ζ : ℂ) ∈ Metric.sphere p r := by
    intro ζ
    rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hparam_cont : Continuous (fun ζ : Circle => p + (r : ℂ) * (ζ : ℂ)) :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  refine ⟨fun ζ : Circle => ((f (p + (r : ℂ) * (ζ : ℂ)) : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact OnePoint.continuous_coe.comp (hc.comp_continuous hparam_cont hparam_mem)
  · intro ζ₁ ζ₂ heq
    have heq' : f (p + (r : ℂ) * (ζ₁ : ℂ)) = f (p + (r : ℂ) * (ζ₂ : ℂ)) :=
      OnePoint.coe_injective heq
    have hpt : p + (r : ℂ) * (ζ₁ : ℂ) = p + (r : ℂ) * (ζ₂ : ℂ) :=
      hi (hparam_mem ζ₁) (hparam_mem ζ₂) heq'
    have hmulEq : (r : ℂ) * (ζ₁ : ℂ) = (r : ℂ) * (ζ₂ : ℂ) := add_left_cancel hpt
    have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact Circle.coe_injective (mul_left_cancel₀ hrne hmulEq)
  · unfold toExt
    ext w
    simp only [mem_range, mem_image]
    constructor
    · rintro ⟨ζ, rfl⟩
      exact ⟨f (p + (r : ℂ) * (ζ : ℂ)), ⟨p + (r : ℂ) * (ζ : ℂ), hparam_mem ζ, rfl⟩, rfl⟩
    · rintro ⟨z', ⟨x, hx, rfl⟩, rfl⟩
      have hrne : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      set ζ0 : ℂ := (x - p) / r with hζ0def
      have hdist : ‖x - p‖ = r := by
        have := hx
        rwa [Metric.mem_sphere, dist_eq_norm] at this
      have hζ0norm : ‖ζ0‖ = 1 := by
        rw [hζ0def, norm_div, hdist, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
          div_self hr.ne']
      refine ⟨⟨ζ0, mem_sphere_zero_iff_norm.2 hζ0norm⟩, ?_⟩
      have hxeq : p + (r : ℂ) * ζ0 = x := by
        rw [hζ0def, mul_div_cancel₀ _ hrne]
        ring
      show ((f (p + (r:ℂ) * (ζ0:ℂ)) : ℂ) : ExtPlane) = ((f x : ℂ) : ExtPlane)
      rw [hxeq]

/-- **Invariance of domain.** A continuous injective map on an open set has open image. -/
theorem isOpen_image_of_continuousOn_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hc : ContinuousOn f U) (hi : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro w ⟨p, hpU, rfl⟩
  obtain ⟨ε, hε0, hεU⟩ := Metric.isOpen_iff.mp hU p hpU
  set r : ℝ := ε / 2 with hrdef
  have hr0 : 0 < r := by positivity
  have hrε : r < ε := by rw [hrdef]; linarith
  have hclosedU : Metric.closedBall p r ⊆ U :=
    (Metric.closedBall_subset_ball hrε).trans hεU
  have hballU : Metric.ball p r ⊆ U := (Metric.ball_subset_closedBall).trans hclosedU
  have hsphereU : Metric.sphere p r ⊆ U := by
    rw [← Metric.closedBall_diff_ball]
    exact (Set.diff_subset).trans hclosedU
  have hcC : ContinuousOn f (Metric.sphere p r) := hc.mono hsphereU
  have hiC : Set.InjOn f (Metric.sphere p r) := hi.mono hsphereU
  have hJ : IsJordanCurve (toExt (f '' Metric.sphere p r)) :=
    iod_isJordanCurve_image_sphere hr0 hcC hiC
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAbdd, hBunbdd⟩ :=
    jordan_curve_theorem_complex_bounded hJ
  set C : Set ℂ := f '' Metric.sphere p r with hCdef
  set K : Set ℂ := f '' Metric.closedBall p r with hKdef
  have hKeq : K = f '' Metric.ball p r ∪ C := by
    rw [hKdef, hCdef, ← Metric.ball_union_sphere, Set.image_union]
  have hballdisjC : Disjoint (f '' Metric.ball p r) C := by
    rw [hCdef]
    rw [Set.disjoint_left]
    rintro w ⟨x, hxball, rfl⟩ ⟨y, hysphere, hfxy⟩
    have hxU : x ∈ Metric.closedBall p r := Metric.ball_subset_closedBall hxball
    have hyU : y ∈ Metric.closedBall p r := Metric.sphere_subset_closedBall hysphere
    have hcC' : ContinuousOn f (Metric.closedBall p r) := hc.mono hclosedU
    have hiC' : Set.InjOn f (Metric.closedBall p r) := hi.mono hclosedU
    have hxy : x = y := hiC' hxU hyU hfxy.symm
    rw [hxy] at hxball
    have hyr : dist y p = r := hysphere
    have hylt : dist y p < r := hxball
    linarith
  have hballsub : f '' Metric.ball p r ⊆ A ∪ B := by
    intro z hz
    have hzC : z ∉ C := fun h => Set.disjoint_left.1 hballdisjC hz h
    have : z ∈ A ∪ B ∪ C := huniv ▸ mem_univ z
    rcases this with h | h
    · exact h
    · exact absurd h hzC
  have hballconn : IsConnected (f '' Metric.ball p r) :=
    (isConnected_ball hr0).image f (hc.mono hballU)
  have hballcase : f '' Metric.ball p r ⊆ A ∨ f '' Metric.ball p r ⊆ B := by
    apply (isPreconnected_iff_subset_of_disjoint.1 hballconn.isPreconnected) A B hA hB hballsub
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzA, hzB⟩
    exact Set.disjoint_left.1 hAB hzA hzB
  -- If the image of the ball sat inside the OTHER piece `Q`, then `Q` is disjoint from `K` and
  -- `Kᶜ = P ∪ (Q \ K)` splits `Kᶜ` into two disjoint nonempty open pieces, contradicting W2.
  have hKcompact : IsCompact K := by
    rw [hKdef]; exact (isCompact_closedBall p r).image_of_continuousOn (hc.mono hclosedU)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hKconn : IsConnected Kᶜ := by
    rw [hKdef]; exact isConnected_compl_image_closedBall hr0 (hc.mono hclosedU) (hi.mono hclosedU)
  -- Shared facts about any labelling `P` (containing the ball image) / `Q` (the other piece):
  -- `Q` is always disjoint from `K`, and `Kᶜ` is always covered by `P ∪ (Q \ K)`.
  have hQdisjK : ∀ P Q : Set ℂ, Disjoint P Q → Disjoint Q C →
      f '' Metric.ball p r ⊆ P → Disjoint Q K := by
    intro P Q hPQ hQC hballP
    rw [hKeq]
    refine Set.disjoint_union_right.2 ⟨?_, hQC⟩
    exact Set.disjoint_left.2 fun x hxQ hxball => Set.disjoint_left.1 hPQ (hballP hxball) hxQ
  have hcover : ∀ P Q : Set ℂ, P ∪ Q = A ∪ B → Disjoint Q K → Kᶜ ⊆ P ∪ (Q \ K) := by
    intro P Q hPQunion hQK z hzKc
    have hz : z ∈ A ∪ B ∪ C := huniv ▸ mem_univ z
    have hzC : z ∉ C := fun hzC' => hzKc (by rw [hKeq]; exact Or.inr hzC')
    have hzPQ : z ∈ P ∪ Q := by
      rw [hPQunion]
      rcases hz with h | h
      · exact h
      · exact absurd h hzC
    rcases hzPQ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hzKc⟩
  -- Case `f '' ball p r ⊆ B` is impossible: it forces two disjoint nonempty open pieces
  -- covering `Kᶜ`, contradicting the connectedness of `Kᶜ` given by the W2 stub.
  have hnotB : ¬ f '' Metric.ball p r ⊆ B := by
    intro hballB
    have hAdisjK : Disjoint A K := hQdisjK B A hAB.symm hAC hballB
    have hAKc : A ⊆ Kᶜ := fun x hxA => Set.disjoint_left.1 hAdisjK hxA
    have hBnotK : ¬ B ⊆ K := fun hBK => hBunbdd (hKcompact.isBounded.subset hBK)
    obtain ⟨b, hbB, hbK⟩ : (B \ K).Nonempty := Set.not_subset.1 hBnotK
    have hcov : Kᶜ ⊆ B ∪ (A \ K) := hcover B A (by rw [Set.union_comm]) hAdisjK
    have hempty : Kᶜ ∩ (B ∩ (A \ K)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hzB, hzA, -⟩
      exact Set.disjoint_left.1 hAB hzA hzB
    rcases (isPreconnected_iff_subset_of_disjoint.1 hKconn.isPreconnected) B (A \ K) hB
      (hA.sdiff hKclosed) hcov hempty with h | h
    · obtain ⟨a, haA⟩ := hAc.nonempty
      exact Set.disjoint_left.1 hAB haA (h (hAKc haA))
    · have hbKc : b ∈ Kᶜ := hbK
      exact Set.disjoint_left.1 hAB (h hbKc).1 hbB
  -- So `f '' ball p r ⊆ A`, and then `A ⊆ K`, hence (missing `C`) `A ⊆ f '' ball p r`.
  have hballA : f '' Metric.ball p r ⊆ A := hballcase.resolve_right hnotB
  have hBdisjK : Disjoint B K := hQdisjK A B hAB hBC hballA
  have hBKc : B ⊆ Kᶜ := fun x hxB => Set.disjoint_left.1 hBdisjK hxB
  have hcovA : Kᶜ ⊆ A ∪ (B \ K) := hcover A B rfl hBdisjK
  have hemptyA : Kᶜ ∩ (A ∩ (B \ K)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzA, hzB, -⟩
    exact Set.disjoint_left.1 hAB hzA hzB
  have hAK : A ⊆ K := by
    rcases (isPreconnected_iff_subset_of_disjoint.1 hKconn.isPreconnected) A (B \ K) hA
      (hB.sdiff hKclosed) hcovA hemptyA with h | h
    · exfalso
      obtain ⟨bb, hbb⟩ := hBc.nonempty
      exact Set.disjoint_left.1 hAB (h (hBKc hbb)) hbb
    · intro z hzA
      by_contra hzK
      have hzKc : z ∈ Kᶜ := hzK
      exact Set.disjoint_left.1 hAB hzA (h hzKc).1
  have hAballA : A ⊆ f '' Metric.ball p r := by
    intro z hzA
    have hzK := hAK hzA
    rw [hKeq] at hzK
    rcases hzK with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hAC hzA)
  have hAeq : f '' Metric.ball p r = A := Set.Subset.antisymm hballA hAballA
  have hmemA : f p ∈ A := hAeq ▸ ⟨p, mem_ball_self hr0, rfl⟩
  have hAsubU : A ⊆ f '' U := hAeq ▸ (Set.image_mono hballU)
  exact Filter.mem_of_superset (hA.mem_nhds hmemA) hAsubU

/-- The `_of_subset` form: restrict the hypotheses to a smaller open subset. -/
theorem isOpen_image_of_continuousOn_injOn_of_subset {U V : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hc : ContinuousOn f U) (hi : Set.InjOn f U) (hV : V ⊆ U) (hVo : IsOpen V) : IsOpen (f '' V) :=
  isOpen_image_of_continuousOn_injOn hVo (hc.mono hV) (hi.mono hV)

end LiZhongQC
