import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# §31 有限型 Riemann 曲面 — Riemann surfaces of finite type

* §31.1 surfaces of finite type `(g, n, m)`: a compact surface minus `n` punctures and `m`
  holes; punctures vs. holes; the Schottky double `S^d`; the exceptional types; the double of a
  non-exceptional surface has hyperbolic universal covering
                                      — `FiniteTypeStructure`, `IsSchottkyDouble`, `IsExceptionalType`
* §31.2 admissible quadratic differentials `Q̃(S₀)` (simple poles at punctures, real on the
  boundary curves); the symmetric extension to `S^d`; (31.1), the decomposition `Ω ⊕ Ω'`; Theorem
  31.1: `dim_ℝ Q̃(S₀) = 6g - 6 + 2n + 3m` (31.2)
                                      — `admissibleQDSpace`, `thm31_1_admissibleQD_finrank`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

/-! ## §31.1 Basic notions -/

/-- A closed Jordan disc in a Riemann surface with smooth (`C^∞`) boundary: the closure of a bounded
Jordan domain in a chart, whose boundary is a smooth regular Jordan curve.

**Correction (2026-09-27).**  The boundary curve was only `C¹`, too weak for the boundary conditions of
`IsAdmissibleQD` read in charts (without Kellogg–Warschawski regularity the conformal collar map can have
unbounded derivative at a boundary point, and those conditions then cut a dimension off `Q̃(S₀)`); it is
now `C^∞`, the book's smooth boundary. -/
def IsClosedDiscIn {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (D : Set X) : Prop :=
  ∃ x : X, D ⊆ (chartAt ℂ x).source ∧ ∃ J : Set ℂ, IsJordanDomain J ∧ Bornology.IsBounded J ∧
    closure J ⊆ (chartAt ℂ x).target ∧ chartAt ℂ x '' D = closure J ∧
    ∃ c : ℝ → ℂ, ContDiff ℝ ∞ c ∧ (∀ t, deriv c t ≠ 0) ∧ (∀ t, c (t + 1) = c t) ∧
      InjOn c (Ico 0 1) ∧ c '' Ico 0 1 = frontier J

/-- **§31.1 (有限型曲面).**  `S` is a Riemann surface of type `(g, n, m)`: there are a closed
surface `X` of genus `g`, `n` points `P` and `m` pairwise disjoint closed discs `D j` (with smooth
boundary) such that `S` is conformally `X ∖ (P ∪ ⋃ D j)` (via the open holomorphic embedding `ι`).
The points of `P` are the punctures (穿孔点), the boundaries of the `D j` the holes (洞). -/
structure FiniteTypeStructure (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] (g n m : ℕ) where
  X : ClosedRS.{u}
  P : Finset X.carrier
  D : Fin m → Set X.carrier
  ι : S → X.carrier
  genus : HasGenus X.carrier g
  card_P : P.card = n
  disc : ∀ j, IsClosedDiscIn (D j)
  disjoint : Pairwise fun i j => Disjoint (D i) (D j)
  disjoint_P : ∀ j, Disjoint (D j) ↑P
  embedding : Topology.IsOpenEmbedding ι
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι
  range_ι : range ι = (↑P ∪ ⋃ j, D j)ᶜ

/-- `S` is a Riemann surface of type `(g, n, m)` (the type of `S` is determined by `S`). -/
def IsFiniteType (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] (g n m : ℕ) : Prop :=
  Nonempty (FiniteTypeStructure S g n m)

/-- §31.1 (例外型): the exceptional types
`(0,0,0), (0,1,0), (1,0,0), (0,2,0); (0,0,1), (0,1,1), (0,0,2)`: the surface or its Schottky double
does not have hyperbolic universal covering. -/
def IsExceptionalType (g n m : ℕ) : Prop :=
  (g, n, m) = (0, 0, 0) ∨ (g, n, m) = (0, 1, 0) ∨ (g, n, m) = (1, 0, 0) ∨ (g, n, m) = (0, 2, 0) ∨
    (g, n, m) = (0, 0, 1) ∨ (g, n, m) = (0, 1, 1) ∨ (g, n, m) = (0, 0, 2)

/-- The complement of a finite set of points of a Riemann surface, as an open subset (again a
Riemann surface). -/
def puncturedOpens {X : Type u} [TopologicalSpace X] [T2Space X] (P : Finset X) : TopologicalSpace.Opens X :=
  ⟨(↑P : Set X)ᶜ, P.finite_toSet.isClosed.isOpen_compl⟩

/-- An anti-conformal involution `J` of a Riemann surface. -/
def IsAnticonformalInvolution {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (J : X ≃ₜ X) : Prop :=
  (∀ p, J (J p) = p) ∧ ∀ x : X, DifferentiableOn ℂ (fun z => conj (localMapExpr J x z)) (localMapDomain J x)

/-- **§31.1 (Schottky 二倍面).**  `(Xd, J, ιd)` is a Schottky double `S^d` of the surface `S` of type
`(g, n, m)` with structure `F`: `Xd` is a closed surface of genus `2g + m - 1` with an anti-conformal
involution `J`, `ιd : S → Xd` is a holomorphic open embedding, `ιd(S)` and `J(ιd(S))` (the mirror
image) are disjoint, and `Xd` is `ιd(S) ∪ J(ιd(S))` together with the fixed curves of `J` (the
`m` boundary curves) and the `2n` punctures (images of `P` and their mirror images). -/
structure IsSchottkyDouble {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (Xd : ClosedRS.{u}) (J : Xd.carrier ≃ₜ Xd.carrier) (ιd : S → Xd.carrier)
    (Pd : Finset Xd.carrier) : Prop where
  genus : HasGenus Xd.carrier (2 * g + m - 1)
  involution : IsAnticonformalInvolution J
  embedding : Topology.IsOpenEmbedding ιd
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ιd
  disjoint : Disjoint (range ιd) (range (J ∘ ιd))
  card_Pd : Pd.card = 2 * n
  Pd_invariant : J '' ↑Pd = ↑Pd
  cover : range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ ↑Pd = univ
  fixed_curves : {x | J x = x} = frontier (range ιd) \ ↑Pd

-- exists_schottkyDouble (§31.1) is stated and proved in LiZhongQC/Lemmas/SchottkyTerminal.lean
-- (the concrete double, its complex atlas and its genus).

section s31hy_helpers

open Jacobians

/-- An injective function analytic on a punctured disc has no essential singularity at the centre: the image
of a small punctured disc misses a disc (open mapping at a point of the outer annulus), so `1/(g - w₀)` is bounded
and the singularity of `1/(g - w₀)` is removable. -/
theorem s31hy_injective_meromorphicAt {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : ∀ z ∈ ball z₀ r, z ≠ z₀ → AnalyticAt ℂ g z)
    (hinj : InjOn g (ball z₀ r \ {z₀})) : MeromorphicAt g z₀ := by
  set ρ : ℝ := r / 4 with hρ
  set δ : ℝ := r / 8 with hδ
  have hρ0 : 0 < ρ := by positivity
  have hδ0 : 0 < δ := by positivity
  set z1 : ℂ := z₀ + ((r / 2 : ℝ) : ℂ) with hz1
  have hz1d : ‖z1 - z₀‖ = r / 2 := by
    rw [hz1, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  -- the small ball around `z1` lies in the outer annulus
  have hball : ∀ z ∈ ball z1 δ, ρ < ‖z - z₀‖ ∧ ‖z - z₀‖ < r := by
    intro z hz
    rw [mem_ball_iff_norm] at hz
    have h1 : ‖z - z₀‖ ≤ ‖z - z1‖ + ‖z1 - z₀‖ := by
      calc ‖z - z₀‖ = ‖(z - z1) + (z1 - z₀)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖z1 - z₀‖ ≤ ‖z1 - z‖ + ‖z - z₀‖ := by
      calc ‖z1 - z₀‖ = ‖(z1 - z) + (z - z₀)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have e : ‖z1 - z‖ = ‖z - z1‖ := norm_sub_rev _ _
    constructor <;> linarith
  have hanal1 : AnalyticOnNhd ℂ g (ball z1 δ) := fun z hz => by
    have := hball z hz
    refine hg z ?_ ?_
    · rw [mem_ball_iff_norm]; exact this.2
    · intro h; rw [h, sub_self, norm_zero] at this; linarith [this.1]
  have hinj1 : InjOn g (ball z1 δ) := fun a ha b hb hab =>
    hinj ⟨by rw [mem_ball_iff_norm]; exact (hball a ha).2, fun h => by
      have := (hball a ha).1; rw [mem_singleton_iff.1 h, sub_self, norm_zero] at this; linarith⟩
      ⟨by rw [mem_ball_iff_norm]; exact (hball b hb).2, fun h => by
      have := (hball b hb).1; rw [mem_singleton_iff.1 h, sub_self, norm_zero] at this; linarith⟩ hab
  have hz1mem : z1 ∈ ball z1 δ := mem_ball_self hδ0
  -- the image of the small ball is open
  have hopen : IsOpen (g '' ball z1 δ) := by
    rcases hanal1.is_constant_or_isOpen (convex_ball z1 δ).isPreconnected with ⟨w, hw⟩ | h
    · exfalso
      set z2 : ℂ := z1 + ((δ / 2 : ℝ) : ℂ) with hz2
      have hz2mem : z2 ∈ ball z1 δ := by
        rw [mem_ball_iff_norm, hz2, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        linarith
      have := hinj1 hz1mem hz2mem ((hw z1 hz1mem).trans (hw z2 hz2mem).symm)
      have h0 : ((δ / 2 : ℝ) : ℂ) = 0 := by
        have : z1 = z1 + ((δ / 2 : ℝ) : ℂ) := this
        linear_combination -this
      have : δ / 2 = 0 := by exact_mod_cast h0
      linarith
    · exact h _ subset_rfl isOpen_ball
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hopen (g z1) ⟨z1, hz1mem, rfl⟩
  -- the punctured small disc is mapped away from `ball (g z1) ε`
  have hfar : ∀ z ∈ ball z₀ ρ, z ≠ z₀ → ε ≤ ‖g z - g z1‖ := by
    intro z hz hzne
    by_contra hlt
    push_neg at hlt
    have hmem : g z ∈ ball (g z1) ε := by rw [mem_ball_iff_norm]; exact hlt
    obtain ⟨z', hz', hz'e⟩ := hεsub hmem
    have hzr : z ∈ ball z₀ r \ {z₀} := ⟨by
      rw [mem_ball_iff_norm] at hz ⊢; linarith, hzne⟩
    have hz'r : z' ∈ ball z₀ r \ {z₀} := ⟨by
      rw [mem_ball_iff_norm]; exact (hball z' hz').2, fun h => by
      have := (hball z' hz').1; rw [mem_singleton_iff.1 h, sub_self, norm_zero] at this; linarith⟩
    have := hinj hz'r hzr hz'e
    rw [← this] at hz
    rw [mem_ball_iff_norm] at hz
    linarith [(hball z' hz').1]
  -- `k = 1/(g - g z1)` is bounded and analytic on the punctured disc
  set k : ℂ → ℂ := fun z => (g z - g z1)⁻¹ with hk
  have hkd : DifferentiableOn ℂ k (ball z₀ ρ \ {z₀}) := by
    intro z hz
    have hzr : z ∈ ball z₀ r := by
      have := hz.1; rw [mem_ball_iff_norm] at this ⊢; linarith
    have ha : AnalyticAt ℂ g z := hg z hzr hz.2
    have hne : g z - g z1 ≠ 0 := by
      intro h0
      have := hfar z hz.1 hz.2
      rw [h0, norm_zero] at this
      linarith
    exact (((ha.sub analyticAt_const).inv hne).differentiableAt).differentiableWithinAt
  have hkb : BddAbove (norm ∘ k '' (ball z₀ ρ \ {z₀})) := by
    refine ⟨ε⁻¹, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    show ‖k z‖ ≤ ε⁻¹
    rw [hk]
    simp only
    rw [norm_inv]
    exact inv_anti₀ hε (hfar z hz.1 hz.2)
  have hrem := Complex.differentiableOn_update_limUnder_of_bddAbove (isOpen_ball.mem_nhds (mem_ball_self hρ0)) hkd hkb
  set k' : ℂ → ℂ := Function.update k z₀ (limUnder (𝓝[≠] z₀) k) with hk'
  have hk'an : AnalyticAt ℂ k' z₀ := hrem.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hρ0))
  have hmer : MeromorphicAt (fun z => g z1 + (k' z)⁻¹) z₀ :=
    (MeromorphicAt.const (g z1) z₀).add hk'an.meromorphicAt.inv
  refine hmer.congr ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds (mem_ball_self hρ0))] with z hzne hzb
  have hzne' : z ≠ z₀ := mem_compl_singleton_iff.1 hzne
  show g z1 + (k' z)⁻¹ = g z
  rw [hk', Function.update_of_ne hzne', hk]
  simp only
  rw [inv_inv]
  ring

/-- A holomorphic map between compact Riemann surfaces with a regular value of fibre size `1` is a bijection
and an open map (the proof of `Jacobians.degreeOne_homeo`, with the bijectivity exposed). -/
theorem s31hy_bijective_of_fibre {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (F : X → Y) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hnc : ¬ IsConstantMap F) {y₀ : Y}
    (hy₀ : y₀ ∉ Jacobians.Discharge.Manifold.criticalValuesGeneral F) (h1 : (F ⁻¹' {y₀}).ncard = 1) :
    Function.Bijective F ∧ IsOpenMap F := by
  classical
  have hnc' : ¬ ∃ y₀ : Y, ∀ x, F x = y₀ := hnc
  have hsurj : Function.Surjective F := surjective_of_nonconstant F hF hnc'
  have hopen : IsOpenMap F := isOpenMap_of_nonconstant F hF hnc'
  set C : Set Y := Jacobians.Discharge.Manifold.criticalValuesGeneral F with hC
  have hCfin : C.Finite := Jacobians.Discharge.Manifold.criticalValues_finite_general F hF hnc
  have hdeg : degreeFiber F hF = 1 := by
    obtain ⟨w, hwval⟩ :=
      Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq F hF hnc hy₀
    have hwcard : degreeFiber F hF = w.card :=
      degreeFiber_eq_card_of_regularWitness F hF hnc w
    have hcardeq : w.card = (F ⁻¹' {w.toWitness.value}).ncard := w.toWitness.card_eq_ncard
    rw [hwval] at hcardeq
    rw [hwcard, hcardeq, h1]
  have hsingleton : ∀ y ∉ C, ∃ p, F ⁻¹' {y} = {p} := by
    intro y hy
    obtain ⟨w, hwval⟩ :=
      Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq F hF hnc hy
    have hwcard : degreeFiber F hF = w.card :=
      degreeFiber_eq_card_of_regularWitness F hF hnc w
    have hcard1 : (F ⁻¹' {y}).ncard = 1 := by
      have hcardeq : w.card = (F ⁻¹' {w.toWitness.value}).ncard :=
        w.toWitness.card_eq_ncard
      rw [hwval] at hcardeq
      have : (F ⁻¹' {y}).ncard = w.card := hcardeq.symm
      rw [this, ← hwcard, hdeg]
    exact Set.ncard_eq_one.mp hcard1
  have hinj : Function.Injective F := by
    intro a b hab
    by_contra hne
    obtain ⟨U, V, hUopen, hVopen, haU, hbV, hUV⟩ := t2_separation hne
    have hcU : F a ∈ F '' U := ⟨a, haU, rfl⟩
    have hcV : F a ∈ F '' V := ⟨b, hbV, hab.symm⟩
    have hWopen : IsOpen (F '' U ∩ F '' V) := (hopen U hUopen).inter (hopen V hVopen)
    have hWne : (F '' U ∩ F '' V).Nonempty := ⟨F a, hcU, hcV⟩
    obtain ⟨y, ⟨⟨u, huU, hFu⟩, ⟨v, hvV, hFv⟩⟩, hyC⟩ :=
      exists_mem_open_notMem_finite hWopen hWne hCfin
    obtain ⟨p, hp⟩ := hsingleton y hyC
    have hup : u = p := by
      have : u ∈ F ⁻¹' {y} := hFu
      rw [hp] at this; exact this
    have hvp : v = p := by
      have : v ∈ F ⁻¹' {y} := hFv
      rw [hp] at this; exact this
    have huv : u = v := hup.trans hvp.symm
    exact (hUV.ne_of_mem huU (huv ▸ hvV)) rfl
  exact ⟨⟨hinj, hsurj⟩, hopen⟩

/-- A closed surface minus finitely many points that carries an injective holomorphic function whose
image misses only finitely many complex numbers is the sphere, and the number of punctures is
`1 +` the number of missed values. -/
theorem s31hy_sphere_of_injective {X : ClosedRS.{u}} (P : Finset X.carrier)
    (ψ : puncturedOpens P → ℂ) (hψ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ) (hinj : Function.Injective ψ)
    (hfin : {w : ℂ | w ∉ range ψ}.Finite) :
    Nonempty (X.carrier ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      P.card = 1 + {w : ℂ | w ∉ range ψ}.ncard := by
  classical
  have hψc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ψ := k22u_mdifferentiable_contMDiff hψ
  set f : X.carrier → ℂ := fun x => if h : x ∈ (↑P : Set X.carrier)ᶜ then ψ ⟨x, h⟩ else 0 with hfdef
  have hpo : ∀ x : X.carrier, x ∈ puncturedOpens P ↔ x ∉ P := fun x => by
    show x ∈ (↑P : Set X.carrier)ᶜ ↔ x ∉ P
    simp
  have hf_on : ∀ y : puncturedOpens P, f y = ψ y := fun y => by
    have hy' : (y : X.carrier) ∈ (↑P : Set X.carrier)ᶜ := y.2
    simp only [hfdef]
    rw [dif_pos hy']
  have hfsm : ∀ x : X.carrier, x ∉ P → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := fun x hx => by
    have hx' : x ∈ (↑P : Set X.carrier)ᶜ := by simpa using hx
    have h1 : (fun y : puncturedOpens P => f y) = ψ := funext hf_on
    have := hψc ⟨x, hx'⟩
    rw [← h1] at this
    exact (contMDiffAt_subtype_iff (U := puncturedOpens P) (f := f) (x := ⟨x, hx'⟩)).1 this
  -- analyticity of chart pullbacks away from the punctures
  have hanal : ∀ (x : X.carrier) (z : ℂ), z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∉ P →
      AnalyticAt ℂ (f ∘ (chartAt ℂ x).symm) z := by
    intro x z hz hzP
    have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ x).symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hz
    have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (f ∘ (chartAt ℂ x).symm) z :=
      ContMDiffAt.comp z (hfsm _ hzP) hsymm
    exact (contMDiffAt_iff_contDiffAt.1 hcomp).analyticAt
  have hmer : IsMeromorphic X.carrier f := by
    intro x
    have hz := (chartAt (H := ℂ) x).map_source (mem_chart_source ℂ x)
    have hsy : (chartAt (H := ℂ) x).symm ((chartAt (H := ℂ) x) x) = x :=
      (chartAt (H := ℂ) x).left_inv (mem_chart_source ℂ x)
    by_cases hx : x ∈ P
    · -- a puncture: the pullback is injective and analytic on a punctured disc
      set e := chartAt (H := ℂ) x with he
      have hU : ((↑(P.erase x) : Set X.carrier))ᶜ ∈ 𝓝 x :=
        (P.erase x).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      have hnh : e.symm ⁻¹' ((↑(P.erase x) : Set X.carrier))ᶜ ∩ e.target ∈ 𝓝 (e x) := by
        refine Filter.inter_mem ?_ (e.open_target.mem_nhds hz)
        exact (e.continuousAt_symm hz).preimage_mem_nhds (by rw [hsy]; exact hU)
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hnh
      have hnotP : ∀ z ∈ ball (e x) r, z ≠ e x → z ∈ e.target ∧ e.symm z ∉ P := by
        intro z hzb hzne
        obtain ⟨h1, h2⟩ := hball hzb
        refine ⟨h2, fun hzP => ?_⟩
        have hne : e.symm z ≠ x := fun h => hzne (e.symm.injOn h2 hz (by rw [h, hsy]))
        exact h1 (by simp [Finset.mem_erase, hne, hzP])
      refine s31hy_injective_meromorphicAt hr (fun z hzb hzne => ?_) ?_
      · obtain ⟨h1, h2⟩ := hnotP z hzb hzne
        exact hanal x z h1 h2
      · intro a ha b hb hab
        obtain ⟨ha1, ha2⟩ := hnotP a ha.1 ha.2
        obtain ⟨hb1, hb2⟩ := hnotP b hb.1 hb.2
        have h1 := hf_on ⟨e.symm a, (hpo _).2 ha2⟩
        have h2 := hf_on ⟨e.symm b, (hpo _).2 hb2⟩
        have hab' : ψ ⟨e.symm a, (hpo _).2 ha2⟩ = ψ ⟨e.symm b, (hpo _).2 hb2⟩ := by
          rw [← h1, ← h2]; exact hab
        have := congrArg Subtype.val (hinj hab')
        exact e.symm.injOn ha1 hb1 this
    · exact (hanal x _ hz (by rw [hsy]; exact hx)).meromorphicAt
  have : Nonempty X.carrier := ConnectedSpace.toNonempty
  set fM : MeromorphicFunction X.carrier := ⟨f, hmer⟩ with hfM
  letI : ChartedSpace ℂ RiemannSphere := Jacobians.RiemannSphere.instChartedSpaceComplex
  set F : X.carrier → RiemannSphere := fM.toRiemannSphere with hFdef
  have hFsm : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F := fM.contMDiff_toRiemannSphere
  haveI : Infinite X.carrier := Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  have horder : ∀ x : X.carrier, x ∉ P → 0 ≤ fM.orderAtPoint x := by
    intro x hx
    have hz := (chartAt (H := ℂ) x).map_source (mem_chart_source ℂ x)
    have hsy : (chartAt (H := ℂ) x).symm ((chartAt (H := ℂ) x) x) = x :=
      (chartAt (H := ℂ) x).left_inv (mem_chart_source ℂ x)
    have han := hanal x _ hz (by rw [hsy]; exact hx)
    exact untop₀_nonneg_iff.mpr han.meromorphicOrderAt_nonneg
  have hholo : ∀ x : X.carrier, x ∉ P → fM.holoRepr x = f x := by
    intro x hx
    have hc : ContinuousAt f x := (hfsm x hx).continuousAt
    exact (hc.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  have hFT : ∀ y : puncturedOpens P, F y = ((ψ y : ℂ) : RiemannSphere) := by
    intro y
    have hy : (y : X.carrier) ∉ P := (hpo _).1 y.2
    rw [hFdef, fM.toRiemannSphere_of_nonneg (horder y hy), hholo y hy, hf_on]
  -- non-constancy
  have hTinf : (↑P : Set X.carrier)ᶜ.Infinite := Set.infinite_univ.diff P.finite_toSet |>.mono (by simp)
  obtain ⟨a, ha, b, hb, hab⟩ := hTinf.nontrivial
  have ha' : a ∉ P := by simpa using ha
  have hb' : b ∉ P := by simpa using hb
  have hnc : ¬ IsConstantMap F := by
    rintro ⟨c, hc⟩
    have h1 : F a = ((ψ ⟨a, (hpo a).2 ha'⟩ : ℂ) : RiemannSphere) := hFT ⟨a, (hpo a).2 ha'⟩
    have h2 : F b = ((ψ ⟨b, (hpo b).2 hb'⟩ : ℂ) : RiemannSphere) := hFT ⟨b, (hpo b).2 hb'⟩
    have h3 : F a = F b := (hc a).trans (hc b).symm
    have h4 : ψ ⟨a, (hpo a).2 ha'⟩ = ψ ⟨b, (hpo b).2 hb'⟩ :=
      OnePoint.coe_injective (h1.symm.trans (h3.trans h2))
    exact hab (congrArg Subtype.val (hinj h4))
  -- a regular value of fibre size one
  have hCfin := Jacobians.Discharge.Manifold.criticalValues_finite_general F hFsm hnc
  set C := Jacobians.Discharge.Manifold.criticalValuesGeneral F with hCdef
  have hBad : (C ∪ F '' (↑P : Set X.carrier)).Finite := hCfin.union (P.finite_toSet.image F)
  have : Infinite (puncturedOpens P) := hTinf.to_subtype
  have hRinf : (range ψ).Infinite := Set.infinite_range_of_injective hinj
  have hpre : (((↑) : ℂ → RiemannSphere) ⁻¹' (C ∪ F '' (↑P : Set X.carrier))).Finite :=
    hBad.preimage OnePoint.coe_injective.injOn
  obtain ⟨w, hwR, hwB⟩ := (hRinf.diff hpre).nonempty
  obtain ⟨y0, rfl⟩ := hwR
  have hwC : ((ψ y0 : ℂ) : RiemannSphere) ∉ C ∪ F '' (↑P : Set X.carrier) := hwB
  have hfib : F ⁻¹' {((ψ y0 : ℂ) : RiemannSphere)} = {(y0 : X.carrier)} := by
    ext x
    constructor
    · intro hx
      have hxP : x ∉ P := fun hxP => hwC (Or.inr ⟨x, hxP, hx⟩)
      have hx' : F x = ((ψ ⟨x, (hpo x).2 hxP⟩ : ℂ) : RiemannSphere) := hFT ⟨x, (hpo x).2 hxP⟩
      have : ψ ⟨x, (hpo x).2 hxP⟩ = ψ y0 := OnePoint.coe_injective (hx'.symm.trans hx)
      exact congrArg Subtype.val (hinj this)
    · intro hx
      rw [mem_singleton_iff] at hx
      subst hx
      exact hFT y0
  have hone : (F ⁻¹' {((ψ y0 : ℂ) : RiemannSphere)}).ncard = 1 := by
    rw [hfib]; exact Set.ncard_singleton _
  obtain ⟨hb, hopen⟩ := s31hy_bijective_of_fibre F hFsm hnc (fun h => hwC (Or.inl h)) hone
  refine ⟨⟨(Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective F hb) hFsm.continuous hopen).trans
    RiemannSphere.homeoSphere⟩, ?_⟩
  -- counting the punctures
  set N : Set RiemannSphere := {z | z ∉ range (fun y : puncturedOpens P => F y)} with hN
  have hFP : F '' (↑P : Set X.carrier) = N := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩ ⟨y, hy⟩
      have : (y : X.carrier) = p := hb.1 hy
      exact ((hpo y).1 y.2) (this ▸ hp)
    · intro hz
      obtain ⟨x, rfl⟩ := hb.2 z
      by_cases hx : x ∈ P
      · exact ⟨x, hx, rfl⟩
      · exact absurd ⟨⟨x, (hpo x).2 hx⟩, rfl⟩ hz
  have hNeq : N = {OnePoint.infty} ∪ ((↑) : ℂ → RiemannSphere) '' {w : ℂ | w ∉ range ψ} := by
    ext z
    induction z using OnePoint.rec with
    | infty =>
      simp only [hN, mem_setOf_eq, mem_union, mem_singleton_iff, true_or, iff_true]
      rintro ⟨y, hy⟩
      have hy' : F y = OnePoint.infty := hy
      rw [hFT y] at hy'
      exact OnePoint.coe_ne_infty _ hy'
    | coe w =>
      simp only [hN, mem_setOf_eq, mem_union, mem_singleton_iff, mem_image]
      constructor
      · intro hw
        refine Or.inr ⟨w, fun ⟨y, hy⟩ => hw ⟨y, ?_⟩, rfl⟩
        show F y = _
        rw [hFT y, hy]
      · rintro (h | ⟨w', hw', hww'⟩)
        · exact absurd h (OnePoint.coe_ne_infty _)
        · rintro ⟨y, hy⟩
          apply hw'
          have h1 : F y = ((w : ℂ) : RiemannSphere) := hy
          rw [hFT y, ← hww'] at h1
          exact ⟨y, OnePoint.coe_injective h1⟩
  have hcard1 : (↑P : Set X.carrier).ncard = P.card := Set.ncard_coe_finset P
  have hcard2 : (F '' (↑P : Set X.carrier)).ncard = (↑P : Set X.carrier).ncard :=
    Set.ncard_image_of_injective _ hb.1
  rw [← hcard1, ← hcard2, hFP, hNeq]
  have hdisj : Disjoint ({OnePoint.infty} : Set RiemannSphere)
      (((↑) : ℂ → RiemannSphere) '' {w : ℂ | w ∉ range ψ}) := by
    rw [Set.disjoint_singleton_left]
    rintro ⟨w, _, hw⟩
    exact OnePoint.coe_ne_infty _ hw
  rw [Set.ncard_union_eq hdisj (Set.finite_singleton _) (hfin.image _), Set.ncard_singleton,
    Set.ncard_image_of_injective _ OnePoint.coe_injective]

theorem s31hy_homeo_punctured {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {X : ClosedRS.{u}} (P : Finset X.carrier) (ι : S → X.carrier)
    (hemb : Topology.IsOpenEmbedding ι) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι)
    (hrange : range ι = (↑P : Set X.carrier)ᶜ) :
    ∃ e : S ≃ₜ puncturedOpens P, IsBiholomorphic e := by
  have hmem : ∀ s, ι s ∈ puncturedOpens P := fun s => by
    have : ι s ∈ range ι := mem_range_self s
    rw [hrange] at this
    exact this
  set ι' : S → puncturedOpens P := fun s => ⟨ι s, hmem s⟩ with hι'
  have hbij : Function.Bijective ι' :=
    ⟨fun a b h => hemb.injective (congrArg Subtype.val h), fun t => by
      have : (t : X.carrier) ∈ range ι := by rw [hrange]; exact t.2
      obtain ⟨s, hs⟩ := this
      exact ⟨s, Subtype.ext hs⟩⟩
  have hc : Continuous ι' := hemb.continuous.subtype_mk hmem
  have ho : IsOpenMap ι' := by
    intro U hU
    have : ι' '' U = Subtype.val ⁻¹' (ι '' U) := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, hst⟩
        exact ⟨s, hs, Subtype.ext hst⟩
    rw [this]
    exact (hemb.isOpenMap U hU).preimage continuous_subtype_val
  set e : S ≃ₜ puncturedOpens P := (Equiv.ofBijective ι' hbij).toHomeomorphOfContinuousOpen hc ho with he
  have hι : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ ι := (k22u_mdifferentiable_contMDiff hhol).of_le le_top
  have hι' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ ι' :=
    (ContMDiff.subtypeVal_comp_iff (puncturedOpens P) ι').1 hι
  have hdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e := hι'.mdifferentiable (by simp)
  exact ⟨e, (isKQCRS_one_iff e).1 ⟨le_rfl, s23_h_isKQC_one hdiff⟩⟩

theorem s31hy_unif_transfer {S T : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [TopologicalSpace T]
    [ChartedSpace ℂ T] (e : T ≃ₜ S) (he : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) e)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → T}
    (hp : IsUniformization Γ p) : IsUniformization Γ (e ∘ p) :=
  ⟨hp.1.homeomorph_comp e, he.comp hp.2.1, e.surjective.comp hp.2.2.1, fun τ₁ τ₂ => by
    rw [Function.comp_apply, Function.comp_apply, e.injective.eq_iff]
    exact hp.2.2.2 τ₁ τ₂⟩

theorem s31hy_connected_punctured {X : ClosedRS.{u}} (P : Finset X.carrier) :
    ConnectedSpace (puncturedOpens P) := by
  classical
  letI : Infinite X.carrier :=
    Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x, hx⟩ := P.exists_notMem
  have hne : ((↑P : Set X.carrier)ᶜ).Nonempty :=
    ⟨x, by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hx⟩
  have hc : IsConnected ((↑P : Set X.carrier)ᶜ) :=
    (Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
      P.finite_toSet hne).isConnected
  exact Subtype.connectedSpace hc

theorem s31hy_no_compact {X : ClosedRS.{u}} (P : Finset X.carrier) (hP : P.Nonempty)
    (hc : CompactSpace (puncturedOpens P)) : False := by
  classical
  letI : Infinite X.carrier :=
    Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  have hcl : IsClosed (range (Subtype.val : puncturedOpens P → X.carrier)) :=
    (isCompact_range continuous_subtype_val).isClosed
  have hr : range (Subtype.val : puncturedOpens P → X.carrier) = (↑P : Set X.carrier)ᶜ := by
    ext x
    simp [puncturedOpens]
  rw [hr, isClosed_compl_iff] at hcl
  have hclopen : IsClopen (↑P : Set X.carrier) := ⟨P.finite_toSet.isClosed, hcl⟩
  rcases isClopen_iff.1 hclopen with h | h
  · obtain ⟨x, hx⟩ := hP
    have : x ∈ (↑P : Set X.carrier) := hx
    rw [h] at this
    exact this
  · haveI : Finite X.carrier := Set.finite_univ_iff.1 (h ▸ P.finite_toSet)
    exact not_finite X.carrier

theorem s31hy_core {X : ClosedRS.{u}} {g n : ℕ} (hX : HasGenus X.carrier g) (P : Finset X.carrier)
    (hP : P.card = n) (hex : ¬ IsExceptionalType g n 0) :
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → puncturedOpens P),
      IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p := by
  classical
  have hgen : genus X.carrier = g := k22rr_genus_eq hX
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- no punctures
    subst hn
    have hP0 : P = ∅ := Finset.card_eq_zero.1 hP
    subst hP0
    have hg : 1 < g := by
      by_contra h
      apply hex
      have : g = 0 ∨ g = 1 := by omega
      rcases this with rfl | rfl <;> simp [IsExceptionalType]
    obtain ⟨Γ, p, h1, h2, h3⟩ := s22hg_exists_fuchsian_uniformization (S := X.carrier) hg hX
    obtain ⟨e, he⟩ := s31hy_homeo_punctured (S := X.carrier) (∅ : Finset X.carrier) id
      (Homeomorph.refl X.carrier).isOpenEmbedding mdifferentiable_id (by simp)
    exact ⟨Γ, e ∘ p, h1, h2, s31hy_unif_transfer e he.1 h3⟩
  · -- at least one puncture: classify `X ∖ P`
    have hPne : P.Nonempty := Finset.card_pos.1 (hP ▸ hn)
    haveI : ConnectedSpace (puncturedOpens P) := s31hy_connected_punctured P
    -- the two non-hyperbolic planar alternatives
    have hplane : ∀ f : puncturedOpens P → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → Function.Injective f →
        {w : ℂ | w ∉ range f}.Finite → (n = 1 + {w : ℂ | w ∉ range f}.ncard) ∧ g = 0 := by
      intro f hf hinj hfin
      obtain ⟨hsph, hcard⟩ := s31hy_sphere_of_injective P f hf hinj hfin
      refine ⟨hP ▸ hcard, ?_⟩
      have := genus_zero_of_nonempty_homeo_sphere (X := X.carrier) hsph
      omega
    rcases thm22_3_classification (S := puncturedOpens P) with
      ⟨hc, _⟩ | ⟨f, hf, g', hg1, hg2⟩ | ⟨f, hf, g', hg1, hg2⟩ | ⟨L, p, hcov, _, hsurj, hper⟩ | hhyp
    · exact (s31hy_no_compact P hPne hc).elim
    · -- `X ∖ P ≅ ℂ`
      have hrange : {w : ℂ | w ∉ range f} = ∅ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
        exact ⟨g' w, hg2.2 w⟩
      obtain ⟨h1, h2⟩ := hplane f hf hg2.1.injective (by rw [hrange]; exact finite_empty)
      rw [hrange, ncard_empty] at h1
      exact (hex (by
        obtain rfl : n = 1 := by omega
        subst h2
        simp [IsExceptionalType])).elim
    · -- `X ∖ P ≅ ℂ*`
      set ψ : puncturedOpens P → ℂ := fun x => ((f x : puncturedPlaneOpens) : ℂ) with hψ
      have hψd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ψ :=
        ((contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)).comp hf
      have hψi : Function.Injective ψ := fun a b h =>
        hg2.1.injective (Subtype.ext h)
      have hrange : {w : ℂ | w ∉ range ψ} = {0} := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hw
          by_contra hne
          apply hw
          refine ⟨g' ⟨w, hne⟩, ?_⟩
          show ((f (g' ⟨w, hne⟩) : puncturedPlaneOpens) : ℂ) = w
          rw [hg2.2 ⟨w, hne⟩]
        · rintro rfl ⟨x, hx⟩
          exact (f x).2 hx
      obtain ⟨h1, h2⟩ := hplane ψ hψd hψi (by rw [hrange]; exact finite_singleton _)
      rw [hrange, ncard_singleton] at h1
      exact (hex (by
        obtain rfl : n = 2 := by omega
        subst h2
        simp [IsExceptionalType])).elim
    · -- the torus alternative: `X ∖ P` would be compact
      have hc : CompactSpace (puncturedOpens P) := by
        refine isCompact_univ_iff.1 ?_
        have hcomp : IsCompact (range p) :=
          IsZLattice.isCompact_range_of_periodic L.lattice p hcov.continuous (fun z w hw => by
            rw [(hper (z + w) z).2 (by simpa using hw)])
        rwa [hsurj.range_eq] at hcomp
      exact (s31hy_no_compact P hPne hc).elim
    · exact hhyp

theorem s31hy_exceptional_double {g n m : ℕ} (hm : m ≠ 0)
    (h : IsExceptionalType (2 * g + m - 1) (2 * n) 0) : IsExceptionalType g n m := by
  simp only [IsExceptionalType, Prod.mk.injEq] at h ⊢
  rcases h with h | h | h | h | h | h | h
  · right; right; right; right; left; omega
  · omega
  · right; right; right; right; right; right; omega
  · right; right; right; right; right; left; omega
  · omega
  · omega
  · omega

end s31hy_helpers

/-- §31.1: a non-exceptional surface of type `(g, n, 0)` has hyperbolic universal covering
(`ℍ/Γ` with `Γ` a torsion free Fuchsian group), and so has the Schottky double of a non-exceptional
surface of type `(g, n, m)`, `m ≠ 0`; hence their Poincaré metrics are defined. -/
theorem finiteType_hyperbolic {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (hex : ¬ IsExceptionalType g n m) :
    (m = 0 → ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S),
      IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p) ∧
    (m ≠ 0 → ∀ (Xd : ClosedRS.{u}) (J : Xd.carrier ≃ₜ Xd.carrier) (ιd : S → Xd.carrier) (Pd : Finset Xd.carrier),
      IsSchottkyDouble F Xd J ιd Pd →
      ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → puncturedOpens Pd),
        IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p) := by
  classical
  constructor
  · intro hm
    subst hm
    have hr : range F.ι = (↑F.P : Set F.X.carrier)ᶜ := by
      rw [F.range_ι]; simp
    obtain ⟨Γ, p, h1, h2, h3⟩ := s31hy_core F.genus F.P F.card_P hex
    obtain ⟨e, he⟩ := s31hy_homeo_punctured F.P F.ι F.embedding F.holomorphic hr
    obtain ⟨_, g', hg', _, hr'⟩ := he
    have hsymm : (e.symm : puncturedOpens F.P → S) = g' := funext fun x =>
      e.injective (by rw [e.apply_symm_apply, hr' x])
    exact ⟨Γ, e.symm ∘ p, h1, h2, s31hy_unif_transfer e.symm (hsymm ▸ hg') h3⟩
  · intro hm Xd J ιd Pd hD
    have hex' : ¬ IsExceptionalType (2 * g + m - 1) (2 * n) 0 := fun h =>
      hex (s31hy_exceptional_double hm h)
    exact s31hy_core hD.genus Pd hD.card_Pd hex'

/-- §31.1: positivity of the dimension (31.2) is *sufficient* for non-exceptionality — every
exceptional type has `6g - 6 + 2n + 3m ≤ 0`. -/
theorem not_exceptional_of_pos {g n m : ℕ} (h : 0 < 6 * (g : ℤ) - 6 + 2 * n + 3 * m) :
    ¬ IsExceptionalType g n m := by
  simp only [IsExceptionalType, Prod.mk.injEq]
  omega

/-- §31.1: conversely, a non-exceptional type has `6g - 6 + 2n + 3m ≥ 0`, so the dimension (31.2)
of `Q̃(S₀)` is never negative off the exceptional list.

**Correction.**  These two implications replace a previous `not_exceptional_iff` asserting
`¬ IsExceptionalType g n m ↔ 0 < 6g - 6 + 2n + 3m`, which is **false**.  `(0,3,0)` — the
thrice-punctured sphere — is not among the book's seven exceptional types, yet
`6·0 - 6 + 2·3 + 3·0 = 0`, so the left side holds and the right side fails; it is the unique
counterexample.  Weakening to `0 ≤ …` does not repair it either, because the value-`0` fibre is
mixed: `(1,0,0)` and `(0,0,2)` are exceptional and also give `0`.  Hence **no inequality in
`6g - 6 + 2n + 3m` characterises the exceptional list**, and the two implications here are
exactly its true content.

The book (§31.1) gives the exceptional types only as the explicit list
`(0,0,0), (0,1,0), (1,0,0), (0,2,0); (0,0,1), (0,1,1), (0,0,2)`, justified by the surface or its
Schottky double lacking a hyperbolic universal covering, and uses `6g - 6 + 2n + 3m` only in
(31.2), as `dim_ℝ Q̃(S₀)`.  It never states the equivalence.  The underlying conflation is between
*hyperbolic* and *positive-dimensional Teichmüller space*: the thrice-punctured sphere is
hyperbolic — it is the standard example — but rigid, so its Teichmüller space is a point. -/
theorem dim_nonneg_of_not_exceptional {g n m : ℕ} (h : ¬ IsExceptionalType g n m) :
    0 ≤ 6 * (g : ℤ) - 6 + 2 * n + 3 * m := by
  by_contra hlt
  rw [not_le] at hlt
  refine h ?_
  simp only [IsExceptionalType, Prod.mk.injEq]
  omega

/-! ## §31.2 Admissible quadratic differentials -/

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- **§31.2 (允许二次微分).**  A meromorphic quadratic differential `q` on the closed surface `X` of
`F` is admissible for `S₀ = S` if (i) it is holomorphic except for at most simple poles at the
punctures `P`, and (ii) it extends continuously to the non-puncture boundary (the curves `∂(D j)`)
and takes real values along each such curve: `q(c(t)) c'(t)² ∈ ℝ` for the `C¹` parametrizations
`c` of the boundary curves in charts.  (The coefficients are normalized to vanish at the poles.)  Over
the interiors of the holes `D j` the coefficients vanish.

**Correction (2026-09-27).**  The sets `(chartAt ℂ x).target ∩ chartAt ℂ x '' A` became
`(chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' A` and `q = 0` over `interior (D j)` was added, because the
chart's junk values off its source could kill the poles at the punctures, and `q` was unconstrained inside
the holes (so `Q̃(S₀)` was infinite dimensional for `m ≠ 0`); both defects were refuted in Lean (s31t). -/
def IsAdmissibleQD (F : FiniteTypeStructure S g n m) (q : F.X.carrier → ℂ → ℂ) : Prop :=
  IsDiffFamily 2 0 q ∧
  (∀ x : F.X.carrier, DifferentiableOn ℂ (q x) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' range F.ι)) ∧
  (∀ x : F.X.carrier, ∀ p ∈ F.P, p ∈ (chartAt ℂ x).source → q x (chartAt ℂ x p) = 0 ∧
    ∃ c : ℂ, ∃ r : ℂ → ℂ, AnalyticAt ℂ r (chartAt ℂ x p) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p), q x z = c / (z - chartAt ℂ x p) + r z) ∧
  (∀ (x : F.X.carrier) (j : Fin m),
    ContinuousOn (q x) ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (range F.ι ∪ frontier (F.D j)))) ∧
  (∀ (x : F.X.carrier) (j : Fin m) (c : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 c (Icc a b) →
    c '' Icc a b ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' frontier (F.D j) →
    ∀ t ∈ Ioo a b, (q x (c t) * deriv c t ^ 2).im = 0) ∧
  ∀ (x : F.X.carrier) (j : Fin m), ∀ z ∈ (chartAt ℂ x).target,
    (chartAt ℂ x).symm z ∈ interior (F.D j) → q x z = 0

/-- §31.2: the admissible quadratic differentials form a real vector space `Q̃(S₀)`. -/
def admissibleQDSpace (F : FiniteTypeStructure S g n m) : Submodule ℝ (F.X.carrier → ℂ → ℂ) where
  carrier := {q | IsAdmissibleQD F q}
  add_mem' := by
    rintro q₁ q₂ ⟨h₁, d₁, p₁, c₁, r₁, o₁⟩ ⟨h₂, d₂, p₂, c₂, r₂, o₂⟩
    refine ⟨(diffFamilySubmodule _ 2 0).add_mem h₁ h₂, fun x => (d₁ x).add (d₂ x), ?_, ?_, ?_, ?_⟩
    · intro x p hp hs
      obtain ⟨z₁, a₁, s₁, hs₁, e₁⟩ := p₁ x p hp hs
      obtain ⟨z₂, a₂, s₂, hs₂, e₂⟩ := p₂ x p hp hs
      refine ⟨by simp [z₁, z₂], a₁ + a₂, fun z => s₁ z + s₂ z, hs₁.add hs₂, ?_⟩
      filter_upwards [e₁, e₂] with z hz₁ hz₂
      simp only [Pi.add_apply, hz₁, hz₂]
      ring
    · intro x j
      exact (c₁ x j).add (c₂ x j)
    · intro x j c a b hc hsub t ht
      have := r₁ x j c a b hc hsub t ht
      have := r₂ x j c a b hc hsub t ht
      simp only [Pi.add_apply, add_mul, Complex.add_im]
      linarith
    · intro x j z hz hD
      simp [o₁ x j z hz hD, o₂ x j z hz hD]
  zero_mem' :=
    ⟨(diffFamilySubmodule _ 2 0).zero_mem, fun _ => differentiableOn_const 0,
      fun _ _ _ _ => ⟨rfl, 0, fun _ => 0, analyticAt_const, Filter.Eventually.of_forall fun _ => by simp⟩,
      fun _ _ => continuousOn_const, fun _ _ _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
  smul_mem' := by
    rintro c q ⟨h, d, p, cont, r, o⟩
    refine ⟨(diffFamilySubmodule _ 2 0).smul_mem c h, fun x => (d x).const_smul c, ?_, ?_, ?_, ?_⟩
    · intro x p' hp hs
      obtain ⟨z, a, s, hs', e⟩ := p x p' hp hs
      refine ⟨by simp [z], c * a, fun w => c * s w, ?_, ?_⟩
      · exact analyticAt_const.mul hs'
      · filter_upwards [e] with w hw
        simp only [Pi.smul_apply, Complex.real_smul, hw]
        ring
    · intro x j
      exact (cont x j).const_smul c
    · intro x j c' a b hc hsub t ht
      have := r x j c' a b hc hsub t ht
      simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, this, mul_zero]
    · intro x j w hw hD
      simp [o x j w hw hD]

/-- Proposed interface: complex multiplication preserves the actual no-hole
admissible predicate, including zero values at every puncture. -/
theorem k31p_complex_smul [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) :
    ∀ (c : ℂ) (q : F.X.carrier → ℂ → ℂ),
      IsAdmissibleQD F q → IsAdmissibleQD F (c • q) := by
  intro c q hq
  rcases hq with ⟨h, d, p, _cont, _real, _outside⟩
  refine ⟨(diffFamilySubmodule F.X.carrier 2 0).smul_mem c h,
    fun x => (d x).const_smul c, ?_, ?_, ?_, ?_⟩
  · intro x p' hp hs
    obtain ⟨hz, a, r, hr, heq⟩ := p x p' hp hs
    refine ⟨by simp [Pi.smul_apply, smul_eq_mul, hz],
      c * a, fun z => c * r z, analyticAt_const.mul hr, ?_⟩
    filter_upwards [heq] with z hz'
    simp only [Pi.smul_apply, smul_eq_mul, hz']
    ring
  · intro x j
    exact Fin.elim0 j
  · intro x j
    exact Fin.elim0 j
  · intro x j
    exact Fin.elim0 j

/-- Proposed interface: taking the complex span adds no new families. -/
theorem k31p_complex_carrier [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) :
    ∀ q : F.X.carrier → ℂ → ℂ,
      q ∈ Submodule.span ℂ
        (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)) ↔ IsAdmissibleQD F q := by
  intro q
  constructor
  · intro hq
    refine Submodule.span_induction
      (p := fun q _ => IsAdmissibleQD F q) ?_ ?_ ?_ ?_ hq
    · intro q' hq'
      exact hq'
    · exact (admissibleQDSpace F).zero_mem
    · intro q₁ q₂ _ _ h₁ h₂
      exact (admissibleQDSpace F).add_mem h₁ h₂
    · intro c q' _ hq'
      exact k31p_complex_smul F c q' hq'
  · intro hq
    exact Submodule.subset_span hq

/-- Proposed interface: the same actual carrier has the original real vector-space structure
after restriction of scalars. -/
theorem k31p_real_equiv [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) :
    Nonempty
      ((Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)))
        ≃ₗ[ℝ] admissibleQDSpace F) := by
  refine ⟨{
    toFun := fun q => ⟨q.1, (k31p_complex_carrier F q.1).1 q.2⟩
    invFun := fun q => ⟨q.1, (k31p_complex_carrier F q.1).2 q.2⟩
    left_inv := fun q => Subtype.ext rfl
    right_inv := fun q => Subtype.ext rfl
    map_add' := fun q₁ q₂ => Subtype.ext rfl
    map_smul' := fun c q => Subtype.ext rfl }⟩

/-- Proposed interface: the reduced puncture divisor is an actual finitely supported
integer function, equal to one on P and zero elsewhere, of degree n. -/
theorem k31p_puncture_divisor [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) :
    ∃ E : Divisor F.X.carrier,
      (∀ x ∈ F.P, E x = 1) ∧ (∀ x ∉ F.P, E x = 0) ∧ E.deg = n := by
  classical
  let E : Divisor F.X.carrier := Finsupp.onFinset F.P
    (fun x => if x ∈ F.P then (1 : ℤ) else 0)
    (by
      intro x hx
      by_contra hpx
      exact hx (if_neg hpx))
  have hE (x : F.X.carrier) : E x = if x ∈ F.P then (1 : ℤ) else 0 := rfl
  have hsupport : E.support = F.P := by
    ext x
    by_cases hx : x ∈ F.P <;> simp [Finsupp.mem_support_iff, hE, hx]
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x hx
    simp [hE, hx]
  · intro x hx
    simp [hE, hx]
  · change (∑ x ∈ E.support, E x) = (n : ℤ)
    rw [hsupport]
    calc
      (∑ x ∈ F.P, E x) = ∑ x ∈ F.P, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hE, hx]
      _ = (F.P.card : ℤ) := by simp
      _ = (n : ℤ) := by rw [F.card_P]

/-- Proposed interface: for an actual meromorphic germ, order at least minus one
means a simple principal part plus an analytic remainder. No implication from a
junk value of meromorphicOrderAt is used. -/
theorem k31p_simple_pole_normal_form {φ : ℂ → ℂ} {a : ℂ}
    (hφ : MeromorphicAt φ a) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt φ a ↔
      ∃ (c : ℂ) (r : ℂ → ℂ), AnalyticAt ℂ r a ∧
        φ =ᶠ[𝓝[≠] a] (fun z => c / (z - a) + r z) := by
  classical
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - a) a :=
    analyticAt_id.sub analyticAt_const
  have hprod : MeromorphicAt (fun z : ℂ => (z - a) * φ z) a :=
    hlin.meromorphicAt.mul hφ
  have hprod_order : meromorphicOrderAt (fun z : ℂ => (z - a) * φ z) a =
      1 + meromorphicOrderAt φ a := by
    calc
      meromorphicOrderAt (fun z : ℂ => (z - a) * φ z) a =
          meromorphicOrderAt (fun z : ℂ => z - a) a + meromorphicOrderAt φ a :=
        meromorphicOrderAt_mul hlin.meromorphicAt hφ
      _ = 1 + meromorphicOrderAt φ a := by rw [meromorphicOrderAt_id_sub_const]
  have hcancel : (1 : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) = 0 := by
    change ((1 : ℤ) : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) = 0
    rw [← WithTop.coe_add]
    norm_num
  constructor
  · intro horder
    have hnonneg : 0 ≤ meromorphicOrderAt (fun z : ℂ => (z - a) * φ z) a := by
      rw [hprod_order]
      calc
        0 = (1 : WithTop ℤ) + ((-1 : ℤ) : WithTop ℤ) := hcancel.symm
        _ ≤ 1 + meromorphicOrderAt φ a := add_le_add_right horder 1
    obtain ⟨G, hG, heq⟩ := hprod.meromorphicOrderAt_nonneg_iff.mp hnonneg
    refine ⟨G a, dslope G a, kn_analyticAt_dslope_same hG, ?_⟩
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hz_ne
    have hza : z - a ≠ 0 := sub_ne_zero.mpr hz_ne
    have hslope : (z - a) * dslope G a z = G z - G a := by
      simpa only [smul_eq_mul] using sub_smul_dslope G a z
    apply mul_left_cancel₀ hza
    calc
      (z - a) * φ z = G z := hz
      _ = G a + (z - a) * dslope G a z := by rw [hslope]; ring
      _ = (z - a) * (G a / (z - a) + dslope G a z) := by
        field_simp [hza] <;> ring
  · rintro ⟨c, r, hr, heq⟩
    have hA : AnalyticAt ℂ (fun z : ℂ => c + (z - a) * r z) a :=
      analyticAt_const.add (hlin.mul hr)
    have hAeq : (fun z : ℂ => (z - a) * φ z) =ᶠ[𝓝[≠] a]
        (fun z => c + (z - a) * r z) := by
      filter_upwards [heq, self_mem_nhdsWithin] with z hz hz_ne
      have hza : z - a ≠ 0 := sub_ne_zero.mpr hz_ne
      rw [hz]
      field_simp [hza] <;> ring
    have hnonneg : 0 ≤ meromorphicOrderAt (fun z : ℂ => (z - a) * φ z) a :=
      hprod.meromorphicOrderAt_nonneg_iff.mpr ⟨_, hA, hAeq⟩
    rw [hprod_order] at hnonneg
    apply (add_le_add_iff_right_of_ne_top (a := (1 : WithTop ℤ)) (by simp)).mp
    simpa only [hcancel] using hnonneg

/-- Proposed interface: normalized actual admissible families are determined by
their punctured germs in their own charts, including removable punctures. -/
theorem k31p_admissible_ext [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) {q₁ q₂ : F.X.carrier → ℂ → ℂ}
    (h₁ : IsAdmissibleQD F q₁) (h₂ : IsAdmissibleQD F q₂)
    (heq : ∀ x, q₁ x =ᶠ[𝓝[≠] (chartAt ℂ x x)] q₂ x) : q₁ = q₂ := by
  classical
  have hRange : range F.ι = (↑F.P : Set F.X.carrier)ᶜ := by
    simpa using F.range_ι
  funext x z
  by_cases hz : z ∈ (chartAt ℂ x).target
  · let p : F.X.carrier := (chartAt ℂ x).symm z
    let c : ℂ := chartAt ℂ p p
    have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    have hc : c ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hps : (chartAt ℂ p).symm c ∈ (chartAt ℂ x).source := by
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact hp
    have ht : chartTransition x p c = z := by
      change (chartAt ℂ x) ((chartAt ℂ p).symm (chartAt ℂ p p)) = z
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact (chartAt ℂ x).right_inv hz
    have hv := h₁.1.2 x p c hc hps
    have hw := h₂.1.2 x p c hc hps
    simp only [ht, zpow_ofNat, pow_zero, mul_one] at hv hw
    have hd : deriv (chartTransition x p) c ≠ 0 :=
      Jacobians.Dolbeault.transition_deriv_ne_zero (y := p) (z := x) (x := p)
        (mem_chart_source ℂ p) hp
    have hcenter : q₁ p c = q₂ p c := by
      by_cases hP : p ∈ F.P
      · exact ((h₁.2.2.1 p p hP (mem_chart_source ℂ p)).1).trans
          ((h₂.2.2.1 p p hP (mem_chart_source ℂ p)).1).symm
      · have hOpen : IsOpen ((chartAt ℂ p).target ∩
            (chartAt ℂ p).symm ⁻¹' (↑F.P : Set F.X.carrier)ᶜ) :=
          (chartAt ℂ p).isOpen_inter_preimage_symm F.P.finite_toSet.isClosed.isOpen_compl
        have hcA : c ∈ (chartAt ℂ p).target ∩
            (chartAt ℂ p).symm ⁻¹' (↑F.P : Set F.X.carrier)ᶜ := by
          refine ⟨hc, ?_⟩
          change (chartAt ℂ p).symm (chartAt ℂ p p) ∉ F.P
          rwa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
        have hd₁ := h₁.2.1 p
        have hd₂ := h₂.2.1 p
        rw [hRange] at hd₁ hd₂
        exact tendsto_nhds_unique_of_eventuallyEq
          ((hd₁.differentiableAt (hOpen.mem_nhds hcA)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds)
          ((hd₂.differentiableAt (hOpen.mem_nhds hcA)).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds) (heq p)
    apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    exact hv.symm.trans (hcenter.trans hw)
  · rw [h₁.1.1 x z hz, h₂.1.1 x z hz]

/-- Proposed interface: the canonical-square product is actually meromorphic at
every chart point, with precisely the shifted divisor lower bound. -/
theorem k31p_product_order [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) {K : Divisor F.X.carrier}
    (q₀ : F.X.carrier → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) = meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (E : Divisor F.X.carrier) (hEP : ∀ x ∈ F.P, E x = 1)
    (hE0 : ∀ x ∉ F.P, E x = 0) (f : Jacobians.MeromorphicFunction F.X.carrier)
    (hf : f ∈ Jacobians.linearSystem (X := F.X.carrier) (2 • K + E)) :
    ∀ x z, z ∈ (chartAt ℂ x).target →
      MeromorphicAt (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) z ∧
        ((-E ((chartAt ℂ x).symm z) : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt
            (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) z := by
  -- The order formula holds for arbitrary E; its frozen puncture conditions are redundant here.
  have _hEP := hEP
  have _hE0 := hE0
  obtain ⟨σ, hσ⟩ := k22rr_coeff_section q₀ hfamily
  have hcoeff : ∀ x z, z ∈ (chartAt ℂ x).target →
      Jacobians.Dolbeault.formCoeff σ x =ᶠ[𝓝 z] q₀ x := by
    intro x z hz
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz] with w hw
    exact hσ x w hw
  let α : Jacobians.Dolbeault.MeromorphicOneForm F.X.carrier :=
    { toFun := σ
      meromorphic := by
        intro x
        have hx : chartAt ℂ x x ∈ (chartAt ℂ x).target :=
          (chartAt ℂ x).map_source (mem_chart_source ℂ x)
        exact (hmero x).congr
          ((hcoeff x (chartAt ℂ x x) hx).filter_mono nhdsWithin_le_nhds).symm }
  have hαorder : ∀ x, α.formOrderW x = (K x : WithTop ℤ) := by
    intro x
    change meromorphicOrderAt (Jacobians.Dolbeault.formCoeff σ x)
      (chartAt ℂ x x) = (K x : WithTop ℤ)
    have hx := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    rw [meromorphicOrderAt_congr
      ((hcoeff x (chartAt ℂ x x) hx).filter_mono nhdsWithin_le_nhds)]
    exact (horder x).symm
  intro x z hz
  let y : F.X.carrier := (chartAt ℂ x).symm z
  have hy : y ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
  have hcz : chartAt ℂ x y = z := (chartAt ℂ x).right_inv hz
  have hscalar := k22q_scalar_chart_pullback f x y hy
  rw [hcz] at hscalar
  obtain ⟨hfm, hfo⟩ := hscalar
  let ψ : ℂ → ℂ := chartAt ℂ y ∘ (chartAt ℂ x).symm
  have hψ_an : AnalyticAt ℂ ψ z := by
    have h : AnalyticAt ℂ ψ (chartAt ℂ x y) :=
      Jacobians.Dolbeault.transition_analyticAt_of_mem hy (mem_chart_source ℂ y)
    rwa [hcz] at h
  have hψ_val : ψ z = chartAt ℂ y y := rfl
  have hown : MeromorphicAt (Jacobians.Dolbeault.formCoeff α.toFun y) (ψ z) := by
    rw [hψ_val]
    exact α.meromorphic y
  have hcomp := hown.comp_analyticAt hψ_an
  have hchange : Jacobians.Dolbeault.formCoeff α.toFun x =ᶠ[𝓝 z]
      (fun w => deriv ψ w • Jacobians.Dolbeault.formCoeff α.toFun y (ψ w)) := by
    simpa only [hcz] using Jacobians.Dolbeault.formCoeff_change α x y hy
  have hαmero : MeromorphicAt (Jacobians.Dolbeault.formCoeff α.toFun x) z := by
    have hprod : MeromorphicAt
        ((fun w => deriv ψ w) • (Jacobians.Dolbeault.formCoeff α.toFun y ∘ ψ)) z :=
      hψ_an.deriv.meromorphicAt.smul hcomp
    exact hprod.congr (hchange.filter_mono nhdsWithin_le_nhds).symm
  have hqm : MeromorphicAt (q₀ x) z :=
    hαmero.congr ((hcoeff x z hz).filter_mono nhdsWithin_le_nhds)
  have hqo : meromorphicOrderAt (q₀ x) z = (K y : WithTop ℤ) := by
    rw [← meromorphicOrderAt_congr ((hcoeff x z hz).filter_mono nhdsWithin_le_nhds)]
    calc
      meromorphicOrderAt (Jacobians.Dolbeault.formCoeff σ x) z = α.formOrderW y := by
        have h := Jacobians.Dolbeault.formOrderW_chart_invariant α x y hy
        rw [hcz] at h
        exact h.symm
      _ = (K y : WithTop ℤ) := hαorder y
  have hraw : (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) =
      (f.toFun ∘ (chartAt ℂ x).symm) * ((q₀ x) * (q₀ x)) := by
    funext w
    show f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2 =
      f.toFun ((chartAt ℂ x).symm w) * (q₀ x w * q₀ x w)
    rw [pow_two]
  have hraworder : meromorphicOrderAt
      (fun w => f.toFun ((chartAt ℂ x).symm w) * (q₀ x w)^2) z =
      f.orderW y + ((K y : WithTop ℤ) + (K y : WithTop ℤ)) := by
    rw [hraw, meromorphicOrderAt_mul hfm (hqm.mul hqm),
      meromorphicOrderAt_mul hqm hqm, hfo, hqo]
  refine ⟨?_, ?_⟩
  · rw [hraw]
    exact hfm.mul (hqm.mul hqm)
  · change ((-E y : ℤ) : WithTop ℤ) ≤ _
    rw [hraworder]
    have hfy : ((-((2 • K + E) y) : ℤ) : WithTop ℤ) ≤ f.orderW y := by
      change ∀ t, ((-((2 • K + E) t) : ℤ) : WithTop ℤ) ≤ f.orderW t at hf
      exact hf y
    have hbound : ((-(K y + K y + E y) : ℤ) : WithTop ℤ) ≤ f.orderW y := by
      simpa only [Finsupp.smul_apply, two_smul, Finsupp.add_apply] using hfy
    have hcancel : ((-(K y + K y + E y) : ℤ) : WithTop ℤ) +
        ((K y : WithTop ℤ) + (K y : WithTop ℤ)) = ((-E y : ℤ) : WithTop ℤ) := by
      rw [← WithTop.coe_add (K y) (K y),
        ← WithTop.coe_add (-(K y + K y + E y)) (K y + K y)]
      have hint : -(K y + K y + E y) + (K y + K y) = -E y := by ring
      rw [hint]
    calc
      ((-E y : ℤ) : WithTop ℤ) = ((-(K y + K y + E y) : ℤ) : WithTop ℤ) +
          ((K y : WithTop ℤ) + (K y : WithTop ℤ)) := hcancel.symm
      _ ≤ f.orderW y + ((K y : WithTop ℤ) + (K y : WithTop ℤ)) :=
        add_le_add_left hbound _

/-- Proposed interface: regularization enforces all of IsAdmissibleQD, and zeroes
every coefficient at every puncture, including order-zero removable germs. -/
theorem k31p_regularize [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) {K : Divisor F.X.carrier}
    (q₀ : F.X.carrier → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) = meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (E : Divisor F.X.carrier) (hEP : ∀ x ∈ F.P, E x = 1)
    (hE0 : ∀ x ∉ F.P, E x = 0) (f : Jacobians.MeromorphicFunction F.X.carrier)
    (hf : f ∈ Jacobians.linearSystem (X := F.X.carrier) (2 • K + E)) :
    ∃! v : Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)),
      ∀ x, (v : F.X.carrier → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
        (fun z => f.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) := by
  classical
  have hRange : range F.ι = (↑F.P : Set F.X.carrier)ᶜ := by
    simpa using F.range_ι
  let raw : F.X.carrier → ℂ → ℂ := fun x z =>
    f.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2
  let A : F.X.carrier → Set ℂ := fun x =>
    (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (↑F.P : Set F.X.carrier)ᶜ
  let q : F.X.carrier → ℂ → ℂ := fun x =>
    (A x).indicator (toMeromorphicNFOn (raw x) (A x))
  have hOpen : ∀ x, IsOpen (A x) := fun x =>
    (chartAt ℂ x).isOpen_inter_preimage_symm F.P.finite_toSet.isClosed.isOpen_compl
  have hmer : ∀ x, MeromorphicOn (raw x) (chartAt ℂ x).target := by
    intro x z hz
    exact (k31p_product_order F q₀ hfamily hmero horder E hEP hE0 f hf x z hz).1
  have hmerA : ∀ x, MeromorphicOn (raw x) (A x) := fun x z hz => hmer x z hz.1
  have hnonneg : ∀ x z, z ∈ A x → 0 ≤ meromorphicOrderAt (raw x) z := by
    intro x z hz
    have hb := (k31p_product_order F q₀ hfamily hmero horder E hEP hE0 f hf x z hz.1).2
    have hEz : E ((chartAt ℂ x).symm z) = 0 := hE0 _ hz.2
    simpa only [hEz, neg_zero, WithTop.coe_zero] using hb
  have hrepair : ∀ x,
      AnalyticOnNhd ℂ (q x) (A x) ∧
        (∀ z ∈ A x, q x =ᶠ[𝓝[≠] z] raw x) ∧
        ∀ z, z ∉ A x → q x z = 0 := by
    intro x
    exact k22q_c_indicator_normal_form (raw x) (A x) (hOpen x) (hmerA x) (hnonneg x)
  have hzero : ∀ x p, p ∈ F.P → p ∈ (chartAt ℂ x).source →
      q x (chartAt ℂ x p) = 0 := by
    intro x p hp hs
    apply (hrepair x).2.2
    intro ha
    have hn := ha.2
    change (chartAt ℂ x).symm (chartAt ℂ x p) ∉ F.P at hn
    rw [(chartAt ℂ x).left_inv hs] at hn
    exact hn hp
  -- Isolate the physical point from P.erase p. This also handles removable punctures:
  -- their centre is zero, while all neighbouring non-puncture values retain the raw germ.
  have hfullGerm : ∀ x z, z ∈ (chartAt ℂ x).target → q x =ᶠ[𝓝[≠] z] raw x := by
    intro x z hz
    let p : F.X.carrier := (chartAt ℂ x).symm z
    have hErase : (↑(F.P.erase p) : Set F.X.carrier)ᶜ ∈ 𝓝 p :=
      (F.P.erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    have hpre : ∀ᶠ w in 𝓝 z, (chartAt ℂ x).symm w ∉ F.P.erase p :=
      ((chartAt ℂ x).continuousAt_symm hz).preimage_mem_nhds hErase
    have hAevent : ∀ᶠ w in 𝓝[≠] z, w ∈ A x := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        ((chartAt ℂ x).open_target.mem_nhds hz),
        eventually_nhdsWithin_of_eventually_nhds hpre, self_mem_nhdsWithin] with w hwt hwp hwz
      have hwne : w ≠ z := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hwz
      refine ⟨hwt, ?_⟩
      change (chartAt ℂ x).symm w ∉ F.P
      intro hwP
      have hne : (chartAt ℂ x).symm w ≠ p := by
        intro he
        apply hwne
        calc
          w = chartAt ℂ x ((chartAt ℂ x).symm w) := ((chartAt ℂ x).right_inv hwt).symm
          _ = chartAt ℂ x p := congrArg (chartAt ℂ x) he
          _ = z := (chartAt ℂ x).right_inv hz
      exact hwp (Finset.mem_erase.mpr ⟨hne, hwP⟩)
    filter_upwards [hAevent, (hmer x z hz).eventually_analyticAt] with w hw ha
    change (A x).indicator (toMeromorphicNFOn (raw x) (A x)) w = raw x w
    rw [Set.indicator_of_mem hw,
      toMeromorphicNFOn_eq_toMeromorphicNFAt (hmerA x) hw,
      toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
  have hfamilyq : IsDiffFamily 2 0 q := by
    refine ⟨?_, ?_⟩
    · intro x z hz
      apply (hrepair x).2.2
      intro ha
      exact hz ha.1
    · intro x y z hz hx
      have hxt : chartTransition x y z ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source hx
      by_cases hP : (chartAt ℂ y).symm z ∈ F.P
      · have hzy : q y z = 0 := by
          simpa only [(chartAt ℂ y).right_inv hz] using
            hzero y ((chartAt ℂ y).symm z) hP ((chartAt ℂ y).map_target hz)
        have hzx : q x (chartTransition x y z) = 0 :=
          hzero x ((chartAt ℂ y).symm z) hP hx
        simp only [hzy, hzx, zero_mul]
      · have hAy : z ∈ A y := ⟨hz, hP⟩
        have hAx : chartTransition x y z ∈ A x := by
          refine ⟨hxt, ?_⟩
          change (chartAt ℂ x).symm (chartAt ℂ x ((chartAt ℂ y).symm z)) ∉ F.P
          rwa [(chartAt ℂ x).left_inv hx]
        have ha : AnalyticAt ℂ (chartTransition x y) z := by
          change AnalyticAt ℂ ((chartAt ℂ x) ∘ (chartAt ℂ y).symm) z
          simpa only [(chartAt ℂ y).right_inv hz] using
            (Jacobians.Dolbeault.transition_analyticAt_of_mem
              (y := y) (z := x) (x := (chartAt ℂ y).symm z)
              ((chartAt ℂ y).map_target hz) hx)
        have ht : Tendsto (chartTransition x y) (𝓝[≠] z)
            (𝓝[≠] (chartTransition x y z)) :=
          ((chartAt ℂ x).tendsto_nhdsNE hx).comp
            ((chartAt ℂ y).symm.tendsto_nhdsNE hz)
        have hpre : ∀ᶠ u in 𝓝 z,
            (chartAt ℂ y).symm u ∈ (chartAt ℂ x).source :=
          ((chartAt ℂ y).continuousAt_symm hz).preimage_mem_nhds
            ((chartAt ℂ x).open_source.mem_nhds hx)
        have he : q y =ᶠ[𝓝[≠] z]
            (fun u => q x (chartTransition x y u) * (deriv (chartTransition x y) u)^2) := by
          filter_upwards [hfullGerm y z hz,
            ht.eventually (hfullGerm x (chartTransition x y z) hxt),
            nhdsWithin_le_nhds ((chartAt ℂ y).open_target.mem_nhds hz),
            nhdsWithin_le_nhds hpre] with u huy hux hut hus
          have hcoeff := hfamily.2 x y u hut hus
          simp only [zpow_one, zpow_zero, mul_one] at hcoeff
          have hscalar : f.toFun ((chartAt ℂ y).symm u) =
              f.toFun ((chartAt ℂ x).symm (chartTransition x y u)) := by
            change f.toFun ((chartAt ℂ y).symm u) =
              f.toFun ((chartAt ℂ x).symm ((chartAt ℂ x) ((chartAt ℂ y).symm u)))
            rw [(chartAt ℂ x).left_inv hus]
          calc
            q y u = raw y u := huy
            _ = raw x (chartTransition x y u) * (deriv (chartTransition x y) u)^2 := by
              change f.toFun ((chartAt ℂ y).symm u) * (q₀ y u)^2 =
                f.toFun ((chartAt ℂ x).symm (chartTransition x y u)) *
                  (q₀ x (chartTransition x y u))^2 * (deriv (chartTransition x y) u)^2
              rw [hscalar, hcoeff]
              ring
            _ = q x (chartTransition x y u) * (deriv (chartTransition x y) u)^2 := by rw [hux]
        have hl : Tendsto (q y) (𝓝[≠] z) (𝓝 (q y z)) :=
          ((hrepair y).1 z hAy).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        have hr : Tendsto
            (fun u => q x (chartTransition x y u) * (deriv (chartTransition x y) u)^2)
            (𝓝[≠] z)
            (𝓝 (q x (chartTransition x y z) * (deriv (chartTransition x y) z)^2)) :=
          ((((hrepair x).1 (chartTransition x y z) hAx).continuousAt.comp
            ha.continuousAt).mul (ha.deriv.continuousAt.pow 2)).tendsto.mono_left nhdsWithin_le_nhds
        simpa only [zpow_ofNat, pow_zero, mul_one] using
          tendsto_nhds_unique_of_eventuallyEq hl hr he
  have hq : IsAdmissibleQD F q := by
    refine ⟨hfamilyq, ?_, ?_, ?_, ?_, ?_⟩
    · intro x z hz
      rw [hRange] at hz
      exact ((hrepair x).1 z hz).differentiableAt.differentiableWithinAt
    · intro x p hp hs
      have ht := (chartAt ℂ x).map_source hs
      have hb := (k31p_product_order F q₀ hfamily hmero horder E hEP hE0 f hf
        x (chartAt ℂ x p) ht).2
      rw [(chartAt ℂ x).left_inv hs, hEP p hp] at hb
      obtain ⟨c, r, hr, he⟩ :=
        (k31p_simple_pole_normal_form (hmer x (chartAt ℂ x p) ht)).mp hb
      exact ⟨hzero x p hp hs, c, r, hr, (hfullGerm x (chartAt ℂ x p) ht).trans he⟩
    · intro x j
      exact Fin.elim0 j
    · intro x j
      exact Fin.elim0 j
    · intro x j
      exact Fin.elim0 j
  let v : Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)) :=
    ⟨q, (k31p_complex_carrier F q).mpr hq⟩
  have hv : ∀ x, (v : F.X.carrier → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)] raw x := by
    intro x
    exact hfullGerm x _ ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  refine ⟨v, hv, ?_⟩
  intro w hw
  apply Subtype.ext
  apply k31p_admissible_ext F
    ((k31p_complex_carrier F (w : F.X.carrier → ℂ → ℂ)).mp w.property) hq
  intro x
  exact (hw x).trans (hv x).symm

/-- Proposed interface: division produces an actual meromorphic representative in
the shifted linear system. Reconstruction is a punctured-germ statement, so no
pointwise cancellation at a zero of q₀ is asserted. -/
theorem k31p_division [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) {K : Divisor F.X.carrier}
    (q₀ : F.X.carrier → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) = meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (E : Divisor F.X.carrier) (hEP : ∀ x ∈ F.P, E x = 1)
    (hE0 : ∀ x ∉ F.P, E x = 0)
    (v : Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ))) :
    ∃ f : Jacobians.MeromorphicFunction F.X.carrier,
      f ∈ Jacobians.linearSystem (X := F.X.carrier) (2 • K + E) ∧
        ∀ x, (v : F.X.carrier → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
          (fun z => f.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) := by
  classical
  have hadm : IsAdmissibleQD F (v : F.X.carrier → ℂ → ℂ) :=
    (k31p_complex_carrier F (v : F.X.carrier → ℂ → ℂ)).mp v.property
  have hRange : range F.ι = (↑F.P : Set F.X.carrier)ᶜ := by
    simpa using F.range_ι
  -- Local meromorphy is actual on both branches; the pole branch uses its principal part.
  have hlocal : ∀ x,
      MeromorphicAt ((v : F.X.carrier → ℂ → ℂ) x) (chartAt ℂ x x) ∧
        ((-E x : ℤ) : WithTop ℤ) ≤
          meromorphicOrderAt ((v : F.X.carrier → ℂ → ℂ) x) (chartAt ℂ x x) := by
    intro x
    by_cases hx : x ∈ F.P
    · obtain ⟨_hzero, c, r, hr, he⟩ := hadm.2.2.1 x x hx (mem_chart_source ℂ x)
      have hc : MeromorphicAt (fun _ : ℂ => c) (chartAt ℂ x x) := analyticAt_const.meromorphicAt
      have hd : MeromorphicAt (fun z : ℂ => z - chartAt ℂ x x) (chartAt ℂ x x) :=
        (analyticAt_id.sub analyticAt_const).meromorphicAt
      have hm : MeromorphicAt ((v : F.X.carrier → ℂ → ℂ) x) (chartAt ℂ x x) :=
        ((hc.div hd).add hr.meromorphicAt).congr (Filter.EventuallyEq.symm he)
      refine ⟨hm, ?_⟩
      rw [hEP x hx]
      exact (k31p_simple_pole_normal_form hm).mpr ⟨c, r, hr, he⟩
    · have hOpen : IsOpen ((chartAt ℂ x).target ∩
          (chartAt ℂ x).symm ⁻¹' (↑F.P : Set F.X.carrier)ᶜ) :=
        (chartAt ℂ x).isOpen_inter_preimage_symm F.P.finite_toSet.isClosed.isOpen_compl
      have hxA : chartAt ℂ x x ∈ (chartAt ℂ x).target ∩
          (chartAt ℂ x).symm ⁻¹' (↑F.P : Set F.X.carrier)ᶜ := by
        refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
        change (chartAt ℂ x).symm (chartAt ℂ x x) ∉ F.P
        rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
      have hdiff := hadm.2.1 x
      rw [hRange] at hdiff
      have ha := hdiff.analyticAt (hOpen.mem_nhds hxA)
      refine ⟨ha.meromorphicAt, ?_⟩
      simpa only [hE0 x hx, neg_zero, WithTop.coe_zero] using ha.meromorphicOrderAt_nonneg
  let g : F.X.carrier → ℂ := fun p =>
    (v : F.X.carrier → ℂ → ℂ) p (chartAt ℂ p p) / (q₀ p (chartAt ℂ p p))^2
  have hrep : ∀ x z, z ∈ (chartAt ℂ x).target →
      g ((chartAt ℂ x).symm z) = (v : F.X.carrier → ℂ → ℂ) x z / (q₀ x z)^2 := by
    intro x z hz
    let p : F.X.carrier := (chartAt ℂ x).symm z
    let c : ℂ := chartAt ℂ p p
    have hp : p ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz
    have hc : c ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hps : (chartAt ℂ p).symm c ∈ (chartAt ℂ x).source := by
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact hp
    have ht : chartTransition x p c = z := by
      change (chartAt ℂ x) ((chartAt ℂ p).symm (chartAt ℂ p p)) = z
      rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
      exact (chartAt ℂ x).right_inv hz
    have hv := hadm.1.2 x p c hc hps
    have hq := hfamily.2 x p c hc hps
    have hd : deriv (chartTransition x p) c ≠ 0 :=
      Jacobians.Dolbeault.transition_deriv_ne_zero (y := p) (z := x) (x := p)
        (mem_chart_source ℂ p) hp
    simp only [ht, zpow_ofNat, pow_zero, mul_one] at hv
    simp only [ht, zpow_one, zpow_zero, mul_one] at hq
    change (v : F.X.carrier → ℂ → ℂ) p c / (q₀ p c)^2 =
      (v : F.X.carrier → ℂ → ℂ) x z / (q₀ x z)^2
    rw [hv, hq, mul_pow]
    exact mul_div_mul_right ((v : F.X.carrier → ℂ → ℂ) x z) ((q₀ x z)^2)
      (pow_ne_zero 2 hd)
  have he : ∀ x, (g ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 (chartAt ℂ x x)]
      (fun z => (v : F.X.carrier → ℂ → ℂ) x z / (q₀ x z)^2) := by
    intro x
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with z hz
    exact hrep x z hz
  have hg : Jacobians.IsMeromorphic F.X.carrier g := by
    intro x
    exact (((hlocal x).1).div ((hmero x).pow 2)).congr
      ((he x).filter_mono nhdsWithin_le_nhds).symm
  let f : Jacobians.MeromorphicFunction F.X.carrier := ⟨g, hg⟩
  refine ⟨f, ?_, ?_⟩
  · intro x
    change ((-((2 • K + E) x) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)
    rw [meromorphicOrderAt_congr ((he x).filter_mono nhdsWithin_le_nhds)]
    change ((-((2 • K + E) x) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt ((v : F.X.carrier → ℂ → ℂ) x / (q₀ x)^2) (chartAt ℂ x x)
    rw [meromorphicOrderAt_div (hlocal x).1 ((hmero x).pow 2)]
    have hden : meromorphicOrderAt ((q₀ x)^2) (chartAt ℂ x x) =
        (((2 • K) x : ℤ) : WithTop ℤ) := by
      rw [meromorphicOrderAt_pow (hmero x), ← horder x]
      norm_cast <;> simp only [two_smul, Finsupp.add_apply, two_mul]
    rw [hden, sub_eq_add_neg]
    have hbase : ((-((2 • K + E) x) : ℤ) : WithTop ℤ) =
        ((-E x : ℤ) : WithTop ℤ) + (-(((2 • K) x : ℤ) : WithTop ℤ)) := by
      rw [← WithTop.LinearOrderedAddCommGroup.coe_neg,
        ← WithTop.coe_add (-E x) (-((2 • K) x))]
      congr 1
      rw [Finsupp.add_apply]
      ring
    rw [hbase]
    exact add_le_add_left (hlocal x).2 _
  · intro x
    have hqne : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), q₀ x z ≠ 0 := by
      apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero x)).mp
      rw [← horder x]
      exact WithTop.coe_ne_top
    -- Reconstruction uses finite canonical order only off the centre; no zero is cancelled there.
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x))),
      hqne] with z hz hqz
    change (v : F.X.carrier → ℂ → ℂ) x z = g ((chartAt ℂ x).symm z) * (q₀ x z)^2
    rw [hrep x z hz]
    exact (div_mul_cancel₀ _ (pow_ne_zero 2 hqz)).symm

/-- Proposed interface: unique regularization is complex linear on actual scalar
representatives. Its formula records the intended geometric map. -/
theorem k31p_regularize_linearMap [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) {K : Divisor F.X.carrier}
    (q₀ : F.X.carrier → ℂ → ℂ) (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) = meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (E : Divisor F.X.carrier) (hEP : ∀ x ∈ F.P, E x = 1)
    (hE0 : ∀ x ∉ F.P, E x = 0) :
    ∃ L : ↥(Jacobians.linearSystem (X := F.X.carrier) (2 • K + E)) →ₗ[ℂ]
        Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)),
      ∀ f x, (L f : F.X.carrier → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
        (fun z => f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) := by
  classical
  have hreg := fun (f : Jacobians.linearSystem (X := F.X.carrier) (2 • K + E)) =>
    k31p_regularize F q₀ hfamily hmero horder E hEP hE0 f.1 f.2
  let A : Jacobians.linearSystem (X := F.X.carrier) (2 • K + E) →
      Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)) :=
    fun f => Classical.choose (hreg f).exists
  have hA : ∀ f x, (A f : F.X.carrier → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      (fun z => f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2) :=
    fun f => Classical.choose_spec (hreg f).exists
  let L : Jacobians.linearSystem (X := F.X.carrier) (2 • K + E) →ₗ[ℂ]
      Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)) :=
    { toFun := A
      map_add' := by
        intro f g
        apply (hreg (f + g)).unique (hA (f + g))
        intro x
        filter_upwards [hA f x, hA g x] with z hzf hzg
        change (A f : F.X.carrier → ℂ → ℂ) x z +
            (A g : F.X.carrier → ℂ → ℂ) x z =
          (f.1.toFun ((chartAt ℂ x).symm z) +
            g.1.toFun ((chartAt ℂ x).symm z)) * (q₀ x z)^2
        rw [hzf, hzg]
        ring
      map_smul' := by
        intro c f
        apply (hreg (c • f)).unique (hA (c • f))
        intro x
        filter_upwards [hA f x] with z hz
        change c * (A f : F.X.carrier → ℂ → ℂ) x z =
          (c * f.1.toFun ((chartAt ℂ x).symm z)) * (q₀ x z)^2
        rw [hz]
        ring }
  exact ⟨L, hA⟩

/-- Proposed interface: the geometric regularization kills exactly germ-zero
representatives and reaches every actual admissible family. -/
theorem k31p_regularize_kernel_surjective [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] (F : FiniteTypeStructure S g n 0)
    {K : Divisor F.X.carrier} (q₀ : F.X.carrier → ℂ → ℂ)
    (hfamily : IsDiffFamily 1 0 q₀)
    (hmero : ∀ x, MeromorphicAt (q₀ x) (chartAt ℂ x x))
    (horder : ∀ x, (K x : WithTop ℤ) = meromorphicOrderAt (q₀ x) (chartAt ℂ x x))
    (E : Divisor F.X.carrier) (hEP : ∀ x ∈ F.P, E x = 1)
    (hE0 : ∀ x ∉ F.P, E x = 0)
    (L : ↥(Jacobians.linearSystem (X := F.X.carrier) (2 • K + E)) →ₗ[ℂ]
      Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ)))
    (hL : ∀ f x, (L f : F.X.carrier → ℂ → ℂ) x =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      (fun z => f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2)) :
    LinearMap.ker L =
        (Jacobians.germZeroSubmodule (X := F.X.carrier)).submoduleOf
          (Jacobians.linearSystem (X := F.X.carrier) (2 • K + E)) ∧
      Function.Surjective L := by
  constructor
  · ext f
    change L f = 0 ↔ ∀ x, f.1.orderW x = ⊤
    constructor
    · intro hf x
      have hprod := hL f x
      rw [hf] at hprod
      have hqne : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x), q₀ x z ≠ 0 := by
        apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero x)).mp
        rw [← horder x]
        exact WithTop.coe_ne_top
      change meromorphicOrderAt (f.1.toFun ∘ (chartAt ℂ x).symm)
        (chartAt ℂ x x) = ⊤
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [hprod, hqne] with z hz hqz
      change f.1.toFun ((chartAt ℂ x).symm z) = 0
      change 0 = f.1.toFun ((chartAt ℂ x).symm z) * (q₀ x z)^2 at hz
      exact (mul_eq_zero.mp hz.symm).resolve_right (pow_ne_zero 2 hqz)
    · intro hf
      apply Subtype.ext
      apply k31p_admissible_ext F
        ((k31p_complex_carrier F _).mp (L f).property)
        (admissibleQDSpace F).zero_mem
      intro x
      have hfx := hf x
      change meromorphicOrderAt (f.1.toFun ∘ (chartAt ℂ x).symm)
        (chartAt ℂ x x) = ⊤ at hfx
      have hzero : ∀ᶠ z in 𝓝[≠] (chartAt ℂ x x),
          f.1.toFun ((chartAt ℂ x).symm z) = 0 :=
        meromorphicOrderAt_eq_top_iff.mp hfx
      filter_upwards [hL f x, hzero] with z hz hz0
      change (L f : F.X.carrier → ℂ → ℂ) x z = 0
      rw [hz, hz0, zero_mul]
  · intro v
    obtain ⟨f, hf, hdiv⟩ := k31p_division F q₀ hfamily hmero horder E hEP hE0 v
    refine ⟨⟨f, hf⟩, ?_⟩
    exact (k31p_regularize F q₀ hfamily hmero horder E hEP hE0 f hf).unique
      (hL ⟨f, hf⟩) hdiv

/-- Proposed interface: descend the actual geometric linear map through its
germ-zero quotient and the installed mkQ-compatible scalar equivalence. -/
theorem k31p_quotient_equiv [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) {K : Divisor F.X.carrier}
    (hK : IsCanonicalDivisor K) (E : Divisor F.X.carrier)
    (hEP : ∀ x ∈ F.P, E x = 1) (hE0 : ∀ x ∉ F.P, E x = 0) :
    Nonempty
      (meroFunctionSpace (2 • K + E) ≃ₗ[ℂ]
        Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ))) := by
  classical
  obtain ⟨q₀, hfamily, hmero, horder⟩ := hK
  obtain ⟨L, hL⟩ :=
    k31p_regularize_linearMap F (K := K) q₀ hfamily hmero horder E hEP hE0
  obtain ⟨hker, hsurj⟩ :=
    k31p_regularize_kernel_surjective F (K := K) q₀ hfamily hmero horder E hEP hE0 L hL
  obtain ⟨eScalar, _hScalar_mkQ⟩ :=
    k22q_quotient_equiv_mkQ (S := F.X.carrier) (2 • K + E)
  exact ⟨eScalar.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (L.quotKerEquivOfSurjective hsurj))⟩

/-- Proposed interface: nonexceptionality makes the dual divisor's degree strictly
negative for all genera, including punctured genus zero and one. -/
theorem k31p_dual_degree_neg [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) (hex : ¬ IsExceptionalType g n 0)
    {K : Divisor F.X.carrier} (hK : IsCanonicalDivisor K)
    (E : Divisor F.X.carrier) (hdeg : E.deg = n) : (-K - E).deg < 0 := by
  have hstable : 2 < 2 * g + n := by
    by_contra hbad
    have hcases : (g = 0 ∧ n = 0) ∨ (g = 0 ∧ n = 1) ∨
        (g = 0 ∧ n = 2) ∨ (g = 1 ∧ n = 0) := by omega
    rcases hcases with ⟨hg, hn⟩ | ⟨hg, hn⟩ | ⟨hg, hn⟩ | ⟨hg, hn⟩
    · exact hex (Or.inl (by rw [hg, hn]))
    · exact hex (Or.inr (Or.inl (by rw [hg, hn])))
    · exact hex (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hg, hn])))))
    · exact hex (Or.inr (Or.inr (Or.inl (by rw [hg, hn]))))
  have hKdeg := deg_canonical F.genus hK
  change Jacobians.Divisor.deg F.X.carrier (-K - E) < 0
  rw [map_sub, map_neg, k22rr_degree_eq K, k22rr_degree_eq E, hKdeg, hdeg]
  omega

/-- Proposed interface: scalar Riemann--Roch with the shifted divisor, using
negative-degree vanishing of the dual system. -/
theorem k31p_ell_dimension [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) (hex : ¬ IsExceptionalType g n 0)
    {K : Divisor F.X.carrier} (hK : IsCanonicalDivisor K)
    (E : Divisor F.X.carrier) (hdeg : E.deg = n) :
    (ellDim (2 • K + E) : ℤ) = 3 * (g : ℤ) - 3 + n := by
  have hnegdeg := k31p_dual_degree_neg F hex hK E hdeg
  have hneg : ellDim (-K - E) = 0 := by
    rw [k22rr_ellDim_eq_lDim]
    apply Jacobians.lDim_eq_zero_of_deg_neg
    simpa only [k22rr_degree_eq] using hnegdeg
  have hsub : K - (2 • K + E) = -K - E := by
    simp only [two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hdegshift : (2 • K + E).deg = 2 * K.deg + E.deg := by
    change Jacobians.Divisor.deg F.X.carrier (2 • K + E) =
      2 * Jacobians.Divisor.deg F.X.carrier K +
        Jacobians.Divisor.deg F.X.carrier E
    rw [map_add, map_nsmul]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  have hKdeg := deg_canonical F.genus hK
  have hRR := thm22_4_riemann_roch F.genus hK (2 • K + E)
  rw [hsub, hneg, hdegshift, hKdeg, hdeg] at hRR
  omega

/-- Proposed assembly from the preceding equivalence and the already installed
finite-dimensional scalar system; this is still an unverified interface proof. -/
theorem k31p_finite_admissible [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) :
    FiniteDimensional ℂ
      (Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ))) := by
  obtain ⟨E, hEP, hE0, _hdeg⟩ := k31p_puncture_divisor F
  obtain ⟨K, hK⟩ := k22q_canonical_exists (S := F.X.carrier)
  obtain ⟨e⟩ := k31p_quotient_equiv F hK E hEP hE0
  letI : FiniteDimensional ℂ (meroFunctionSpace (2 • K + E)) :=
    k22q_finite_mero (2 • K + E)
  exact e.finiteDimensional


/-- §31.2: for `m = 0` (no holes) the admissible differentials also form a complex vector space,
of complex dimension `3g - 3 + n` (Riemann–Roch, as for compact surfaces). -/
theorem admissibleQD_complex_finrank [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) (hex : ¬ IsExceptionalType g n 0) :
    (∀ (c : ℂ) (q : F.X.carrier → ℂ → ℂ), IsAdmissibleQD F q → IsAdmissibleQD F (c • q)) ∧
      (Module.finrank ℝ (admissibleQDSpace F) : ℤ) = 2 * (3 * g - 3 + n) := by
  classical
  refine ⟨k31p_complex_smul F, ?_⟩
  let Q := Submodule.span ℂ (admissibleQDSpace F : Set (F.X.carrier → ℂ → ℂ))
  letI : FiniteDimensional ℂ Q := k31p_finite_admissible F
  obtain ⟨E, hEP, hE0, hdeg⟩ := k31p_puncture_divisor F
  obtain ⟨K, hK⟩ := k22q_canonical_exists (S := F.X.carrier)
  obtain ⟨eC⟩ := k31p_quotient_equiv F hK E hEP hE0
  obtain ⟨eR⟩ := k31p_real_equiv F
  have hC : ellDim (2 • K + E) = Module.finrank ℂ Q := eC.finrank_eq
  have hR : Module.finrank ℝ Q = Module.finrank ℝ (admissibleQDSpace F) := eR.finrank_eq
  have hd := k31p_ell_dimension F hex hK E hdeg
  rw [← hR, finrank_real_of_complex, ← hC]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    congrArg (fun d : ℤ => 2 * d) hd

/-- §31.2: an admissible differential has at most one horizontal trajectory ending at a puncture
where it has a simple pole, and the non-puncture boundary curves consist of horizontal and vertical
trajectory arcs of `q` (as `q dz²` is real along them).

**Gap (2026-09-27).**  Only the boundary half is formalized, and only pointwise: at each regular point
of a boundary curve where `q ≠ 0`, `q c'²` is real and non-zero, so the direction there is horizontal or
vertical; the statement at a simple pole ("at most one horizontal trajectory ends there") is not
formalized, and "arcs" (a constant sign along each arc) is not stated.  **Correction (2026-09-27).**
`hsub` uses `(chartAt ℂ x).symm ⁻¹'` in place of the chart image, following `IsAdmissibleQD`. -/
theorem admissibleQD_boundary_trajectories [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) {q : F.X.carrier → ℂ → ℂ} (hq : IsAdmissibleQD F q) (x : F.X.carrier)
    (j : Fin m) (c : ℝ → ℂ) (a b : ℝ) (hc : ContDiffOn ℝ 1 c (Icc a b)) (hc' : ∀ t ∈ Ioo a b, deriv c t ≠ 0)
    (hsub : c '' Icc a b ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' frontier (F.D j))
    (hne : ∀ t ∈ Ioo a b, q x (c t) ≠ 0) :
    ∀ t ∈ Ioo a b, 0 < (q x (c t) * deriv c t ^ 2).re ∨ (q x (c t) * deriv c t ^ 2).re < 0 := by
  intro t ht
  have him : (q x (c t) * deriv c t ^ 2).im = 0 := hq.2.2.2.2.1 x j c a b hc hsub t ht
  have hne' : q x (c t) * deriv c t ^ 2 ≠ 0 := mul_ne_zero (hne t ht) (pow_ne_zero 2 (hc' t ht))
  rcases lt_trichotomy (q x (c t) * deriv c t ^ 2).re 0 with h | h | h
  · exact Or.inr h
  · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hne'
  · exact Or.inl h

/-! §31.2 (symmetric extension).  The reflection extension of an admissible quadratic differential to the Schottky double is proved in LiZhongQC/Lemmas/QDSymmetricExtension.lean, which needs the double machinery developed after this file. -/

/-- (31.1): the double `S^d` is of type `(2g + m - 1, 2n, 0)`, so
`dim_ℝ Q̃(S^d) = 12g + 6m - 12 + 4n = 2(6g - 6 + 2n + 3m)`. -/
theorem eq31_1_double_finrank [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (Fd : FiniteTypeStructure (puncturedOpens Pd) (2 * g + m - 1) (2 * n) 0) :
    (Module.finrank ℝ (admissibleQDSpace Fd) : ℤ) = 2 * (6 * g - 6 + 2 * n + 3 * m) := by
  classical
  -- The dimension uses Fd's type; hd records its geometric double origin.
  have _h := hd
  letI : Infinite Xd.carrier :=
    Jacobians.Discharge.ContMDiff.Degree.infinite_of_chartedSpace_complex
  obtain ⟨x, hx⟩ := Pd.exists_notMem
  have hne : ((↑Pd : Set Xd.carrier)ᶜ).Nonempty :=
    ⟨x, by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hx⟩
  have hc : IsConnected ((↑Pd : Set Xd.carrier)ᶜ) :=
    (Jacobians.Discharge.Manifold.isPathConnected_compl_finite_of_connected_chartedSpace_complex
      Pd.finite_toSet hne).isConnected
  letI : ConnectedSpace (puncturedOpens Pd) := Subtype.connectedSpace hc
  have hexd : ¬ IsExceptionalType (2 * g + m - 1) (2 * n) 0 := by
    intro h
    unfold IsExceptionalType at h
    rcases h with h | h | h | h | h | h | h
    · have hgd : 2 * g + m - 1 = 0 := congrArg Prod.fst h
      have hnd : 2 * n = 0 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
      have hg0 : g = 0 := by omega
      have hn0 : n = 0 := by omega
      have hm1 : m = 1 := by omega
      exact hex (by simp [IsExceptionalType, hg0, hn0, hm1])
    · have hnd : 2 * n = 1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
      omega
    · have hgd : 2 * g + m - 1 = 1 := congrArg Prod.fst h
      have hnd : 2 * n = 0 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
      have hg0 : g = 0 := by omega
      have hn0 : n = 0 := by omega
      have hm2 : m = 2 := by omega
      exact hex (by simp [IsExceptionalType, hg0, hn0, hm2])
    · have hgd : 2 * g + m - 1 = 0 := congrArg Prod.fst h
      have hnd : 2 * n = 2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
      have hg0 : g = 0 := by omega
      have hn1 : n = 1 := by omega
      have hm1 : m = 1 := by omega
      exact hex (by simp [IsExceptionalType, hg0, hn1, hm1])
    · have hmd : (0 : ℕ) = 1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
      omega
    · have hmd : (0 : ℕ) = 1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
      omega
    · have hmd : (0 : ℕ) = 2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
      omega
  have hle : 1 ≤ 2 * g + m := by omega
  have hdim := (admissibleQD_complex_finrank Fd hexd).2
  calc
    (Module.finrank ℝ (admissibleQDSpace Fd) : ℤ) =
        2 * (3 * (2 * (g : ℤ) + (m : ℤ) - 1) - 3 + 2 * (n : ℤ)) := by
      simpa only [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one] using hdim
    _ = 2 * (6 * g - 6 + 2 * n + 3 * m) := by ring

/-! §31.2 (decomposition).  The reflection of the admissible differentials of the double and the splitting into symmetric and anti-symmetric parts are proved in LiZhongQC/Lemmas/QDDoubleDecomposition.lean, which needs the double machinery developed after this file. -/

-- thm31_1_admissibleQD_finrank (Theorem 31.1, (31.2)) is stated and proved in LiZhongQC/Lemmas/QDDimension.lean
-- (it needs the Schottky double and the decomposition of Q̃(S^d)).

end LiZhongQC
