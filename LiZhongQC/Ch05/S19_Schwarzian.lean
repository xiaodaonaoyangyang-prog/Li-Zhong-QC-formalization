import LiZhongQC.Ch03.S14_PoincareMetric
import LiZhongQC.Lemmas.DiscAutomorphism
import LiZhongQC.Lemmas.KrausNehari

/-!
# §19 Schwarz 导数与 Nehari 定理 — The Schwarzian derivative and Nehari's theorem

* §19.1 the Schwarzian derivative of a meromorphic function   — `schwarzianHol`, `schwarzian`
* Möbius transformations have vanishing Schwarzian; chain rule (19.1)
* Theorem 19.1 (existence and uniqueness up to Möbius transformations) — `thm19_1_*`
* Theorem 19.2 (Nehari–Kraus: `|S_f(z)|(1 - |z|²)² ≤ 6`)     — `thm19_2_nehari`
* §19.3 the norm `‖S_f‖_D` (19.4), (19.5), the outer radius of univalence `σ₂(D)`,
  `σ₁(D)`, Theorem 19.3 (`σ₂ = 3/2 + σ₁`) and its corollary `σ₂ ≤ 3`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- The Schwarzian derivative `S_f = (f''/f')' - ½(f''/f')²` of a function holomorphic near `z`. -/
def schwarzianHol (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (fun w => deriv (deriv f) w / deriv f w) z - (1 / 2) * (deriv (deriv f) z / deriv f z) ^ 2

open scoped Classical in
/-- §19.1: the Schwarzian derivative of a meromorphic function; at a pole `z` it is defined as
`S_{1/f}(z)` (using the normal form of `f` at `z`, whose value at a pole is `0`).

The branch is taken on the *order* of the germ, and both branches use the normal form.  Testing
`AnalyticAt f z` instead would be wrong: a germ with a removable singularity at `z` but the
"wrong" value `f z` is not `AnalyticAt`, yet must not be sent to the pole branch — its normal
form can vanish at `z`, and then the reciprocal is singular and `schwarzianHol` returns junk.
Branching on the order makes `schwarzian f z` depend only on the germ of `f` on a punctured
neighbourhood of `z` (`schwarzian_congr`), and agrees with the naive definition whenever `f` is
already in normal form at `z` — in particular whenever `f` is analytic at `z`. -/
def schwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 ≤ meromorphicOrderAt f z then schwarzianHol (toMeromorphicNFAt f z) z
  else schwarzianHol (fun w => (toMeromorphicNFAt f z w)⁻¹) z

/-- On an analytic germ the Schwarzian is the naive holomorphic one. -/
theorem schwarzian_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    schwarzian f z = schwarzianHol f z := by
  unfold schwarzian
  rw [if_pos hf.meromorphicOrderAt_nonneg, toMeromorphicNFAt_eq_self.mpr hf.meromorphicNFAt]

/-- At a pole the Schwarzian is that of `1/f`, computed in normal form. -/
theorem schwarzian_of_order_neg {f : ℂ → ℂ} {z : ℂ} (hf : meromorphicOrderAt f z < 0) :
    schwarzian f z = schwarzianHol (fun w => (toMeromorphicNFAt f z w)⁻¹) z := by
  unfold schwarzian
  rw [if_neg (not_le.mpr hf)]

/-- `f` is a locally univalent meromorphic function on `D`: at every point of `D` either `f` is
holomorphic with `f' ≠ 0`, or `f` has a simple pole (`1/f` is holomorphic with non-zero
derivative).

The pole is detected by `meromorphicOrderAt f z < 0`, **not** by `¬ AnalyticAt ℂ f z`.  A Lean
function can fail `AnalyticAt` at a removable singularity merely by carrying a wrong value there;
with `¬ AnalyticAt` such points were classified as poles, and two of them made `IsUnivMero` fail
(its pole set is required to be a subsingleton) for a function whose germ is the identity.  That
made `IsSchwarzDomain unitDisc a` false for every `a > 0` — see the README Corrections. -/
def IsLocUnivMero (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  MeromorphicOn f D ∧ ∀ z ∈ D, (AnalyticAt ℂ f z ∧ deriv f z ≠ 0) ∨
    (meromorphicOrderAt f z < 0 ∧ AnalyticAt ℂ (fun w => (toMeromorphicNFAt f z w)⁻¹) z ∧
      deriv (fun w => (toMeromorphicNFAt f z w)⁻¹) z ≠ 0)

/-- `f` is a univalent (injective) meromorphic function on `D`: locally univalent, injective at
its holomorphic points, with at most one pole. -/
def IsUnivMero (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  IsLocUnivMero f D ∧ InjOn f {z ∈ D | AnalyticAt ℂ f z} ∧
    {z ∈ D | ¬ AnalyticAt ℂ f z}.Subsingleton

/-! ### The Schwarzian of a fractional linear transformation -/

/-- The derivative of a fractional linear map away from its pole. -/
theorem hasDerivAt_mobius {a b c d : ℂ} {w : ℂ} (hw : c * w + d ≠ 0) :
    HasDerivAt (fun v => (a * v + b) / (c * v + d)) ((a * d - b * c) / (c * w + d) ^ 2) w := by
  have hn : HasDerivAt (fun v : ℂ => a * v + b) a w := by
    simpa using ((hasDerivAt_id w).const_mul a).add_const b
  have hd : HasDerivAt (fun v : ℂ => c * v + d) c w := by
    simpa using ((hasDerivAt_id w).const_mul c).add_const d
  have e : a * d - b * c = a * (c * w + d) - (a * w + b) * c := by ring
  rw [e]
  exact hn.div hd hw

/-- The derivative of `(ad - bc)/(cv + d)²`, the first derivative of a fractional linear map. -/
theorem hasDerivAt_mobius_deriv {a b c d : ℂ} {w : ℂ} (hw : c * w + d ≠ 0) :
    HasDerivAt (fun v => (a * d - b * c) / (c * v + d) ^ 2)
      (-(2 * c * (a * d - b * c)) / (c * w + d) ^ 3) w := by
  have hd : HasDerivAt (fun v : ℂ => c * v + d) c w := by
    simpa using ((hasDerivAt_id w).const_mul c).add_const d
  have hp : HasDerivAt (fun v : ℂ => (c * v + d) ^ 2) (2 * (c * w + d) ^ 1 * c) w := hd.pow 2
  have hq := (hasDerivAt_const w (a * d - b * c)).div hp (pow_ne_zero 2 hw)
  convert hq using 1
  field_simp
  ring

/-- The derivative of `-2c/(cv + d)`, the logarithmic derivative `f''/f'` of a fractional linear
map. -/
theorem hasDerivAt_mobius_logDeriv {c d : ℂ} {w : ℂ} (hw : c * w + d ≠ 0) :
    HasDerivAt (fun v => -(2 * c) / (c * v + d)) (2 * c ^ 2 / (c * w + d) ^ 2) w := by
  have hd : HasDerivAt (fun v : ℂ => c * v + d) c w := by
    simpa using ((hasDerivAt_id w).const_mul c).add_const d
  have hq := (hasDerivAt_const w (-(2 * c))).div hd hw
  convert hq using 1
  field_simp
  ring

/-- §19.1: the Schwarzian derivative of a fractional linear transformation vanishes away from its
pole. -/
theorem schwarzianHol_mobius {a b c d : ℂ} (h : a * d - b * c ≠ 0) {z : ℂ}
    (hz : c * z + d ≠ 0) : schwarzianHol (fun w => (a * w + b) / (c * w + d)) z = 0 := by
  set f : ℂ → ℂ := fun w => (a * w + b) / (c * w + d) with hf_def
  have hopen : IsOpen {w : ℂ | c * w + d ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hnhds : {w : ℂ | c * w + d ≠ 0} ∈ 𝓝 z := hopen.mem_nhds hz
  -- the first derivative
  have hd1 : deriv f =ᶠ[𝓝 z] fun w => (a * d - b * c) / (c * w + d) ^ 2 := by
    filter_upwards [hnhds] with w hw
    exact (hasDerivAt_mobius hw).deriv
  -- the second derivative
  have hd2 : deriv (deriv f) =ᶠ[𝓝 z] fun w => -(2 * c * (a * d - b * c)) / (c * w + d) ^ 3 := by
    filter_upwards [hnhds, hd1.eventually_nhds] with w hw hev
    have hev' : deriv f =ᶠ[𝓝 w] fun v => (a * d - b * c) / (c * v + d) ^ 2 := hev
    rw [hev'.deriv_eq]
    exact (hasDerivAt_mobius_deriv hw).deriv
  -- the logarithmic derivative `f''/f'`
  have hq : (fun w => deriv (deriv f) w / deriv f w) =ᶠ[𝓝 z] fun w => -(2 * c) / (c * w + d) := by
    filter_upwards [hnhds, hd1, hd2] with w hw e1 e2
    have hne : (a * d - b * c) / (c * w + d) ^ 2 ≠ 0 := div_ne_zero h (pow_ne_zero 2 hw)
    rw [e1, e2, show -(2 * c * (a * d - b * c)) / (c * w + d) ^ 3
        = -(2 * c) / (c * w + d) * ((a * d - b * c) / (c * w + d) ^ 2) by field_simp,
      mul_div_cancel_right₀ _ hne]
  have hd3 : deriv (fun w => deriv (deriv f) w / deriv f w) z = 2 * c ^ 2 / (c * z + d) ^ 2 := by
    rw [hq.deriv_eq]
    exact (hasDerivAt_mobius_logDeriv hz).deriv
  have hval : deriv (deriv f) z / deriv f z = -(2 * c) / (c * z + d) := hq.self_of_nhds
  unfold schwarzianHol
  rw [hd3, hval]
  field_simp
  ring

/-- `schwarzianHol` depends only on the germ of the function at the point. -/
theorem schwarzianHol_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    schwarzianHol f z = schwarzianHol g z := by
  have h1 : deriv f =ᶠ[𝓝 z] deriv g := h.deriv
  have h2 : deriv (deriv f) =ᶠ[𝓝 z] deriv (deriv g) := h1.deriv
  have h3 : (fun w => deriv (deriv f) w / deriv f w)
      =ᶠ[𝓝 z] fun w => deriv (deriv g) w / deriv g w := by
    filter_upwards [h1, h2] with w e1 e2
    rw [e1, e2]
  unfold schwarzianHol
  rw [h3.deriv_eq, h1.self_of_nhds, h2.self_of_nhds]

/-- The normal form at `z` depends only on the germ of `f` on a punctured neighbourhood of `z`
(this is Mathlib's local identity theorem for functions in normal form). -/
theorem toMeromorphicNFAt_congr_nhdsNE {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝[≠] z] g) :
    toMeromorphicNFAt f z =ᶠ[𝓝 z] toMeromorphicNFAt g z := by
  refine (meromorphicNFAt_toMeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    meromorphicNFAt_toMeromorphicNFAt).mp ?_
  by_cases hf : MeromorphicAt f z
  · exact (hf.eq_nhdsNE_toMeromorphicNFAt.symm.trans h).trans (hf.congr h).eq_nhdsNE_toMeromorphicNFAt
  · have hg : ¬ MeromorphicAt g z := fun hg => hf (hg.congr h.symm)
    rw [toMeromorphicNFAt_of_not_meromorphicAt hf, toMeromorphicNFAt_of_not_meromorphicAt hg]

/-- `schwarzian` depends only on the germ of the function on a punctured neighbourhood. -/
theorem schwarzian_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝[≠] z] g) :
    schwarzian f z = schwarzian g z := by
  have hNF := toMeromorphicNFAt_congr_nhdsNE h
  unfold schwarzian
  rw [meromorphicOrderAt_congr h]
  split_ifs
  · exact schwarzianHol_congr hNF
  · exact schwarzianHol_congr (hNF.mono fun w hw => congrArg Inv.inv hw)

/-- At the pole of a fractional linear map, no function agreeing with it off the pole can be
continuous: `g(w)(cw + d) = aw + b` off the pole, and the two sides have different limits. -/
theorem not_continuousAt_mobius_pole {a b c d : ℂ} {z : ℂ} (hc : c ≠ 0) (hz : c * z + d = 0)
    (hab : a * z + b ≠ 0) {g : ℂ → ℂ}
    (hg : g =ᶠ[𝓝[≠] z] fun w => (a * w + b) / (c * w + d)) : ¬ ContinuousAt g z := by
  intro hcont
  have hcne : ∀ᶠ w in 𝓝[≠] z, c * w + d ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw hcon
    refine hw (sub_eq_zero.mp ?_)
    have h0 : c * (w - z) = 0 := by linear_combination hcon - hz
    exact (mul_eq_zero.mp h0).resolve_left hc
  have h1 : Tendsto (fun w => g w * (c * w + d)) (𝓝[≠] z) (𝓝 0) := by
    have hmul : ContinuousAt (fun w : ℂ => g w * (c * w + d)) z := hcont.mul (by fun_prop)
    have h1a : Tendsto (fun w => g w * (c * w + d)) (𝓝[≠] z) (𝓝 (g z * (c * z + d))) :=
      hmul.tendsto.mono_left nhdsWithin_le_nhds
    simpa [hz] using h1a
  have h2 : Tendsto (fun w => g w * (c * w + d)) (𝓝[≠] z) (𝓝 (a * z + b)) := by
    refine Tendsto.congr' ?_
      ((by fun_prop : Continuous fun w : ℂ => a * w + b).continuousAt.continuousWithinAt)
    filter_upwards [hg, hcne] with w e hcw
    rw [e, div_mul_cancel₀ _ hcw]
  exact hab (tendsto_nhds_unique h2 h1)

/-- §19.1: the Schwarzian derivative of a fractional linear transformation vanishes. -/
theorem schwarzian_mobius {a b c d : ℂ} (h : a * d - b * c ≠ 0) (z : ℂ) :
    schwarzian (fun w => (a * w + b) / (c * w + d)) z = 0 := by
  by_cases hz : c * z + d = 0
  · -- `z` is the pole; the Schwarzian is that of `1/f` in normal form
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_mul, zero_add] at hz
      subst hz
      simp at h
    have hab : a * z + b ≠ 0 := fun hcon => h (by linear_combination a * hz - c * hcon)
    have hmero : MeromorphicAt (fun w : ℂ => (a * w + b) / (c * w + d)) z := by fun_prop
    have hFeq := hmero.eq_nhdsNE_toMeromorphicNFAt
    -- the normal form is not analytic at the pole, so the germ has negative order
    have hnotAN : ¬ AnalyticAt ℂ
        (toMeromorphicNFAt (fun w : ℂ => (a * w + b) / (c * w + d)) z) z := fun hA =>
      not_continuousAt_mobius_pole hc hz hab hFeq.symm hA.continuousAt
    have horder : meromorphicOrderAt (fun w : ℂ => (a * w + b) / (c * w + d)) z < 0 := by
      rw [meromorphicOrderAt_congr hFeq]
      exact not_le.mp fun hle => hnotAN
        (meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mp hle)
    -- the normal form takes the value `0` at the pole
    have hF0 : toMeromorphicNFAt (fun w : ℂ => (a * w + b) / (c * w + d)) z z = 0 := by
      rcases meromorphicNFAt_iff_analyticAt_or.mp
        (meromorphicNFAt_toMeromorphicNFAt (f := fun w : ℂ => (a * w + b) / (c * w + d))
          (x := z)) with
        hA | ⟨-, -, h0⟩
      · exact absurd hA hnotAN
      · exact h0
    -- so `1/F` is the fractional linear map `(cw + d)/(aw + b)` near `z`
    have hgerm : (fun w => (toMeromorphicNFAt (fun w : ℂ => (a * w + b) / (c * w + d)) z w)⁻¹)
        =ᶠ[𝓝 z] fun w => (c * w + d) / (a * w + b) := by
      have hp := eventually_nhdsWithin_iff.mp
        (show ∀ᶠ w in 𝓝[≠] z,
            (toMeromorphicNFAt (fun w : ℂ => (a * w + b) / (c * w + d)) z w)⁻¹
              = (c * w + d) / (a * w + b) by
          filter_upwards [hFeq] with w e
          rw [← e, inv_div])
      filter_upwards [hp] with w hw
      by_cases hwz : w = z
      · subst hwz
        rw [hF0, inv_zero, hz, zero_div]
      · exact hw hwz
    rw [schwarzian_of_order_neg horder, schwarzianHol_congr hgerm]
    exact schwarzianHol_mobius (fun hcon => h (by linear_combination -hcon)) hab
  · -- `z` is not the pole
    have hA : AnalyticAt ℂ (fun w : ℂ => (a * w + b) / (c * w + d)) z :=
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ => a * w + b) z).div
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ => c * w + d) z) hz
    rw [schwarzian_of_analyticAt hA]
    exact schwarzianHol_mobius h hz

/-- The chain rule (19.1): `S_{f∘g} = (S_f ∘ g) g'² + S_g`. -/
theorem eq19_1_chain_rule {f g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) (hg' : deriv g z ≠ 0)
    (hf : AnalyticAt ℂ f (g z)) (hf' : deriv f (g z) ≠ 0) :
    schwarzian (f ∘ g) z = schwarzian f (g z) * deriv g z ^ 2 + schwarzian g z := by
  have hgc : ContinuousAt g z := hg.continuousAt
  -- everything stays analytic, and the derivatives stay non-zero, near `z`
  have hgA : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ g w := hg.eventually_analyticAt
  have hgD : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (deriv g) w := hg.deriv.eventually_analyticAt
  have hgne : ∀ᶠ w in 𝓝 z, deriv g w ≠ 0 := hg.deriv.continuousAt.eventually_ne hg'
  have hfA : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ f (g w) := hgc.eventually hf.eventually_analyticAt
  have hfD : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (deriv f) (g w) :=
    hgc.eventually hf.deriv.eventually_analyticAt
  have hfne : ∀ᶠ w in 𝓝 z, deriv f (g w) ≠ 0 :=
    hgc.eventually (hf.deriv.continuousAt.eventually_ne hf')
  -- the first two derivatives of the composite
  have hd1 : deriv (f ∘ g) =ᶠ[𝓝 z] fun w => deriv f (g w) * deriv g w := by
    filter_upwards [hgA, hfA] with w hgw hfw
    exact deriv_comp w hfw.differentiableAt hgw.differentiableAt
  have hd2 : deriv (deriv (f ∘ g)) =ᶠ[𝓝 z]
      fun w => deriv (deriv f) (g w) * deriv g w ^ 2 + deriv f (g w) * deriv (deriv g) w := by
    filter_upwards [hgA, hgD, hfD, hd1.eventually_nhds] with w hgw hgdw hfdw hev
    have hev' : deriv (f ∘ g) =ᶠ[𝓝 w] fun v => deriv f (g v) * deriv g v := hev
    rw [hev'.deriv_eq]
    have h1 : HasDerivAt (fun v => deriv f (g v)) (deriv (deriv f) (g w) * deriv g w) w :=
      hfdw.differentiableAt.hasDerivAt.comp w hgw.differentiableAt.hasDerivAt
    have h2 : HasDerivAt (deriv g) (deriv (deriv g) w) w := hgdw.differentiableAt.hasDerivAt
    convert (h1.mul h2).deriv using 1
    ring
  -- the logarithmic derivative of the composite
  have hlog : (fun w => deriv (deriv (f ∘ g)) w / deriv (f ∘ g) w) =ᶠ[𝓝 z]
      fun w => deriv (deriv f) (g w) / deriv f (g w) * deriv g w
        + deriv (deriv g) w / deriv g w := by
    filter_upwards [hd1, hd2, hgne, hfne] with w e1 e2 hgw hfw
    rw [e1, e2]
    field_simp
  -- differentiate it at `z`
  have hu : DifferentiableAt ℂ (fun y => deriv (deriv f) y / deriv f y) (g z) :=
    hf.deriv.deriv.differentiableAt.div hf.deriv.differentiableAt hf'
  have hv : DifferentiableAt ℂ (fun w => deriv (deriv g) w / deriv g w) z :=
    hg.deriv.deriv.differentiableAt.div hg.deriv.differentiableAt hg'
  have hdlog : deriv (fun w => deriv (deriv (f ∘ g)) w / deriv (f ∘ g) w) z
      = deriv (fun y => deriv (deriv f) y / deriv f y) (g z) * deriv g z ^ 2
        + deriv (deriv f) (g z) / deriv f (g z) * deriv (deriv g) z
        + deriv (fun w => deriv (deriv g) w / deriv g w) z := by
    rw [hlog.deriv_eq]
    have hcomp : HasDerivAt (fun w => deriv (deriv f) (g w) / deriv f (g w))
        (deriv (fun y => deriv (deriv f) y / deriv f y) (g z) * deriv g z) z :=
      hu.hasDerivAt.comp z hg.differentiableAt.hasDerivAt
    have hgd : HasDerivAt (deriv g) (deriv (deriv g) z) z := hg.deriv.differentiableAt.hasDerivAt
    convert ((hcomp.mul hgd).add hv.hasDerivAt).deriv using 1
    ring
  have hlogz : deriv (deriv (f ∘ g)) z / deriv (f ∘ g) z
      = deriv (deriv f) (g z) / deriv f (g z) * deriv g z + deriv (deriv g) z / deriv g z :=
    hlog.self_of_nhds
  -- all three Schwarzians are the holomorphic ones
  rw [schwarzian_of_analyticAt (hf.comp hg), schwarzian_of_analyticAt hf,
    schwarzian_of_analyticAt hg]
  unfold schwarzianHol
  rw [hdlog, hlogz]
  field_simp
  ring

/-- Post-composition with a Möbius map, away from its pole: the chain rule (19.1) together with
`schwarzian_mobius` gives `S_{M∘g} = S_g`. -/
theorem schwarzian_mobius_comp_of_ne {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (hg' : deriv g z ≠ 0) {a b c d : ℂ} (h : a * d - b * c ≠ 0) (hden : c * g z + d ≠ 0) :
    schwarzian (fun w => (a * g w + b) / (c * g w + d)) z = schwarzian g z := by
  have hM : AnalyticAt ℂ (fun v : ℂ => (a * v + b) / (c * v + d)) (g z) :=
    (by fun_prop : AnalyticAt ℂ (fun v : ℂ => a * v + b) (g z)).div
      (by fun_prop : AnalyticAt ℂ (fun v : ℂ => c * v + d) (g z)) hden
  have hM' : deriv (fun v : ℂ => (a * v + b) / (c * v + d)) (g z) ≠ 0 := by
    rw [(hasDerivAt_mobius hden).deriv]
    exact div_ne_zero h (pow_ne_zero _ hden)
  have hchain := eq19_1_chain_rule hg hg' hM hM'
  rw [schwarzian_mobius h (g z), zero_mul, zero_add] at hchain
  exact hchain

/-- If `G` is analytic with a simple zero at `z`, then `1/G` has a simple pole there and, by the
definition of the Schwarzian at a pole, the two Schwarzians agree. -/
theorem schwarzian_inv_of_simple_zero {G : ℂ → ℂ} {z : ℂ} (hG : AnalyticAt ℂ G z)
    (hG0 : G z = 0) (hG' : deriv G z ≠ 0) :
    schwarzian (fun w => (G w)⁻¹) z = schwarzian G z := by
  have h1 : meromorphicOrderAt G z = 1 := by
    rw [hG.meromorphicOrderAt_eq, hG.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hG0 hG']
    rfl
  have horder : meromorphicOrderAt (fun w => (G w)⁻¹) z < 0 := by
    have hval : meromorphicOrderAt (fun w => (G w)⁻¹) z = -1 := by
      show meromorphicOrderAt G⁻¹ z = -1
      rw [meromorphicOrderAt_inv, h1]
    rw [hval]
    decide
  rw [schwarzian_of_order_neg horder,
    (toMeromorphicNFAt_eq_self (f := fun w => (G w)⁻¹) (x := z)).mpr hG.meromorphicNFAt.inv,
    schwarzian_of_analyticAt hG]
  simp only [inv_inv]

/-- The Schwarzian is unchanged by `f ↦ 1/f` at a point of local univalence. -/
theorem schwarzian_inv {u : ℂ → ℂ} {z : ℂ} (hu : AnalyticAt ℂ u z) (hu' : deriv u z ≠ 0) :
    schwarzian (fun w => (u w)⁻¹) z = schwarzian u z := by
  rcases eq_or_ne (u z) 0 with h0 | h0
  · exact schwarzian_inv_of_simple_zero hu h0 hu'
  · have hcomp := schwarzian_mobius_comp_of_ne hu hu' (a := 0) (b := 1) (c := 1) (d := 0)
      (by norm_num) (by simpa using h0)
    simpa using hcomp

/-- `schwarzianHol f` is analytic wherever `f` is analytic with non-vanishing derivative:
it is `q' - q²/2` for the analytic function `q = f''/f'`. -/
theorem analyticAt_schwarzianHol {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hf' : deriv f z ≠ 0) : AnalyticAt ℂ (schwarzianHol f) z := by
  have hq : AnalyticAt ℂ (fun w => deriv (deriv f) w / deriv f w) z :=
    hf.deriv.deriv.div hf.deriv hf'
  have h : AnalyticAt ℂ (fun w => deriv (fun v => deriv (deriv f) v / deriv f v) w
      - 1 / 2 * (deriv (deriv f) w / deriv f w) ^ 2) z :=
    hq.deriv.sub (analyticAt_const.mul (hq.pow 2))
  exact h

/-- §19.1: a locally univalent meromorphic function has a holomorphic Schwarzian derivative.

At a point where `f` is analytic this is `analyticAt_schwarzianHol`.  At a pole, `f` agrees off
`z` with `1/u` for `u` the reciprocal of the normal form, and `schwarzian_inv` identifies
`schwarzian f` with `schwarzian u` on a *whole* neighbourhood of `z` — the pole is removable for
the Schwarzian, which is the content of the statement. -/
theorem schwarzian_holomorphic {f : ℂ → ℂ} {D : Set ℂ} (_hD : IsOpen D) (hf : IsLocUnivMero f D) :
    DifferentiableOn ℂ (schwarzian f) D := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases hf.2 z hz with ⟨hA, hA'⟩ | ⟨-, hu, hu'⟩
  · -- `f` is analytic at `z`, and stays so nearby
    have hnear : schwarzian f =ᶠ[𝓝 z] schwarzianHol f := by
      filter_upwards [hA.eventually_analyticAt] with w hw
      exact schwarzian_of_analyticAt hw
    exact hnear.differentiableAt_iff.mpr (analyticAt_schwarzianHol hA hA').differentiableAt
  · -- `f` has a pole at `z`
    set u : ℂ → ℂ := fun w => (toMeromorphicNFAt f z w)⁻¹ with hudef
    have hmero : MeromorphicAt f z := hf.1 z hz
    have hfu : f =ᶠ[𝓝[≠] z] fun w => (u w)⁻¹ := by
      filter_upwards [hmero.eq_nhdsNE_toMeromorphicNFAt] with w hw
      simp only [hudef, inv_inv]
      exact hw
    -- an open `U ∋ z` on which `u` is analytic with `u' ≠ 0`, and `f = 1/u` off `z`
    have hcomb : ∀ᶠ w in 𝓝 z, (w ≠ z → f w = (u w)⁻¹) ∧ AnalyticAt ℂ u w ∧ deriv u w ≠ 0 := by
      filter_upwards [eventually_nhdsWithin_iff.mp hfu, hu.eventually_analyticAt,
        hu.deriv.continuousAt.eventually_ne hu'] with w e1 e2 e3
      exact ⟨e1, e2, e3⟩
    obtain ⟨U, hU, hUo, hzU⟩ := _root_.eventually_nhds_iff.mp hcomb
    have hnear : schwarzian f =ᶠ[𝓝 z] schwarzianHol u := by
      filter_upwards [hUo.mem_nhds hzU] with w hw
      obtain ⟨-, e2, e3⟩ := hU w hw
      have hgerm : f =ᶠ[𝓝[≠] w] fun v => (u v)⁻¹ := by
        rcases eq_or_ne w z with rfl | hwz
        · exact hfu
        · refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
          filter_upwards [(hUo.sdiff isClosed_singleton).mem_nhds ⟨hw, hwz⟩] with v hv
          exact (hU v hv.1).1 hv.2
      rw [schwarzian_congr hgerm, schwarzian_inv e2 e3, schwarzian_of_analyticAt e2]
    exact hnear.differentiableAt_iff.mpr (analyticAt_schwarzianHol hu hu').differentiableAt

/-- Invariance under post-composition with Möbius transformations, at a point where `g` is
analytic and locally univalent.  When `g z` is the pole of the Möbius map the composite acquires
a pole, and the statement is read through `schwarzian_inv`. -/
theorem schwarzian_mobius_comp_analytic {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z)
    (hg' : deriv g z ≠ 0) {a b c d : ℂ} (h : a * d - b * c ≠ 0) :
    schwarzian (fun w => (a * g w + b) / (c * g w + d)) z = schwarzian g z := by
  by_cases hden : c * g z + d = 0
  · have hnum : a * g z + b ≠ 0 := fun hcon => h (by linear_combination a * hden - c * hcon)
    have hdet' : c * b - d * a ≠ 0 := fun hcon => h (by linear_combination -hcon)
    have hGa : AnalyticAt ℂ (fun w => (c * g w + d) / (a * g w + b)) z :=
      (by fun_prop : AnalyticAt ℂ (fun w => c * g w + d) z).div
        (by fun_prop : AnalyticAt ℂ (fun w => a * g w + b) z) hnum
    have hG' : deriv (fun w => (c * g w + d) / (a * g w + b)) z ≠ 0 := by
      have h1 : HasDerivAt (fun v : ℂ => (c * v + d) / (a * v + b))
          ((c * b - d * a) / (a * g z + b) ^ 2) (g z) := hasDerivAt_mobius hnum
      have h2 : HasDerivAt (fun w => (c * g w + d) / (a * g w + b))
          ((c * b - d * a) / (a * g z + b) ^ 2 * deriv g z) z :=
        h1.comp z hg.differentiableAt.hasDerivAt
      rw [h2.deriv]
      exact mul_ne_zero (div_ne_zero hdet' (pow_ne_zero _ hnum)) hg'
    have hrw : (fun w => (a * g w + b) / (c * g w + d))
        = fun w => ((c * g w + d) / (a * g w + b))⁻¹ := by
      funext w; rw [inv_div]
    rw [hrw, schwarzian_inv hGa hG', schwarzian_mobius_comp_of_ne hg hg' hdet' hnum]
  · exact schwarzian_mobius_comp_of_ne hg hg' h hden

/-- Invariance under post-composition with Möbius transformations: `S_{M∘f} = S_f`. -/
theorem schwarzian_mobius_comp {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLocUnivMero f D) {a b c d : ℂ}
    (h : a * d - b * c ≠ 0) {z : ℂ} (hz : z ∈ D) :
    schwarzian (fun w => (a * f w + b) / (c * f w + d)) z = schwarzian f z := by
  rcases hf.2 z hz with ⟨hA, hA'⟩ | ⟨-, hu, hu'⟩
  · exact schwarzian_mobius_comp_analytic hA hA' h
  · -- at a pole, `f` agrees off `z` with `1/u` for `u` analytic with `u' ≠ 0`
    set u : ℂ → ℂ := fun w => (toMeromorphicNFAt f z w)⁻¹ with hudef
    have hmero : MeromorphicAt f z := hf.1 z hz
    have hfu : f =ᶠ[𝓝[≠] z] fun w => (u w)⁻¹ := by
      filter_upwards [hmero.eq_nhdsNE_toMeromorphicNFAt] with w hw
      simp only [hudef, inv_inv]
      exact hw
    have hune : ∀ᶠ w in 𝓝[≠] z, u w ≠ 0 := by
      refine hu.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hcon => hu' ?_
      have hz0 : u =ᶠ[𝓝 z] fun _ => (0 : ℂ) := hcon
      rw [hz0.deriv_eq, deriv_const]
    have hdet : b * c - a * d ≠ 0 := fun hcon => h (by linear_combination -hcon)
    -- clearing `u` from the numerator and denominator turns `M ∘ f` into a Möbius map of `u`
    have hgerm : (fun w => (a * f w + b) / (c * f w + d)) =ᶠ[𝓝[≠] z]
        fun w => (b * u w + a) / (d * u w + c) := by
      filter_upwards [hfu, hune] with w e hne
      rw [e]
      have e1 : a * (u w)⁻¹ + b = (b * u w + a) / u w := by field_simp; ring
      have e2 : c * (u w)⁻¹ + d = (d * u w + c) / u w := by field_simp; ring
      rw [e1, e2]
      rcases eq_or_ne (d * u w + c) 0 with hd | hd
      · rw [hd, zero_div, div_zero, div_zero]
      · field_simp
    rw [schwarzian_congr hgerm, schwarzian_mobius_comp_analytic hu hu' hdet,
      schwarzian_congr hfu, schwarzian_inv hu hu']

/-- A simply connected hyperbolic plane domain: open, connected, simply connected, `≠ ℂ` (so its
boundary in `ℂ̄` has more than one point). -/
def IsHyperbolicSimplyConnected (D : Set ℂ) : Prop :=
  IsOpen D ∧ IsConnected D ∧ IsSimplyConnected D ∧ D ≠ univ

/-! ### Holomorphic solutions of `w'' + (φ/2) w = 0` on a simply connected domain -/

/-- **Radial comparison estimate.**  Let `H' = h` on `D`, with `H` vanishing at `g 0`, and let `g`
be holomorphic near `closedBall 0 ρ` with `‖g'‖ ≤ A` there and `g (closedBall 0 ρ) ⊆ D`.  A bound
`‖h (g ξ)‖ ≤ K ‖ξ‖ʲ` on the ball integrates along the curves `t ↦ g (t ζ)` to
`‖H (g ζ)‖ ≤ K A ‖ζ‖ʲ⁺¹ / (j + 1)`. -/
theorem norm_comp_le_of_hasDerivAt_radial {D : Set ℂ} {g H h : ℂ → ℂ} {ρ ρ' A K : ℝ} {j : ℕ}
    (hρρ' : ρ < ρ') (hgd : DifferentiableOn ℂ g (ball 0 ρ')) (hgD : MapsTo g (closedBall 0 ρ) D)
    (hH : ∀ z ∈ D, HasDerivAt H (h z) z) (hH0 : H (g 0) = 0)
    (hA : ∀ ζ ∈ closedBall (0 : ℂ) ρ, ‖deriv g ζ‖ ≤ A)
    (hh : ∀ ζ ∈ closedBall (0 : ℂ) ρ, ‖h (g ζ)‖ ≤ K * ‖ζ‖ ^ j) :
    ∀ ζ ∈ closedBall (0 : ℂ) ρ, ‖H (g ζ)‖ ≤ K * A * ‖ζ‖ ^ (j + 1) / (j + 1) := by
  intro ζ hζ
  have hζn : ‖ζ‖ ≤ ρ := mem_closedBall_zero_iff.1 hζ
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * ζ ∈ closedBall (0 : ℂ) ρ := by
    intro t ht
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg ζ, ht.1, ht.2]
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => H (g ((t : ℂ) * ζ)))
      (h (g ((t : ℂ) * ζ)) * (deriv g ((t : ℂ) * ζ) * ζ)) t := by
    intro t ht
    have hball : (t : ℂ) * ζ ∈ ball (0 : ℂ) ρ' := closedBall_subset_ball hρρ' (hmem t ht)
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * ζ) ζ t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const ζ
    have h2 : HasDerivAt g (deriv g ((t : ℂ) * ζ)) ((t : ℂ) * ζ) :=
      (hgd.differentiableAt (isOpen_ball.mem_nhds hball)).hasDerivAt
    have h3 : HasDerivAt H (h (g ((t : ℂ) * ζ))) (g ((t : ℂ) * ζ)) := hH _ (hgD (hmem t ht))
    exact h3.comp t (h2.comp t h1)
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => K * A * ‖ζ‖ ^ (j + 1) * t ^ (j + 1) / (j + 1))
      (K * A * ‖ζ‖ ^ (j + 1) * t ^ j) t := by
    intro t
    have h := ((hasDerivAt_pow (j + 1) t).const_mul (K * A * ‖ζ‖ ^ (j + 1))).div_const
      ((j : ℝ) + 1)
    simp only [Nat.add_sub_cancel] at h
    convert h using 1
    push_cast
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => H (g ((t : ℂ) * ζ))) (Icc 0 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t : ℝ => H (g ((t : ℂ) * ζ)))
    (B := fun t : ℝ => K * A * ‖ζ‖ ^ (j + 1) * t ^ (j + 1) / (j + 1))
    (B' := fun t : ℝ => K * A * ‖ζ‖ ^ (j + 1) * t ^ j) hcont
    (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ hB ?_
    (right_mem_Icc.2 zero_le_one)
  · simpa using hbound
  · simp [hH0]
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have hn : ‖(t : ℂ) * ζ‖ = t * ‖ζ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht'.1]
    have e1 := hh _ (hmem t ht')
    have e2 := hA _ (hmem t ht')
    rw [hn] at e1
    calc ‖h (g ((t : ℂ) * ζ)) * (deriv g ((t : ℂ) * ζ) * ζ)‖
        = ‖h (g ((t : ℂ) * ζ))‖ * (‖deriv g ((t : ℂ) * ζ)‖ * ‖ζ‖) := by
          rw [norm_mul, norm_mul]
      _ ≤ (K * (t * ‖ζ‖) ^ j) * (A * ‖ζ‖) :=
          mul_le_mul e1 (mul_le_mul_of_nonneg_right e2 (norm_nonneg _)) (by positivity)
            ((norm_nonneg _).trans e1)
      _ = K * A * ‖ζ‖ ^ (j + 1) * t ^ j := by ring

/-- **Existence of holomorphic solutions** of `w'' + (φ/2) w = 0 with prescribed `w (g 0)` and
`w' (g 0)`, on an open set `D` which has normalized primitives and is covered by the images of
discs under a holomorphic `g` (proof machinery for `eq19_2_ode`).

The Picard iterates `u₀ = α + β (z - z₀)`, `uₙ₊₁ = P P (-(φ/2) uₙ)` satisfy
`‖uₙ (g ζ)‖ ≤ C (M A²)ⁿ ‖ζ‖²ⁿ / (2n)!` by `norm_comp_le_of_hasDerivAt_radial`; their sum converges
locally uniformly, together with its first two derivatives. -/
theorem exists_ode_solution_of_radialCover {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℂ}
    (hg0 : g 0 ∈ D)
    (hprim : ∀ h : ℂ → ℂ, DifferentiableOn ℂ h D →
      ∃ H : ℂ → ℂ, (∀ z ∈ D, HasDerivAt H (h z) z) ∧ H (g 0) = 0)
    (hcover : ∀ z ∈ D, ∃ ρ ρ' : ℝ, 0 < ρ ∧ ρ < ρ' ∧ DifferentiableOn ℂ g (ball 0 ρ') ∧
      MapsTo g (closedBall 0 ρ) D ∧ g '' closedBall 0 ρ ∈ 𝓝 z)
    {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ D) (α β : ℂ) :
    ∃ w : ℂ → ℂ, DifferentiableOn ℂ w D ∧ (∀ z ∈ D, deriv (deriv w) z = -(φ z / 2) * w z) ∧
      w (g 0) = α ∧ deriv w (g 0) = β := by
  classical
  -- a normalized primitive operator
  obtain ⟨P, hP⟩ : ∃ P : (ℂ → ℂ) → ℂ → ℂ, ∀ h, DifferentiableOn ℂ h D →
      (∀ z ∈ D, HasDerivAt (P h) (h z) z) ∧ P h (g 0) = 0 := by
    refine ⟨fun h => if hh : DifferentiableOn ℂ h D then Classical.choose (hprim h hh) else 0,
      fun h hh => ?_⟩
    simp only [dif_pos hh]
    exact Classical.choose_spec (hprim h hh)
  have hPd : ∀ h, DifferentiableOn ℂ h D → DifferentiableOn ℂ (P h) D := fun h hh z hz =>
    ((hP h hh).1 z hz).differentiableAt.differentiableWithinAt
  -- the Picard iterates
  obtain ⟨u, hu0, husucc⟩ : ∃ u : ℕ → ℂ → ℂ, u 0 = (fun z => α + β * (z - g 0)) ∧
      ∀ n, u (n + 1) = P (P (fun z => -(φ z / 2) * u n z)) :=
    ⟨fun n => Nat.rec (fun z => α + β * (z - g 0))
      (fun _ v => P (P (fun z => -(φ z / 2) * v z))) n, rfl, fun n => rfl⟩
  have hud : ∀ n, DifferentiableOn ℂ (u n) D := by
    intro n
    induction n with
    | zero =>
      rw [hu0]
      fun_prop
    | succ n ih =>
      rw [husucc]
      exact hPd _ (hPd _ ((hφ.div_const 2).neg.mul ih))
  have hkd : ∀ n, DifferentiableOn ℂ (fun z => -(φ z / 2) * u n z) D :=
    fun n => (hφ.div_const 2).neg.mul (hud n)
  -- derivatives of the iterates
  have hderiv_succ : ∀ n, ∀ z ∈ D, deriv (u (n + 1)) z = P (fun z => -(φ z / 2) * u n z) z := by
    intro n z hz
    rw [husucc]
    exact ((hP _ (hPd _ (hkd n))).1 z hz).deriv
  have hderiv2_succ : ∀ n, ∀ z ∈ D, deriv (deriv (u (n + 1))) z = -(φ z / 2) * u n z := by
    intro n z hz
    have hev : deriv (u (n + 1)) =ᶠ[𝓝 z] P (fun z => -(φ z / 2) * u n z) := by
      filter_upwards [hD.mem_nhds hz] with y hy
      exact hderiv_succ n y hy
    rw [hev.deriv_eq]
    exact ((hP _ (hkd n)).1 z hz).deriv
  have hderiv_zero : ∀ z, deriv (u 0) z = β := by
    intro z
    rw [hu0]
    have h : HasDerivAt (fun z => α + β * (z - g 0)) β z := by
      simpa using (((hasDerivAt_id z).sub_const (g 0)).const_mul β).const_add α
    exact h.deriv
  have hderiv2_zero : ∀ z, deriv (deriv (u 0)) z = 0 := by
    intro z
    have h : deriv (u 0) = fun _ => β := funext hderiv_zero
    rw [h, deriv_const]
  have hval_succ : ∀ n, u (n + 1) (g 0) = 0 := fun n => by
    rw [husucc]
    exact (hP _ (hPd _ (hkd n))).2
  have hderiv_succ_0 : ∀ n, deriv (u (n + 1)) (g 0) = 0 := fun n => by
    rw [hderiv_succ n (g 0) hg0]
    exact (hP _ (hkd n)).2
  -- local summable bounds
  have hsum : ∀ z ∈ D, ∃ t ∈ 𝓝 z, ∃ v : ℕ → ℝ, Summable v ∧ ∀ n, ∀ x ∈ t, ‖u n x‖ ≤ v n := by
    intro z hz
    obtain ⟨ρ, ρ', hρ, hρρ', hgd, hgD, hN⟩ := hcover z hz
    have hcb : closedBall (0 : ℂ) ρ ⊆ ball 0 ρ' := closedBall_subset_ball hρρ'
    have hK : IsCompact (closedBall (0 : ℂ) ρ) := isCompact_closedBall 0 ρ
    have hgc : ContinuousOn g (closedBall 0 ρ) := hgd.continuousOn.mono hcb
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
      ((hgd.deriv isOpen_ball).continuousOn.mono hcb)
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun ζ => φ (g ζ) / 2)
      ((hφ.continuousOn.comp hgc hgD).div_const 2)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun ζ => u 0 (g ζ))
      ((hud 0).continuousOn.comp hgc hgD)
    have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) ρ := mem_closedBall_self hρ.le
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 h0mem)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 h0mem)
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 h0mem)
    have hbound : ∀ n, ∀ ζ ∈ closedBall (0 : ℂ) ρ,
        ‖u n (g ζ)‖ ≤ C * (M * A ^ 2) ^ n / (2 * n).factorial * ‖ζ‖ ^ (2 * n) := by
      intro n
      induction n with
      | zero =>
        intro ζ hζ
        simpa using hC ζ hζ
      | succ n ih =>
        intro ζ hζ
        have hk : ∀ ξ ∈ closedBall (0 : ℂ) ρ, ‖(fun z => -(φ z / 2) * u n z) (g ξ)‖ ≤
            (M * (C * (M * A ^ 2) ^ n / (2 * n).factorial)) * ‖ξ‖ ^ (2 * n) := by
          intro ξ hξ
          show ‖-(φ (g ξ) / 2) * u n (g ξ)‖ ≤ _
          rw [norm_mul, norm_neg, mul_assoc]
          exact mul_le_mul (hM ξ hξ) (ih ξ hξ) (norm_nonneg _) hM0
        have h1 := norm_comp_le_of_hasDerivAt_radial hρρ' hgd hgD (hP _ (hkd n)).1
          (hP _ (hkd n)).2 hA hk
        have h1' : ∀ ξ ∈ closedBall (0 : ℂ) ρ, ‖P (fun z => -(φ z / 2) * u n z) (g ξ)‖ ≤
            (M * (C * (M * A ^ 2) ^ n / (2 * n).factorial) * A / (2 * n + 1)) *
              ‖ξ‖ ^ (2 * n + 1) := by
          intro ξ hξ
          calc _ ≤ _ := h1 ξ hξ
            _ = _ := by push_cast; ring
        have h2 := norm_comp_le_of_hasDerivAt_radial hρρ' hgd hgD
          (hP _ (hPd _ (hkd n))).1 (hP _ (hPd _ (hkd n))).2 hA h1'
        have hf : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
        rw [husucc]
        calc ‖P (P fun z => -(φ z / 2) * u n z) (g ζ)‖ ≤ _ := h2 ζ hζ
          _ = C * (M * A ^ 2) ^ (n + 1) / (2 * (n + 1)).factorial * ‖ζ‖ ^ (2 * (n + 1)) := by
            rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
            push_cast
            field_simp
            ring
    have hcoef : ∀ n : ℕ, 0 ≤ C * (M * A ^ 2) ^ n / ((2 * n).factorial : ℝ) := fun n =>
      div_nonneg (mul_nonneg hC0 (pow_nonneg (mul_nonneg hM0 (sq_nonneg A)) n)) (Nat.cast_nonneg _)
    refine ⟨g '' closedBall 0 ρ, hN,
      fun n => C * (M * A ^ 2) ^ n / (2 * n).factorial * ρ ^ (2 * n), ?_, ?_⟩
    · have hs := (Real.summable_pow_div_factorial (M * A ^ 2 * ρ ^ 2)).mul_left C
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hcoef n) (pow_nonneg hρ.le _))
        (fun n => ?_) hs
      have hfac : (n.factorial : ℝ) ≤ (2 * n).factorial := by
        exact_mod_cast Nat.factorial_le (by omega)
      have hn0 : (0 : ℝ) < n.factorial := by positivity
      have e : C * (M * A ^ 2) ^ n / ((2 * n).factorial : ℝ) * ρ ^ (2 * n)
          = C * ((M * A ^ 2 * ρ ^ 2) ^ n / (2 * n).factorial) := by
        rw [mul_pow, ← pow_mul]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left
        (pow_nonneg (mul_nonneg (mul_nonneg hM0 (sq_nonneg A)) (sq_nonneg ρ)) n) hn0 hfac) hC0
    · rintro n x ⟨ζ, hζ, rfl⟩
      calc ‖u n (g ζ)‖ ≤ _ := hbound n ζ hζ
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 hζ) _) (hcoef n)
  -- the sum of the series and its derivatives
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℂ → ℂ, S = fun N z => ∑ n ∈ Finset.range N, u n z := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ → ℂ, w = fun z => ∑' n, u n z := ⟨_, rfl⟩
  have hconv : TendstoLocallyUniformlyOn S w atTop D := by
    rw [hS, hw]
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz => ?_
    obtain ⟨t, ht, v, hv, hvb⟩ := hsum z hz
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, tendstoUniformlyOn_tsum_nat hv hvb⟩
  have hSd : ∀ N, DifferentiableOn ℂ (S N) D := fun N => by
    rw [hS]
    exact DifferentiableOn.fun_sum fun n _ => hud n
  have hdS : ∀ N, ∀ z ∈ D, deriv (S N) z = ∑ n ∈ Finset.range N, deriv (u n) z := by
    intro N z hz
    rw [hS]
    exact deriv_fun_sum fun n _ => (hud n).differentiableAt (hD.mem_nhds hz)
  have hddS : ∀ N, ∀ z ∈ D,
      deriv (deriv (S N)) z = ∑ n ∈ Finset.range N, deriv (deriv (u n)) z := by
    intro N z hz
    have hev : deriv (S N) =ᶠ[𝓝 z] fun y => ∑ n ∈ Finset.range N, deriv (u n) y := by
      filter_upwards [hD.mem_nhds hz] with y hy
      exact hdS N y hy
    rw [hev.deriv_eq]
    exact deriv_fun_sum fun n _ => ((hud n).deriv hD).differentiableAt (hD.mem_nhds hz)
  have hODE_S : ∀ N, ∀ z ∈ D, deriv (deriv (S (N + 1))) z = -(φ z / 2) * S N z := by
    intro N z hz
    rw [hddS (N + 1) z hz, Finset.sum_range_succ', hderiv2_zero, add_zero, hS, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hderiv2_succ n z hz
  have hconv1 := hconv.deriv (Eventually.of_forall hSd) hD
  have hconv2 := hconv1.deriv (Eventually.of_forall fun N => (hSd N).deriv hD) hD
  have hwd : DifferentiableOn ℂ w D := hconv.differentiableOn (Eventually.of_forall hSd) hD
  refine ⟨w, hwd, fun z hz => ?_, ?_, ?_⟩
  · have h1 : Tendsto (fun N => deriv (deriv (S (N + 1))) z) atTop (𝓝 (deriv (deriv w) z)) :=
      (hconv2.tendsto_at hz).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N => deriv (deriv (S (N + 1))) z) atTop (𝓝 (-(φ z / 2) * w z)) :=
      ((hconv.tendsto_at hz).const_mul (-(φ z / 2))).congr fun N => (hODE_S N z hz).symm
    exact tendsto_nhds_unique h1 h2
  · rw [hw]
    show ∑' n, u n (g 0) = α
    rw [tsum_eq_single 0 fun n hn => ?_]
    · rw [hu0]
      simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact hval_succ m
  · have h1 : Tendsto (fun N => deriv (S N) (g 0)) atTop (𝓝 (deriv w (g 0))) :=
      hconv1.tendsto_at hg0
    have h2 : Tendsto (fun N => deriv (S N) (g 0)) atTop (𝓝 β) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      rw [hdS (m + 1) (g 0) hg0, Finset.sum_range_succ', hderiv_zero]
      simp [hderiv_succ_0]
    exact tendsto_nhds_unique h1 h2

/-- A simply connected domain is covered by the images of discs under one holomorphic map: the
inverse of a Riemann map, or the identity when the domain is `ℂ` (proof machinery for
`eq19_2_ode`). -/
theorem exists_radialCover_of_simplyConnected {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D)
    [SimplyConnectedSpace ↥D] :
    ∃ g : ℂ → ℂ, g 0 ∈ D ∧ ∀ z ∈ D, ∃ ρ ρ' : ℝ, 0 < ρ ∧ ρ < ρ' ∧
      DifferentiableOn ℂ g (ball 0 ρ') ∧ MapsTo g (closedBall 0 ρ) D ∧
        g '' closedBall 0 ρ ∈ 𝓝 z := by
  by_cases hne : Dᶜ.Nonempty
  · obtain ⟨z₁, hz₁⟩ := hDc.nonempty
    obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap hD hDc hne hz₁
    obtain ⟨hψ, hψb⟩ := RMT.invFunOn_riemannMap hD hf.diff hf.injOn hfb
    refine ⟨Function.invFunOn f D, hψb.mapsTo (mem_ball_self one_pos), fun z hz => ?_⟩
    have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.1 (hfb.mapsTo hz)
    refine ⟨(‖f z‖ + 1) / 2, 1, by positivity, by linarith, hψ, ?_, ?_⟩
    · intro ζ hζ
      exact hψb.mapsTo (closedBall_subset_ball (by linarith) hζ)
    · have hcont : ContinuousAt f z := hf.diff.continuousOn.continuousAt (hD.mem_nhds hz)
      have hnhds : D ∩ f ⁻¹' ball 0 ((‖f z‖ + 1) / 2) ∈ 𝓝 z :=
        inter_mem (hD.mem_nhds hz) (hcont.preimage_mem_nhds
          (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith)))
      refine mem_of_superset hnhds fun w hw => ⟨f w, ball_subset_closedBall hw.2, ?_⟩
      exact hfb.invOn_invFunOn.1 hw.1
  · have hD' : D = univ := by
      rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
      exact hne
    refine ⟨id, by rw [hD']; exact mem_univ _, fun z _ => ⟨‖z‖ + 1, ‖z‖ + 2, by positivity,
      by linarith, differentiableOn_id, fun _ _ => by rw [hD']; exact mem_univ _, ?_⟩⟩
    rw [image_id]
    exact mem_of_superset (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))
      ball_subset_closedBall

/-- If `q' = c / p²` with `c ≠ 0` and `p'' = -(φ/2) p` near `z`, with `p` non-vanishing, then
`S_q (z) = φ (z)`: indeed `q''/q' = -2p'/p`, so `S_q = -2p''/p` (proof machinery for
`eq19_2_ode`). -/
theorem schwarzianHol_eq_of_deriv_eq_const_div_sq {q p φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) {c : ℂ} (hc : c ≠ 0) (hp : DifferentiableOn ℂ p U)
    (hp0 : ∀ y ∈ U, p y ≠ 0) (hq : ∀ y ∈ U, deriv q y = c / p y ^ 2)
    (hpp : ∀ y ∈ U, deriv (deriv p) y = -(φ y / 2) * p y) :
    schwarzianHol q z = φ z := by
  have hp' : DifferentiableOn ℂ (deriv p) U := hp.deriv hU
  have hd2 : ∀ y ∈ U, deriv (deriv q) y = -(2 * c * deriv p y) / p y ^ 3 := by
    intro y hy
    have hev : deriv q =ᶠ[𝓝 y] fun v => c / p v ^ 2 := by
      filter_upwards [hU.mem_nhds hy] with v hv
      exact hq v hv
    rw [hev.deriv_eq]
    have hpy := (hp.differentiableAt (hU.mem_nhds hy)).hasDerivAt
    have h : HasDerivAt (fun v => c / p v ^ 2) _ y :=
      (hasDerivAt_const y c).div (hpy.pow 2) (pow_ne_zero 2 (hp0 y hy))
    rw [h.deriv]
    have := hp0 y hy
    norm_num
    field_simp
  have hr : (fun y => deriv (deriv q) y / deriv q y) =ᶠ[𝓝 z]
      fun y => -2 * deriv p y / p y := by
    filter_upwards [hU.mem_nhds hz] with y hy
    rw [hd2 y hy, hq y hy]
    have := hp0 y hy
    field_simp
  have hr' : deriv (fun y => deriv (deriv q) y / deriv q y) z =
      (-2 * deriv (deriv p) z * p z - -2 * deriv p z * deriv p z) / p z ^ 2 := by
    rw [hr.deriv_eq]
    have h1 := (hp'.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have h2 := (hp.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    exact ((h1.const_mul (-2)).div h2 (hp0 z hz)).deriv
  have hval : deriv (deriv q) z / deriv q z = -2 * deriv p z / p z := hr.self_of_nhds
  unfold schwarzianHol
  rw [hr', hval, hpp z hz]
  have := hp0 z hz
  field_simp
  ring

/-- §19.1 (19.2): for `φ` holomorphic in a simply connected domain `D`, the equation
`w'' + ½ φ w = 0` has solutions `w₁, w₂` with `w₁ w₂' - w₂ w₁' = 1`, and `f = w₁/w₂` satisfies
`S_f = φ`.

The book quotes the existence of the solutions as standard.  Here they are built by Picard
iteration on `D` itself (`exists_ode_solution_of_radialCover`): primitives exist on the simply
connected domain (`RMT.exists_primitive_of_simplyConnected`), and the iterates are estimated along
the images `t ↦ g (t ζ)` of radii under the inverse `g` of a Riemann map
(`exists_radialCover_of_simplyConnected`), so no analytic continuation along paths and no monodromy
theorem are needed.  The Wronskian is constant, so `w₁/w₂` is locally univalent with simple poles at
the zeros of `w₂`, and `S_{w₁/w₂} = -2 w₂''/w₂ = φ` (`schwarzianHol_eq_of_deriv_eq_const_div_sq`). -/
theorem eq19_2_ode {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) (hDs : IsSimplyConnected D)
    {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ D) :
    ∃ w₁ w₂ : ℂ → ℂ, DifferentiableOn ℂ w₁ D ∧ DifferentiableOn ℂ w₂ D ∧
      (∀ z ∈ D, deriv (deriv w₁) z + φ z / 2 * w₁ z = 0 ∧ deriv (deriv w₂) z + φ z / 2 * w₂ z = 0 ∧
        w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1) ∧
      IsLocUnivMero (fun z => w₁ z / w₂ z) D ∧ ∀ z ∈ D, schwarzian (fun z => w₁ z / w₂ z) z = φ z := by
  haveI : SimplyConnectedSpace ↥D := hDs
  obtain ⟨g, hg0, hcover⟩ := exists_radialCover_of_simplyConnected hD hDc
  have hprim : ∀ h : ℂ → ℂ, DifferentiableOn ℂ h D →
      ∃ H : ℂ → ℂ, (∀ z ∈ D, HasDerivAt H (h z) z) ∧ H (g 0) = 0 := by
    intro h hh
    obtain ⟨G, hG, hG'⟩ := RMT.exists_primitive_of_simplyConnected hD hDc hh
    refine ⟨fun z => G z - G (g 0), fun z hz => ?_, sub_self _⟩
    have h1 := (hG.differentiableAt (hD.mem_nhds hz)).hasDerivAt
    rw [hG' z hz] at h1
    exact h1.sub_const _
  obtain ⟨w₁, hw₁, hode₁, hw₁0, hw₁0'⟩ :=
    exists_ode_solution_of_radialCover hD hg0 hprim hcover hφ 1 0
  obtain ⟨w₂, hw₂, hode₂, hw₂0, hw₂0'⟩ :=
    exists_ode_solution_of_radialCover hD hg0 hprim hcover hφ 0 1
  -- the Wronskian is constant, equal to its value `1` at `g 0`
  have hW : ∀ z ∈ D, w₁ z * deriv w₂ z - w₂ z * deriv w₁ z = 1 := by
    have hd₁ : DifferentiableOn ℂ (deriv w₁) D := hw₁.deriv hD
    have hd₂ : DifferentiableOn ℂ (deriv w₂) D := hw₂.deriv hD
    have hWd : DifferentiableOn ℂ (fun z => w₁ z * deriv w₂ z - w₂ z * deriv w₁ z) D :=
      (hw₁.mul hd₂).sub (hw₂.mul hd₁)
    have hW' : EqOn (deriv fun z => w₁ z * deriv w₂ z - w₂ z * deriv w₁ z) 0 D := by
      intro z hz
      have hn := hD.mem_nhds hz
      have h : HasDerivAt (fun z => w₁ z * deriv w₂ z - w₂ z * deriv w₁ z) _ z :=
        ((hw₁.differentiableAt hn).hasDerivAt.mul (hd₂.differentiableAt hn).hasDerivAt).sub
          ((hw₂.differentiableAt hn).hasDerivAt.mul (hd₁.differentiableAt hn).hasDerivAt)
      rw [h.deriv, hode₁ z hz, hode₂ z hz]
      simp only [Pi.zero_apply]
      ring
    intro z hz
    have h := hD.is_const_of_deriv_eq_zero hDc.isPreconnected hWd hW' hz hg0
    rw [h, hw₁0, hw₂0, hw₁0', hw₂0']
    ring
  have han₁ : ∀ z ∈ D, AnalyticAt ℂ w₁ z := fun z hz => hw₁.analyticAt (hD.mem_nhds hz)
  have han₂ : ∀ z ∈ D, AnalyticAt ℂ w₂ z := fun z hz => hw₂.analyticAt (hD.mem_nhds hz)
  -- points where `w₂ ≠ 0`: `f = w₁/w₂` is analytic with `f' = -1/w₂²`
  have hne2 : ∀ z ∈ D, w₂ z ≠ 0 → AnalyticAt ℂ (fun z => w₁ z / w₂ z) z ∧
      deriv (fun z => w₁ z / w₂ z) z ≠ 0 ∧ schwarzian (fun z => w₁ z / w₂ z) z = φ z := by
    intro z hz h2
    have hU : IsOpen (D ∩ w₂ ⁻¹' {0}ᶜ) :=
      hw₂.continuousOn.isOpen_inter_preimage hD isOpen_compl_singleton
    have hderiv : ∀ y ∈ D ∩ w₂ ⁻¹' {0}ᶜ, deriv (fun z => w₁ z / w₂ z) y = -1 / w₂ y ^ 2 := by
      intro y hy
      have hy2 : w₂ y ≠ 0 := hy.2
      have hn := hD.mem_nhds hy.1
      have h : HasDerivAt (fun z => w₁ z / w₂ z) _ y :=
        (hw₁.differentiableAt hn).hasDerivAt.div (hw₂.differentiableAt hn).hasDerivAt hy2
      rw [h.deriv, div_left_inj' (pow_ne_zero 2 hy2)]
      linear_combination -hW y hy.1
    have hfa : AnalyticAt ℂ (fun z => w₁ z / w₂ z) z := (han₁ z hz).div (han₂ z hz) h2
    refine ⟨hfa, ?_, ?_⟩
    · rw [hderiv z ⟨hz, h2⟩]
      exact div_ne_zero (by norm_num) (pow_ne_zero 2 h2)
    · rw [schwarzian_of_analyticAt hfa]
      exact schwarzianHol_eq_of_deriv_eq_const_div_sq hU ⟨hz, h2⟩ (by norm_num)
        (hw₂.mono inter_subset_left) (fun y hy => hy.2) hderiv (fun y hy => hode₂ y hy.1)
  -- points where `w₂ = 0`: `f = 1/G` with `G = w₂/w₁` analytic, `G' = 1/w₁²`
  have heq2 : ∀ z ∈ D, w₂ z = 0 →
      (meromorphicOrderAt (fun z => w₁ z / w₂ z) z < 0 ∧
        AnalyticAt ℂ (fun w => (toMeromorphicNFAt (fun z => w₁ z / w₂ z) z w)⁻¹) z ∧
        deriv (fun w => (toMeromorphicNFAt (fun z => w₁ z / w₂ z) z w)⁻¹) z ≠ 0) ∧
      schwarzian (fun z => w₁ z / w₂ z) z = φ z := by
    intro z hz h2
    have hWz := hW z hz
    have h1 : w₁ z ≠ 0 := by
      intro h
      rw [h, h2] at hWz
      simp at hWz
    have hGa : AnalyticAt ℂ (fun y => w₂ y / w₁ y) z := (han₂ z hz).div (han₁ z hz) h1
    have hfG : (fun z => w₁ z / w₂ z) = fun y => (w₂ y / w₁ y)⁻¹ := by
      funext y
      rw [inv_div]
    have hU : IsOpen (D ∩ w₁ ⁻¹' {0}ᶜ) :=
      hw₁.continuousOn.isOpen_inter_preimage hD isOpen_compl_singleton
    have hGderiv : ∀ y ∈ D ∩ w₁ ⁻¹' {0}ᶜ, deriv (fun y => w₂ y / w₁ y) y = 1 / w₁ y ^ 2 := by
      intro y hy
      have hy1 : w₁ y ≠ 0 := hy.2
      have hn := hD.mem_nhds hy.1
      have h : HasDerivAt (fun y => w₂ y / w₁ y) _ y :=
        (hw₂.differentiableAt hn).hasDerivAt.div (hw₁.differentiableAt hn).hasDerivAt hy1
      rw [h.deriv, div_left_inj' (pow_ne_zero 2 hy1)]
      linear_combination hW y hy.1
    have hG0 : (fun y => w₂ y / w₁ y) z = 0 := by simp [h2]
    have hG' : deriv (fun y => w₂ y / w₁ y) z ≠ 0 := by
      rw [hGderiv z ⟨hz, h1⟩]
      exact div_ne_zero one_ne_zero (pow_ne_zero 2 h1)
    have hord1 : meromorphicOrderAt (fun y => w₂ y / w₁ y) z = 1 := by
      rw [hGa.meromorphicOrderAt_eq, hGa.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hG0 hG']
      rfl
    have hord : meromorphicOrderAt (fun y => (w₂ y / w₁ y)⁻¹) z = -1 := by
      show meromorphicOrderAt (fun y => w₂ y / w₁ y)⁻¹ z = -1
      rw [meromorphicOrderAt_inv, hord1]
    have hNF : toMeromorphicNFAt (fun y => (w₂ y / w₁ y)⁻¹) z = fun y => (w₂ y / w₁ y)⁻¹ :=
      (toMeromorphicNFAt_eq_self (f := fun y => (w₂ y / w₁ y)⁻¹) (x := z)).mpr
        hGa.meromorphicNFAt.inv
    rw [hfG, hNF]
    simp only [inv_inv]
    refine ⟨⟨by rw [hord]; decide, hGa, hG'⟩, ?_⟩
    rw [schwarzian_inv_of_simple_zero hGa hG0 hG', schwarzian_of_analyticAt hGa]
    exact schwarzianHol_eq_of_deriv_eq_const_div_sq hU ⟨hz, h1⟩ one_ne_zero
      (hw₁.mono inter_subset_left) (fun y hy => hy.2) hGderiv (fun y hy => hode₁ y hy.1)
  refine ⟨w₁, w₂, hw₁, hw₂, fun z hz => ⟨by rw [hode₁ z hz]; ring, by rw [hode₂ z hz]; ring,
    hW z hz⟩, ⟨fun z hz => (han₁ z hz).meromorphicAt.div (han₂ z hz).meromorphicAt,
    fun z hz => ?_⟩, fun z hz => ?_⟩
  · by_cases h2 : w₂ z = 0
    · exact Or.inr (heq2 z hz h2).1
    · exact Or.inl ⟨(hne2 z hz h2).1, (hne2 z hz h2).2.1⟩
  · by_cases h2 : w₂ z = 0
    · exact (heq2 z hz h2).2
    · exact (hne2 z hz h2).2.2

/-- **Theorem 19.1** (existence): for every `φ` holomorphic in a simply connected domain `D` there
is a locally univalent meromorphic `f` in `D` with `S_f = φ`. -/
theorem thm19_1_exists {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D)
    (hDs : IsSimplyConnected D) {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ D) :
    ∃ f : ℂ → ℂ, IsLocUnivMero f D ∧ ∀ z ∈ D, schwarzian f z = φ z := by
  obtain ⟨w₁, w₂, -, -, -, hloc, hS⟩ := eq19_2_ode hD hDc hDs hφ
  exact ⟨fun z => w₁ z / w₂ z, hloc, hS⟩

/-! ### Uniqueness in Theorem 19.1: fractional linear maps -/

/-- `x ↦ M (1/x)` is again fractional linear, with the columns of `M` swapped. -/
theorem mobius_inv_arg {a b c d t : ℂ} (ht : t ≠ 0) :
    (b * t⁻¹ + a) / (d * t⁻¹ + c) = (a * t + b) / (c * t + d) := by
  have e1 : b * t⁻¹ + a = (a * t + b) * t⁻¹ := by
    rw [add_mul, mul_assoc, mul_inv_cancel₀ ht, mul_one, add_comm]
  have e2 : d * t⁻¹ + c = (c * t + d) * t⁻¹ := by
    rw [add_mul, mul_assoc, mul_inv_cancel₀ ht, mul_one, add_comm]
  rw [e1, e2, mul_div_mul_right _ _ (inv_ne_zero ht)]

/-- An analytic function with non-vanishing derivative has no zeros on a punctured
neighbourhood. -/
theorem eventually_ne_zero_of_deriv_ne_zero {G : ℂ → ℂ} {z : ℂ} (hG : AnalyticAt ℂ G z)
    (hG' : deriv G z ≠ 0) : ∀ᶠ y in 𝓝[≠] z, G y ≠ 0 := by
  rcases hG.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exfalso
    apply hG'
    have hev : G =ᶠ[𝓝 z] fun _ => (0 : ℂ) := h0
    rw [hev.deriv_eq, deriv_const]
  · exact h0

/-- **Rigidity of fractional linear maps.**  Two of them agreeing on a punctured neighbourhood of a
point agree everywhere, as functions `ℂ → ℂ` (at a pole both take the value `0`). -/
theorem mobius_eq_of_eventually_nhdsNE {a b c d a' b' c' d' : ℂ} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) {x₀ : ℂ}
    (heq : ∀ᶠ x in 𝓝[≠] x₀, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d')) :
    ∀ x, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d') := by
  have hden : ∀ {p q r s : ℂ}, p * s - q * r ≠ 0 → ∀ᶠ x in 𝓝[≠] x₀, r * x + s ≠ 0 := by
    intro p q r s hdet
    have han : AnalyticAt ℂ (fun x : ℂ => r * x + s) x₀ := by fun_prop
    rcases han.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
    · exfalso
      have hev : (fun x : ℂ => r * x + s) =ᶠ[𝓝 x₀] fun _ => (0 : ℂ) := h0
      have hr : r = 0 := by
        have hd : HasDerivAt (fun x : ℂ => r * x + s) r x₀ := by
          simpa using ((hasDerivAt_id x₀).const_mul r).add_const s
        have h1 := hd.deriv
        rw [hev.deriv_eq, deriv_const] at h1
        exact h1.symm
      have hs : s = 0 := by
        have h1 : r * x₀ + s = 0 := hev.self_of_nhds
        rw [hr, zero_mul, zero_add] at h1
        exact h1
      exact hdet (by rw [hr, hs]; ring)
    · exact h0
  have hP : ∀ x, (a * x + b) * (c' * x + d') - (a' * x + b') * (c * x + d) = 0 := by
    have hfreq : ∃ᶠ x in 𝓝[≠] x₀,
        (a * x + b) * (c' * x + d') - (a' * x + b') * (c * x + d) = 0 := by
      refine Eventually.frequently ?_
      filter_upwards [heq, hden h, hden h'] with x hx h1 h2
      rw [div_eq_div_iff h1 h2] at hx
      linear_combination hx
    have hPan : AnalyticOnNhd ℂ
        (fun x : ℂ => (a * x + b) * (c' * x + d') - (a' * x + b') * (c * x + d)) univ :=
      fun x _ => by fun_prop
    intro x
    exact hPan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ x₀)
      hfreq (mem_univ x)
  intro x
  have hPx := hP x
  by_cases h1 : c * x + d = 0
  · have hnum : a * x + b ≠ 0 := fun hn => h (by linear_combination a * h1 - c * hn)
    have h2 : c' * x + d' = 0 := by
      rw [h1, mul_zero, sub_zero] at hPx
      exact (mul_eq_zero.1 hPx).resolve_left hnum
    rw [h1, h2, div_zero, div_zero]
  · by_cases h2 : c' * x + d' = 0
    · exfalso
      have hnum' : a' * x + b' ≠ 0 := fun hn => h' (by linear_combination a' * h2 - c' * hn)
      rw [h2, mul_zero, zero_sub, neg_eq_zero] at hPx
      exact mul_ne_zero hnum' h1 hPx
    · rw [div_eq_div_iff h1 h2]
      linear_combination hPx

/-- Transport of `mobius_eq_of_eventually_nhdsNE` along an analytic map with non-vanishing
derivative, which is open. -/
theorem mobius_eq_of_comp_eventually_nhdsNE {a b c d a' b' c' d' : ℂ} (h : a * d - b * c ≠ 0)
    (h' : a' * d' - b' * c' ≠ 0) {G : ℂ → ℂ} {y₀ : ℂ} (hG : AnalyticAt ℂ G y₀)
    (hG' : deriv G y₀ ≠ 0)
    (heq : ∀ᶠ y in 𝓝[≠] y₀, (a * G y + b) / (c * G y + d) = (a' * G y + b') / (c' * G y + d')) :
    ∀ x, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d') := by
  refine mobius_eq_of_eventually_nhdsNE h h' (x₀ := G y₀) ?_
  have hmap : map G (𝓝 y₀) = 𝓝 (G y₀) := hG.hasStrictDerivAt.map_nhds_eq hG'
  rw [eventually_nhdsWithin_iff] at heq ⊢
  rw [← hmap, eventually_map]
  filter_upwards [heq] with y hy hne
  exact hy fun hyy => hne (mem_singleton_iff.2 (congrArg G (mem_singleton_iff.1 hyy)))

/-! ### Uniqueness in Theorem 19.1: local charts -/

/-- A locally univalent meromorphic function is, near each point, either an analytic function with
non-vanishing derivative or its reciprocal, and its Schwarzian is the holomorphic Schwarzian of that
analytic function. -/
theorem exists_chart_of_isLocUnivMero {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLocUnivMero f D) {z : ℂ}
    (hz : z ∈ D) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F z ∧ deriv F z ≠ 0 ∧ schwarzian f =ᶠ[𝓝 z] schwarzianHol F ∧
      ((f =ᶠ[𝓝[≠] z] F) ∨ (f =ᶠ[𝓝[≠] z] fun y => (F y)⁻¹)) := by
  rcases hf.2 z hz with ⟨hA, hA'⟩ | ⟨-, hu, hu'⟩
  · refine ⟨f, hA, hA', ?_, Or.inl (EventuallyEq.refl _ _)⟩
    filter_upwards [hA.eventually_analyticAt] with w hw
    exact schwarzian_of_analyticAt hw
  · set u : ℂ → ℂ := fun w => (toMeromorphicNFAt f z w)⁻¹ with hudef
    have hmero : MeromorphicAt f z := hf.1 z hz
    have hfu : f =ᶠ[𝓝[≠] z] fun w => (u w)⁻¹ := by
      filter_upwards [hmero.eq_nhdsNE_toMeromorphicNFAt] with w hw
      simp only [hudef, inv_inv]
      exact hw
    have hcomb : ∀ᶠ w in 𝓝 z, (w ≠ z → f w = (u w)⁻¹) ∧ AnalyticAt ℂ u w ∧ deriv u w ≠ 0 := by
      filter_upwards [eventually_nhdsWithin_iff.mp hfu, hu.eventually_analyticAt,
        hu.deriv.continuousAt.eventually_ne hu'] with w e1 e2 e3
      exact ⟨e1, e2, e3⟩
    obtain ⟨U, hU, hUo, hzU⟩ := _root_.eventually_nhds_iff.mp hcomb
    refine ⟨u, hu, hu', ?_, Or.inr hfu⟩
    filter_upwards [hUo.mem_nhds hzU] with w hw
    obtain ⟨-, e2, e3⟩ := hU w hw
    have hgerm : f =ᶠ[𝓝[≠] w] fun v => (u v)⁻¹ := by
      rcases eq_or_ne w z with rfl | hwz
      · exact hfu
      · refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [(hUo.sdiff isClosed_singleton).mem_nhds ⟨hw, hwz⟩] with v hv
        exact (hU v hv.1).1 hv.2
    rw [schwarzian_congr hgerm, schwarzian_inv e2 e3, schwarzian_of_analyticAt e2]

/-- If `M ∘ g = N ∘ g` near a point of a domain where `g` is locally univalent meromorphic, the
fractional linear maps `M` and `N` coincide. -/
theorem mobius_eq_of_comp_eventuallyEq {g : ℂ → ℂ} {D : Set ℂ} (hg : IsLocUnivMero g D) {z : ℂ}
    (hz : z ∈ D) {a b c d a' b' c' d' : ℂ} (h : a * d - b * c ≠ 0) (h' : a' * d' - b' * c' ≠ 0)
    (heq : (fun y => (a * g y + b) / (c * g y + d)) =ᶠ[𝓝[≠] z]
      fun y => (a' * g y + b') / (c' * g y + d')) :
    ∀ x, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d') := by
  obtain ⟨G, hGa, hG', -, hrel⟩ := exists_chart_of_isLocUnivMero hg hz
  rcases hrel with hgG | hgG
  · refine mobius_eq_of_comp_eventually_nhdsNE h h' hGa hG' ?_
    filter_upwards [heq, hgG] with y hy hgy
    rw [← hgy]
    exact hy
  · have hdet₁ : b * c - a * d ≠ 0 := fun hc => h (by linear_combination -hc)
    have hdet₂ : b' * c' - a' * d' ≠ 0 := fun hc => h' (by linear_combination -hc)
    have hinv : ∀ x, (b * x + a) / (d * x + c) = (b' * x + a') / (d' * x + c') := by
      refine mobius_eq_of_comp_eventually_nhdsNE hdet₁ hdet₂ hGa hG' ?_
      filter_upwards [heq, hgG, eventually_ne_zero_of_deriv_ne_zero hGa hG'] with y hy hgy hy0
      rw [hgy, mobius_inv_arg hy0, mobius_inv_arg hy0] at hy
      exact hy
    refine mobius_eq_of_eventually_nhdsNE h h' (x₀ := 1) ?_
    filter_upwards [(eventually_ne_nhds (one_ne_zero (α := ℂ))).filter_mono nhdsWithin_le_nhds]
      with x hx
    have e := hinv x⁻¹
    rw [mobius_inv_arg hx, mobius_inv_arg hx] at e
    exact e

/-! ### Uniqueness in Theorem 19.1: the solutions `(f')^{-1/2}` and `f (f')^{-1/2}` -/

/-- A zero-free holomorphic function on a disc has a holomorphic square root. -/
theorem exists_sq_eq_on_ball {F : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (ball z r)) (hF0 : ∀ y ∈ ball z r, F y ≠ 0) :
    ∃ s : ℂ → ℂ, DifferentiableOn ℂ s (ball z r) ∧ ∀ y ∈ ball z r, s y ^ 2 = F y := by
  haveI : ContractibleSpace ↥(ball z r) :=
    (convex_ball z r).contractibleSpace ⟨z, mem_ball_self hr⟩
  haveI : SimplyConnectedSpace ↥(ball z r) := SimplyConnectedSpace.ofContractible _
  exact RMT.hasHolomorphicSqrt_of_simplyConnected isOpen_ball
    ⟨⟨z, mem_ball_self hr⟩, (convex_ball z r).isPreconnected⟩ F hF hF0

/-- On a disc where `F' ≠ 0`, the functions `y₂ = (F')^{-1/2}` and `y₁ = F y₂` solve
`w'' + ½ S_F w = 0`, with Wronskian `y₁ y₂' - y₂ y₁' = -1`. -/
theorem exists_solutions_on_ball {F : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (ball z r)) (hF' : ∀ y ∈ ball z r, deriv F y ≠ 0) :
    ∃ y₁ y₂ : ℂ → ℂ, DifferentiableOn ℂ y₁ (ball z r) ∧ DifferentiableOn ℂ y₂ (ball z r) ∧
      (∀ y ∈ ball z r, deriv (deriv y₁) y = -(schwarzianHol F y / 2) * y₁ y) ∧
      (∀ y ∈ ball z r, deriv (deriv y₂) y = -(schwarzianHol F y / 2) * y₂ y) ∧
      (∀ y ∈ ball z r, y₂ y ≠ 0) ∧ (∀ y ∈ ball z r, y₁ y = F y * y₂ y) ∧
      (∀ y ∈ ball z r, y₁ y * deriv y₂ y - y₂ y * deriv y₁ y = -1) := by
  have hUo : IsOpen (ball z r) := isOpen_ball
  have hF1 : DifferentiableOn ℂ (deriv F) (ball z r) := hF.deriv hUo
  have hF2 : DifferentiableOn ℂ (deriv (deriv F)) (ball z r) := hF1.deriv hUo
  obtain ⟨s, hs, hs2⟩ := exists_sq_eq_on_ball hr hF1 hF'
  have hs0 : ∀ y ∈ ball z r, s y ≠ 0 := fun y hy h0 => hF' y hy (by rw [← hs2 y hy, h0]; ring)
  -- `2 s s' = F''`
  have hsd : ∀ y ∈ ball z r, deriv s y = deriv (deriv F) y / (2 * s y) := by
    intro y hy
    have hn := hUo.mem_nhds hy
    have hev : (fun v => s v ^ 2) =ᶠ[𝓝 y] deriv F := by
      filter_upwards [hn] with v hv
      exact hs2 v hv
    have h1 : HasDerivAt (fun v => s v ^ 2) _ y := (hs.differentiableAt hn).hasDerivAt.pow 2
    have h2 := h1.deriv
    rw [hev.deriv_eq] at h2
    norm_num at h2
    rw [eq_div_iff (mul_ne_zero two_ne_zero (hs0 y hy))]
    linear_combination -h2
  -- `p = 1/s`
  obtain ⟨p, hp⟩ : ∃ p : ℂ → ℂ, p = fun y => (s y)⁻¹ := ⟨_, rfl⟩
  have hpd : DifferentiableOn ℂ p (ball z r) := by
    rw [hp]
    exact fun y hy => ((hs.differentiableAt (hUo.mem_nhds hy)).inv (hs0 y hy)).differentiableWithinAt
  have hp1 : ∀ y ∈ ball z r, deriv p y = -(deriv (deriv F) y / deriv F y / 2) * p y := by
    intro y hy
    have hn := hUo.mem_nhds hy
    have h1 : HasDerivAt (fun y => (s y)⁻¹) (-deriv s y / s y ^ 2) y :=
      (hs.differentiableAt hn).hasDerivAt.inv (hs0 y hy)
    rw [hp, h1.deriv, hsd y hy, ← hs2 y hy]
    have := hs0 y hy
    field_simp
  have hu : DifferentiableOn ℂ (fun y => deriv (deriv F) y / deriv F y) (ball z r) :=
    hF2.div hF1 hF'
  have hp2 : ∀ y ∈ ball z r, deriv (deriv p) y = -(schwarzianHol F y / 2) * p y := by
    intro y hy
    have hn := hUo.mem_nhds hy
    have hev : deriv p =ᶠ[𝓝 y] fun v => -(deriv (deriv F) v / deriv F v / 2) * p v := by
      filter_upwards [hn] with v hv
      exact hp1 v hv
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun v => -(deriv (deriv F) v / deriv F v / 2) * p v) _ y :=
      (((hu.differentiableAt hn).hasDerivAt.div_const 2).neg).mul (hpd.differentiableAt hn).hasDerivAt
    rw [h1.deriv, hp1 y hy]
    simp only [Pi.neg_apply]
    unfold schwarzianHol
    ring
  -- `q = F p`
  obtain ⟨q, hq⟩ : ∃ q : ℂ → ℂ, q = fun y => F y * p y := ⟨_, rfl⟩
  have hqd : DifferentiableOn ℂ q (ball z r) := by
    rw [hq]
    exact hF.mul hpd
  have hq1 : ∀ y ∈ ball z r, deriv q y = deriv F y * p y + F y * deriv p y := by
    intro y hy
    have hn := hUo.mem_nhds hy
    have h1 : HasDerivAt (fun y => F y * p y) _ y :=
      (hF.differentiableAt hn).hasDerivAt.mul (hpd.differentiableAt hn).hasDerivAt
    rw [hq, h1.deriv]
  have hpd1 : DifferentiableOn ℂ (deriv p) (ball z r) := hpd.deriv hUo
  have hq2 : ∀ y ∈ ball z r, deriv (deriv q) y = -(schwarzianHol F y / 2) * q y := by
    intro y hy
    have hn := hUo.mem_nhds hy
    have hev : deriv q =ᶠ[𝓝 y] fun v => deriv F v * p v + F v * deriv p v := by
      filter_upwards [hn] with v hv
      exact hq1 v hv
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun v => deriv F v * p v + F v * deriv p v) _ y :=
      ((hF1.differentiableAt hn).hasDerivAt.mul (hpd.differentiableAt hn).hasDerivAt).add
        ((hF.differentiableAt hn).hasDerivAt.mul (hpd1.differentiableAt hn).hasDerivAt)
    rw [h1.deriv, hp2 y hy, hp1 y hy, hq]
    have := hF' y hy
    field_simp
    ring
  have hW : ∀ y ∈ ball z r, q y * deriv p y - p y * deriv q y = -1 := by
    intro y hy
    rw [hq1 y hy, hq, hp]
    simp only
    rw [← hs2 y hy]
    have := hs0 y hy
    field_simp
    ring
  refine ⟨q, p, hqd, hpd, hq2, hp2, fun y hy => ?_, fun y _ => by rw [hq], hW⟩
  rw [hp]
  exact inv_ne_zero (hs0 y hy)

/-- The Wronskian of two solutions of `w'' + ½ φ w = 0` is constant on a preconnected open set. -/
theorem wronskian_const_of_ode {y₁ y₂ φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (h₁ : DifferentiableOn ℂ y₁ U) (h₂ : DifferentiableOn ℂ y₂ U)
    (e₁ : ∀ y ∈ U, deriv (deriv y₁) y = -(φ y / 2) * y₁ y)
    (e₂ : ∀ y ∈ U, deriv (deriv y₂) y = -(φ y / 2) * y₂ y) {x₀ : ℂ} (hx₀ : x₀ ∈ U) :
    ∀ y ∈ U, y₁ y * deriv y₂ y - y₂ y * deriv y₁ y =
      y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ := by
  have hd₁ : DifferentiableOn ℂ (deriv y₁) U := h₁.deriv hU
  have hd₂ : DifferentiableOn ℂ (deriv y₂) U := h₂.deriv hU
  have hWd : DifferentiableOn ℂ (fun y => y₁ y * deriv y₂ y - y₂ y * deriv y₁ y) U :=
    (h₁.mul hd₂).sub (h₂.mul hd₁)
  have hW' : EqOn (deriv fun y => y₁ y * deriv y₂ y - y₂ y * deriv y₁ y) 0 U := by
    intro y hy
    have hn := hU.mem_nhds hy
    have h : HasDerivAt (fun y => y₁ y * deriv y₂ y - y₂ y * deriv y₁ y) _ y :=
      ((h₁.differentiableAt hn).hasDerivAt.mul (hd₂.differentiableAt hn).hasDerivAt).sub
        ((h₂.differentiableAt hn).hasDerivAt.mul (hd₁.differentiableAt hn).hasDerivAt)
    rw [h.deriv, e₁ y hy, e₂ y hy]
    simp only [Pi.zero_apply]
    ring
  intro y hy
  exact hU.is_const_of_deriv_eq_zero hUc hWd hW' hy hx₀

/-- **Local uniqueness.**  Two analytic functions with non-vanishing derivatives and the same
Schwarzian near `z` differ by a fractional linear map near `z`: the solutions `(F')^{-1/2}`,
`F (F')^{-1/2}` and `(G')^{-1/2}`, `G (G')^{-1/2}` of the same equation are related by constant
Wronskians. -/
theorem exists_mobius_of_schwarzianHol_eventuallyEq {F G : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hF' : deriv F z ≠ 0) (hG : AnalyticAt ℂ G z) (hG' : deriv G z ≠ 0)
    (hS : schwarzianHol F =ᶠ[𝓝 z] schwarzianHol G) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ F =ᶠ[𝓝 z] fun y => (a * G y + b) / (c * G y + d) := by
  have hev : ∀ᶠ y in 𝓝 z, AnalyticAt ℂ F y ∧ AnalyticAt ℂ G y ∧ deriv F y ≠ 0 ∧
      deriv G y ≠ 0 ∧ schwarzianHol F y = schwarzianHol G y := by
    filter_upwards [hF.eventually_analyticAt, hG.eventually_analyticAt,
      hF.deriv.continuousAt.eventually_ne hF', hG.deriv.continuousAt.eventually_ne hG', hS]
      with y h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hBc : IsPreconnected (ball z r) := (convex_ball z r).isPreconnected
  have hzB : z ∈ ball z r := mem_ball_self hr
  have hFd : DifferentiableOn ℂ F (ball z r) := fun y hy =>
    (hball y hy).1.differentiableAt.differentiableWithinAt
  have hGd : DifferentiableOn ℂ G (ball z r) := fun y hy =>
    (hball y hy).2.1.differentiableAt.differentiableWithinAt
  obtain ⟨y₁, y₂, hy₁, hy₂, e₁, e₂, hy₂0, hy₁F, W₁₂⟩ :=
    exists_solutions_on_ball hr hFd fun y hy => (hball y hy).2.2.1
  obtain ⟨y₃, y₄, hy₃, hy₄, e₃, e₄, hy₄0, hy₃G, W₃₄⟩ :=
    exists_solutions_on_ball hr hGd fun y hy => (hball y hy).2.2.2.1
  have e₃' : ∀ y ∈ ball z r, deriv (deriv y₃) y = -(schwarzianHol F y / 2) * y₃ y :=
    fun y hy => by rw [(hball y hy).2.2.2.2]; exact e₃ y hy
  have e₄' : ∀ y ∈ ball z r, deriv (deriv y₄) y = -(schwarzianHol F y / 2) * y₄ y :=
    fun y hy => by rw [(hball y hy).2.2.2.2]; exact e₄ y hy
  obtain ⟨κ₁₄, hκ₁₄⟩ : ∃ κ : ℂ, κ = y₁ z * deriv y₄ z - y₄ z * deriv y₁ z := ⟨_, rfl⟩
  obtain ⟨κ₃₁, hκ₃₁⟩ : ∃ κ : ℂ, κ = y₃ z * deriv y₁ z - y₁ z * deriv y₃ z := ⟨_, rfl⟩
  obtain ⟨κ₂₄, hκ₂₄⟩ : ∃ κ : ℂ, κ = y₂ z * deriv y₄ z - y₄ z * deriv y₂ z := ⟨_, rfl⟩
  obtain ⟨κ₃₂, hκ₃₂⟩ : ∃ κ : ℂ, κ = y₃ z * deriv y₂ z - y₂ z * deriv y₃ z := ⟨_, rfl⟩
  refine ⟨κ₁₄, κ₃₁, κ₂₄, κ₃₂, ?_, ?_⟩
  · -- the Plücker relation: the determinant is the product of the two Wronskians
    have h12 := W₁₂ z hzB
    have h34 := W₃₄ z hzB
    have hpl : κ₁₄ * κ₃₂ - κ₃₁ * κ₂₄ = (y₁ z * deriv y₂ z - y₂ z * deriv y₁ z) *
        (y₃ z * deriv y₄ z - y₄ z * deriv y₃ z) := by
      rw [hκ₁₄, hκ₃₁, hκ₂₄, hκ₃₂]
      ring
    rw [hpl, h12, h34]
    norm_num
  · filter_upwards [ball_mem_nhds z hr] with y hy
    have c14 := wronskian_const_of_ode isOpen_ball hBc hy₁ hy₄ e₁ e₄' hzB y hy
    have c31 := wronskian_const_of_ode isOpen_ball hBc hy₃ hy₁ e₃' e₁ hzB y hy
    have c24 := wronskian_const_of_ode isOpen_ball hBc hy₂ hy₄ e₂ e₄' hzB y hy
    have c32 := wronskian_const_of_ode isOpen_ball hBc hy₃ hy₂ e₃' e₂ hzB y hy
    rw [← hκ₁₄] at c14
    rw [← hκ₃₁] at c31
    rw [← hκ₂₄] at c24
    rw [← hκ₃₂] at c32
    have w34 := W₃₄ y hy
    have r1 : y₁ y * (-1) = κ₁₄ * y₃ y + κ₃₁ * y₄ y := by
      rw [← w34, ← c14, ← c31]
      ring
    have r2 : y₂ y * (-1) = κ₂₄ * y₃ y + κ₃₂ * y₄ y := by
      rw [← w34, ← c24, ← c32]
      ring
    rw [hy₁F y hy, hy₃G y hy] at r1
    rw [hy₃G y hy] at r2
    have hy2 := hy₂0 y hy
    have hy4 := hy₄0 y hy
    have hden : κ₂₄ * G y + κ₃₂ ≠ 0 := by
      intro h0
      apply hy2
      linear_combination -r2 - y₄ y * h0
    show F y = (κ₁₄ * G y + κ₃₁) / (κ₂₄ * G y + κ₃₂)
    rw [eq_div_iff hden]
    apply mul_right_cancel₀ hy4
    linear_combination (-F y) * r2 + r1

/-! ### Uniqueness in Theorem 19.1: from local to global -/

/-- Near every point of `D`, `f` is a fractional linear function of `g`. -/
theorem exists_mobius_eventuallyEq_of_schwarzian_eq {f g : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hf : IsLocUnivMero f D) (hg : IsLocUnivMero g D)
    (h : ∀ z ∈ D, schwarzian f z = schwarzian g z) {z : ℂ} (hz : z ∈ D) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ f =ᶠ[𝓝[≠] z] fun y => (a * g y + b) / (c * g y + d) := by
  obtain ⟨F, hFa, hF', hSF, hfF⟩ := exists_chart_of_isLocUnivMero hf hz
  obtain ⟨G, hGa, hG', hSG, hgG⟩ := exists_chart_of_isLocUnivMero hg hz
  have hS : schwarzianHol F =ᶠ[𝓝 z] schwarzianHol G := by
    filter_upwards [hSF, hSG, hD.mem_nhds hz] with y e1 e2 hy
    rw [← e1, ← e2, h y hy]
  obtain ⟨a, b, c, d, hdet, hFG⟩ := exists_mobius_of_schwarzianHol_eventuallyEq hFa hF' hGa hG' hS
  have hFG' : F =ᶠ[𝓝[≠] z] fun y => (a * G y + b) / (c * G y + d) :=
    hFG.filter_mono nhdsWithin_le_nhds
  have hG0 := eventually_ne_zero_of_deriv_ne_zero hGa hG'
  rcases hfF with hfF | hfF <;> rcases hgG with hgG | hgG
  · refine ⟨a, b, c, d, hdet, ?_⟩
    filter_upwards [hfF, hFG', hgG] with y e1 e2 e3
    rw [e1, e2, e3]
  · refine ⟨b, a, d, c, fun hc => hdet (by linear_combination -hc), ?_⟩
    filter_upwards [hfF, hFG', hgG, hG0] with y e1 e2 e3 e4
    rw [e1, e2, e3, mobius_inv_arg e4]
  · refine ⟨c, d, a, b, fun hc => hdet (by linear_combination -hc), ?_⟩
    filter_upwards [hfF, hFG', hgG] with y e1 e2 e3
    rw [e1, e2, e3, inv_div]
  · refine ⟨d, c, b, a, fun hc => hdet (by linear_combination hc), ?_⟩
    filter_upwards [hfF, hFG', hgG, hG0] with y e1 e2 e3 e4
    rw [e1, e2, e3, inv_div, mobius_inv_arg e4]

/-- Equality on a punctured neighbourhood of `z` persists on punctured neighbourhoods of all nearby
points. -/
theorem eventually_eventuallyEq_nhdsNE {f F : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝[≠] z] F) :
    ∀ᶠ w in 𝓝 z, f =ᶠ[𝓝[≠] w] F := by
  have h' := (eventually_nhdsWithin_iff.1 h).eventually_nhds
  filter_upwards [h'] with w hw
  rcases eq_or_ne w z with rfl | hwz
  · exact h
  · refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [hw, eventually_ne_nhds hwz] with y hy hyz
    exact hy hyz

/-- **Theorem 19.1** (uniqueness): two locally univalent meromorphic functions in a domain with
the same Schwarzian derivative differ by a fractional linear transformation.

As in the book, `f` and `g` are compared through solutions of `w'' + ½ S_f w = 0`, but no uniqueness
theorem for that equation is needed.  Near each point, `(F')^{-1/2}` and `F (F')^{-1/2}` solve it,
for `F = f`, or `F = 1/f` at a pole (`exists_solutions_on_ball`).  The identity
`y · W(u, v) = W(y, v) u + W(u, y) v` with constant Wronskians then writes `f` as a fractional linear
function of `g` near the point (`exists_mobius_eventuallyEq_of_schwarzian_eq`).  Two fractional
linear maps agreeing near a point coincide (`mobius_eq_of_eventually_nhdsNE`), so the local maps
patch over the connected domain.  The proof is not routed through `f ∘ g⁻¹`: `g` is only *locally*
univalent, so it has no global inverse on `D`. -/
theorem thm19_1_unique {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {f g : ℂ → ℂ}
    (hf : IsLocUnivMero f D) (hg : IsLocUnivMero g D) (h : ∀ z ∈ D, schwarzian f z = schwarzian g z) :
    ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ D, AnalyticAt ℂ f z → AnalyticAt ℂ g z →
      c * g z + d ≠ 0 → f z = (a * g z + b) / (c * g z + d) := by
  obtain ⟨z₀, hz₀⟩ := hDc.nonempty
  obtain ⟨a, b, c, d, hdet, hloc₀⟩ := exists_mobius_eventuallyEq_of_schwarzian_eq hD hf hg h hz₀
  -- the points near which `f = M ∘ g` for this fixed `M`, and those near which `f = N ∘ g` for some
  -- other `N`, are complementary open subsets of the connected set `D`
  have huo : IsOpen (D ∩ {z | f =ᶠ[𝓝[≠] z] fun y => (a * g y + b) / (c * g y + d)}) := by
    refine isOpen_iff_mem_nhds.2 fun z hz => ?_
    filter_upwards [hD.mem_nhds hz.1, eventually_eventuallyEq_nhdsNE hz.2] with w hw1 hw2
    exact ⟨hw1, hw2⟩
  have hvo : IsOpen (D ∩ {z | ∃ a' b' c' d' : ℂ, a' * d' - b' * c' ≠ 0 ∧
      ¬ (∀ x, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d')) ∧
      f =ᶠ[𝓝[≠] z] fun y => (a' * g y + b') / (c' * g y + d')}) := by
    refine isOpen_iff_mem_nhds.2 fun z hz => ?_
    obtain ⟨a', b', c', d', hdet', hne, hrel⟩ := hz.2
    filter_upwards [hD.mem_nhds hz.1, eventually_eventuallyEq_nhdsNE hrel] with w hw1 hw2
    exact ⟨hw1, a', b', c', d', hdet', hne, hw2⟩
  have hdisj : Disjoint (D ∩ {z | f =ᶠ[𝓝[≠] z] fun y => (a * g y + b) / (c * g y + d)})
      (D ∩ {z | ∃ a' b' c' d' : ℂ, a' * d' - b' * c' ≠ 0 ∧
        ¬ (∀ x, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d')) ∧
        f =ᶠ[𝓝[≠] z] fun y => (a' * g y + b') / (c' * g y + d')}) := by
    rw [Set.disjoint_left]
    rintro z ⟨hzD, hzu⟩ ⟨-, a', b', c', d', hdet', hne, hrel⟩
    have hzu' : f =ᶠ[𝓝[≠] z] fun y => (a * g y + b) / (c * g y + d) := hzu
    exact hne (mobius_eq_of_comp_eventuallyEq hg hzD hdet hdet' (hzu'.symm.trans hrel))
  have hcover : D ⊆ (D ∩ {z | f =ᶠ[𝓝[≠] z] fun y => (a * g y + b) / (c * g y + d)}) ∪
      (D ∩ {z | ∃ a' b' c' d' : ℂ, a' * d' - b' * c' ≠ 0 ∧
        ¬ (∀ x, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d')) ∧
        f =ᶠ[𝓝[≠] z] fun y => (a' * g y + b') / (c' * g y + d')}) := by
    intro z hz
    obtain ⟨a', b', c', d', hdet', hrel⟩ := exists_mobius_eventuallyEq_of_schwarzian_eq hD hf hg h hz
    by_cases hsame : ∀ x, (a * x + b) / (c * x + d) = (a' * x + b') / (c' * x + d')
    · left
      refine ⟨hz, ?_⟩
      filter_upwards [hrel] with y hy
      rw [hy, hsame]
    · exact Or.inr ⟨hz, a', b', c', d', hdet', hsame, hrel⟩
  have hsub := hDc.isPreconnected.subset_left_of_subset_union huo hvo hdisj hcover
    ⟨z₀, hz₀, hz₀, hloc₀⟩
  refine ⟨a, b, c, d, hdet, fun z hz hfz hgz hden => ?_⟩
  have hrel : f =ᶠ[𝓝[≠] z] fun y => (a * g y + b) / (c * g y + d) := (hsub hz).2
  have h1 : Tendsto f (𝓝[≠] z) (𝓝 (f z)) := hfz.continuousAt.continuousWithinAt
  have hcont : ContinuousAt (fun y => (a * g y + b) / (c * g y + d)) z :=
    ((continuousAt_const.mul hgz.continuousAt).add continuousAt_const).div
      ((continuousAt_const.mul hgz.continuousAt).add continuousAt_const) hden
  have h2 : Tendsto f (𝓝[≠] z) (𝓝 ((a * g z + b) / (c * g z + d))) :=
    hcont.continuousWithinAt.tendsto.congr' hrel.symm
  exact tendsto_nhds_unique h1 h2

/-! ### Reductions for Theorem 19.2 (`knr_`)

Kraus's inequality is Möbius invariant.  A univalent meromorphic `f` in `Δ` omits a finite value
`w₀` when it has a pole (Liouville, applied to the inverse of `f` on `Δ ∖ {z₀}`), so
`F = 1/(f - w₀)` — with the value `0` at the pole — is holomorphic and univalent with the same
Schwarzian.  A disc automorphism moves the point to `0`, an affine map normalises `F(0) = 0`,
`F'(0) = 1`, and `kraus_nehari_coeff` (the area theorem for one coefficient) finishes. -/

/-- An injective holomorphic map of a nonempty open subset of `Δ` omits a value (Liouville). -/
theorem knr_exists_omitted {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : U ⊆ unitDisc)
    (hd : DifferentiableOn ℂ f U) (hinj : InjOn f U) : ∃ w₀ : ℂ, ∀ w ∈ U, f w ≠ w₀ := by
  by_contra hcon
  simp only [not_exists, not_forall, not_not, exists_prop] at hcon
  have himg : f '' U = univ := Set.eq_univ_of_forall fun v => hcon v
  have hconf : IsConformalOnto f U univ := ⟨hd, hinj, himg⟩
  obtain ⟨hψd, -, hψimg⟩ := hconf.symm hU
  have hψ : Differentiable ℂ (Function.invFunOn f U) := differentiableOn_univ.1 hψd
  have hb : Bornology.IsBounded (Set.range (Function.invFunOn f U)) := by
    rw [← Set.image_univ, hψimg]
    exact Metric.isBounded_ball.subset hUb
  have h01 := hψ.apply_eq_apply_of_bounded hb 0 1
  have e0 : f (Function.invFunOn f U 0) = 0 := Function.invFunOn_eq (hcon 0)
  have e1 : f (Function.invFunOn f U 1) = 1 := Function.invFunOn_eq (hcon 1)
  rw [h01] at e0
  exact zero_ne_one (e0.symm.trans e1)

/-- A univalent meromorphic `f` in `Δ` is, up to a Möbius transformation, a univalent holomorphic
function `F` with the same Schwarzian. -/
theorem knr_exists_holomorphic {f : ℂ → ℂ} (hf : IsUnivMero f unitDisc) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F unitDisc ∧ InjOn F unitDisc ∧
      ∀ w ∈ unitDisc, schwarzian F w = schwarzian f w := by
  obtain ⟨hloc, hinj, hpole⟩ := hf
  by_cases hall : ∀ w ∈ unitDisc, AnalyticAt ℂ f w
  · refine ⟨f, fun w hw => (hall w hw).differentiableAt.differentiableWithinAt, ?_, fun _ _ => rfl⟩
    intro w₁ hw₁ w₂ hw₂ he
    exact hinj ⟨hw₁, hall w₁ hw₁⟩ ⟨hw₂, hall w₂ hw₂⟩ he
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨z₀, hz₀, hA₀⟩ := hall
    -- every other point is analytic
    have hana : ∀ w ∈ unitDisc, w ≠ z₀ → AnalyticAt ℂ f w := fun w hw hne => by
      by_contra hA
      exact hne (hpole ⟨hw, hA⟩ ⟨hz₀, hA₀⟩)
    -- the chart at the pole: `f = 1/u` near `z₀`, `u z₀ = 0`, `u' z₀ ≠ 0`
    obtain ⟨u, hu, hu', -, hchart⟩ := exists_chart_of_isLocUnivMero hloc hz₀
    have hord : meromorphicOrderAt f z₀ < 0 := by
      rcases hloc.2 z₀ hz₀ with ⟨hA, -⟩ | ⟨h, -, -⟩
      · exact absurd hA hA₀
      · exact h
    have hfu : f =ᶠ[𝓝[≠] z₀] fun y => (u y)⁻¹ := by
      rcases hchart with h | h
      · exfalso
        rw [meromorphicOrderAt_congr h] at hord
        exact absurd hord (not_lt.2 hu.meromorphicOrderAt_nonneg)
      · exact h
    have hu0 : u z₀ = 0 := by
      by_contra hne
      rw [meromorphicOrderAt_congr hfu] at hord
      exact absurd hord (not_lt.2 (hu.inv hne).meromorphicOrderAt_nonneg)
    have hune : ∀ᶠ y in 𝓝[≠] z₀, u y ≠ 0 := by
      refine hu.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hcon => hu' ?_
      have hz0 : u =ᶠ[𝓝 z₀] fun _ => (0 : ℂ) := hcon
      rw [hz0.deriv_eq, deriv_const]
    -- the omitted value
    have hUo : IsOpen (unitDisc \ {z₀}) := isOpen_ball.sdiff isClosed_singleton
    obtain ⟨w₀, hw₀⟩ := knr_exists_omitted hUo Set.diff_subset
      (fun w hw => (hana w hw.1 hw.2).differentiableAt.differentiableWithinAt)
      (fun w₁ hw₁ w₂ hw₂ he => hinj ⟨hw₁.1, hana _ hw₁.1 hw₁.2⟩ ⟨hw₂.1, hana _ hw₂.1 hw₂.2⟩ he)
    have hne_w₀ : ∀ w ∈ unitDisc, w ≠ z₀ → f w - w₀ ≠ 0 := fun w hw hne =>
      sub_ne_zero.2 (hw₀ w ⟨hw, hne⟩)
    -- the holomorphic replacement `F = 1/(f - w₀)`, with the value `0` at the pole
    have hFeq : ∀ w, w ≠ z₀ → Function.update (fun y => (f y - w₀)⁻¹) z₀ 0 w = (f w - w₀)⁻¹ :=
      fun w hw => Function.update_of_ne hw _ _
    have hFz₀ : Function.update (fun y => (f y - w₀)⁻¹) z₀ 0 z₀ = 0 := Function.update_self _ _ _
    -- off `z₀`, `F` is a Möbius transform of `f`
    have hgerm : ∀ w ∈ unitDisc, Function.update (fun y => (f y - w₀)⁻¹) z₀ 0 =ᶠ[𝓝[≠] w]
        fun y => (0 * f y + 1) / (1 * f y + -w₀) := by
      intro w _
      have hev : ∀ᶠ y in 𝓝[≠] w, y ≠ z₀ := by
        rcases eq_or_ne w z₀ with rfl | hne
        · exact self_mem_nhdsWithin
        · exact (eventually_ne_nhds hne).filter_mono nhdsWithin_le_nhds
      filter_upwards [hev] with y hy
      rw [hFeq y hy]
      simp only [zero_mul, zero_add, one_mul, one_div, sub_eq_add_neg]
    have hS : ∀ w ∈ unitDisc, schwarzian (Function.update (fun y => (f y - w₀)⁻¹) z₀ 0) w =
        schwarzian f w := fun w hw => by
      rw [schwarzian_congr (hgerm w hw),
        schwarzian_mobius_comp hloc (by norm_num : (0 : ℂ) * -w₀ - 1 * 1 ≠ 0) hw]
    -- analyticity
    have hFan : ∀ w ∈ unitDisc, AnalyticAt ℂ (Function.update (fun y => (f y - w₀)⁻¹) z₀ 0) w := by
      intro w hw
      rcases eq_or_ne w z₀ with rfl | hne
      · -- near the pole `F = u/(1 - w₀ u)`
        have hG : AnalyticAt ℂ (fun y => u y / (1 - w₀ * u y)) w :=
          hu.div (analyticAt_const.sub (analyticAt_const.mul hu)) (by rw [hu0]; simp)
        refine hG.congr ?_
        have h1' : ∀ᶠ y in 𝓝[≠] w,
            u y / (1 - w₀ * u y) = Function.update (fun y => (f y - w₀)⁻¹) w 0 y := by
          filter_upwards [hfu, hune, self_mem_nhdsWithin] with y hy hy0 hyw
          rw [hFeq y hyw, hy]
          field_simp
        have h1 := eventually_nhdsWithin_iff.1 h1'
        filter_upwards [h1] with y hy
        by_cases hyw : y = w
        · subst hyw
          simp [hu0]
        · exact hy hyw
      · have hA := hana w hw hne
        refine ((hA.sub analyticAt_const).inv (hne_w₀ w hw hne)).congr ?_
        filter_upwards [eventually_ne_nhds hne] with y hy
        exact (hFeq y hy).symm
    -- injectivity
    have hFinj : InjOn (Function.update (fun y => (f y - w₀)⁻¹) z₀ 0) unitDisc := by
      intro w₁ hw₁ w₂ hw₂ he
      rcases eq_or_ne w₁ z₀ with h1 | h1 <;> rcases eq_or_ne w₂ z₀ with h2 | h2
      · rw [h1, h2]
      · rw [h1, hFz₀, hFeq w₂ h2, eq_comm, inv_eq_zero] at he
        exact absurd he (hne_w₀ w₂ hw₂ h2)
      · rw [h2, hFz₀, hFeq w₁ h1, inv_eq_zero] at he
        exact absurd he (hne_w₀ w₁ hw₁ h1)
      · rw [hFeq w₁ h1, hFeq w₂ h2, inv_inj, sub_left_inj] at he
        exact hinj ⟨hw₁, hana _ hw₁ h1⟩ ⟨hw₂, hana _ hw₂ h2⟩ he
    exact ⟨_, fun w hw => (hFan w hw).differentiableAt.differentiableWithinAt, hFinj, hS⟩

/-- Kraus's bound at a point of `Δ` for a univalent holomorphic `F`: move the point to `0` by a
disc automorphism, normalise, and apply `kraus_nehari_coeff`. -/
theorem knr_holomorphic_bound {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F unitDisc)
    (hinj : InjOn F unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖schwarzian F z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ 6 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hDo : IsOpen unitDisc := isOpen_ball
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hFan : ∀ w ∈ unitDisc, AnalyticAt ℂ F w := fun w hw => hd.analyticAt (hDo.mem_nhds hw)
  have hF' : ∀ w ∈ unitDisc, deriv F w ≠ 0 := fun w hw => deriv_ne_zero_of_injOn hDo hd hinj hw
  -- the disc automorphism `φ = blaschke (-z)`, `φ 0 = z`, `φ' 0 = 1 - |z|²`
  have ha1 : ‖-z‖ < 1 := by rw [norm_neg]; exact hz1
  have hφ0 : blaschke (-z) 0 = z := by simp [blaschke]
  have hφ'0 : deriv (blaschke (-z)) 0 = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [(hasDerivAt_blaschke ha1 (by simp)).deriv]
    simp only [map_neg, mul_neg, neg_mul, neg_neg, mul_zero, sub_zero, one_pow, div_one,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hφmaps : ∀ w ∈ unitDisc, blaschke (-z) w ∈ unitDisc := fun w hw =>
    mem_ball_zero_iff.2 (blaschke_mem_unitDisc ha1 (mem_ball_zero_iff.1 hw))
  have hφinj : InjOn (blaschke (-z)) unitDisc := by
    intro w₁ hw₁ w₂ hw₂ he
    have := congrArg (blaschke (- -z)) he
    rwa [blaschke_neg_blaschke ha1 (mem_ball_zero_iff.1 hw₁),
      blaschke_neg_blaschke ha1 (mem_ball_zero_iff.1 hw₂)] at this
  have hφan : ∀ w ∈ unitDisc, AnalyticAt ℂ (blaschke (-z)) w := fun w hw =>
    (differentiableOn_blaschke ha1).analyticAt (hDo.mem_nhds hw)
  have hφmob : blaschke (-z) = fun w => (1 * w + z) / (conj z * w + 1) := by
    funext w
    simp only [blaschke, map_neg, sub_neg_eq_add, neg_mul, one_mul]
    ring
  have hdet : (1 : ℂ) * 1 - z * conj z ≠ 0 := by
    rw [Complex.mul_conj, one_mul, Complex.normSq_eq_norm_sq]
    exact_mod_cast hpos.ne'
  -- `F₁ = F ∘ φ`: the chain rule at `0`
  have hF₁an : ∀ w ∈ unitDisc, AnalyticAt ℂ (F ∘ blaschke (-z)) w := fun w hw =>
    (hFan _ (hφmaps w hw)).comp (hφan w hw)
  have hF₁inj : InjOn (F ∘ blaschke (-z)) unitDisc := fun w₁ hw₁ w₂ hw₂ he =>
    hφinj hw₁ hw₂ (hinj (hφmaps w₁ hw₁) (hφmaps w₂ hw₂) he)
  have hφ'ne : deriv (blaschke (-z)) 0 ≠ 0 := by
    rw [hφ'0]
    exact_mod_cast hpos.ne'
  have hchain : schwarzian (F ∘ blaschke (-z)) 0 =
      schwarzian F z * ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
    have := eq19_1_chain_rule (hφan 0 h0) hφ'ne (hFan _ (hφmaps 0 h0)) (hF' _ (hφmaps 0 h0))
    rw [hφ0, hφ'0] at this
    rw [this, hφmob, schwarzian_mobius hdet 0, add_zero]
  have hF₁' : deriv (F ∘ blaschke (-z)) 0 ≠ 0 := by
    have hd1 : HasDerivAt (F ∘ blaschke (-z))
        (deriv F (blaschke (-z) 0) * deriv (blaschke (-z)) 0) 0 :=
      (hFan _ (hφmaps 0 h0)).differentiableAt.hasDerivAt.comp 0
        (hφan 0 h0).differentiableAt.hasDerivAt
    rw [hd1.deriv, hφ0]
    exact mul_ne_zero (hF' z hz) hφ'ne
  -- `F₂ = (F₁ - F₁ 0)/F₁' 0`: the normalisation
  set F₂ : ℂ → ℂ := fun w =>
    ((F ∘ blaschke (-z)) w - (F ∘ blaschke (-z)) 0) / deriv (F ∘ blaschke (-z)) 0 with hF₂
  have hF₂an : ∀ w ∈ unitDisc, AnalyticAt ℂ F₂ w :=
    fun w hw => ((hF₁an w hw).sub analyticAt_const).div analyticAt_const hF₁'
  have hF₂inj : InjOn F₂ unitDisc := by
    intro w₁ hw₁ w₂ hw₂ he
    have he' : (F ∘ blaschke (-z)) w₁ = (F ∘ blaschke (-z)) w₂ := by
      have := he
      simp only [hF₂] at this
      rwa [div_left_inj' hF₁', sub_left_inj] at this
    exact hF₁inj hw₁ hw₂ he'
  have hF₂0 : F₂ 0 = 0 := by
    simp [hF₂]
  have hF₂d : HasDerivAt F₂ (deriv (F ∘ blaschke (-z)) 0 / deriv (F ∘ blaschke (-z)) 0) 0 :=
    ((hF₁an 0 h0).differentiableAt.hasDerivAt.sub_const _).div_const _
  have hF₂'0 : deriv F₂ 0 = 1 := by
    rw [hF₂d.deriv, div_self hF₁']
  have hF₂S : schwarzian F₂ 0 = schwarzian (F ∘ blaschke (-z)) 0 := by
    have hmob := schwarzian_mobius_comp_analytic (hF₁an 0 h0) hF₁'
      (a := (deriv (F ∘ blaschke (-z)) 0)⁻¹) (b := -(F ∘ blaschke (-z)) 0 *
        (deriv (F ∘ blaschke (-z)) 0)⁻¹) (c := 0) (d := 1) (by simp [hF₁'])
    rw [← hmob]
    congr 1
    funext w
    rw [hF₂]
    field_simp
    ring
  -- the Schwarzian at `0` in terms of the derivatives, and the leaf
  have hval : schwarzian F₂ 0 =
      deriv (deriv (deriv F₂)) 0 - (3 / 2) * deriv (deriv F₂) 0 ^ 2 := by
    have hA := hF₂an 0 h0
    rw [schwarzian_of_analyticAt hA]
    unfold schwarzianHol
    have hq : HasDerivAt (fun w => deriv (deriv F₂) w / deriv F₂ w) _ 0 :=
      (hA.deriv.deriv.differentiableAt.hasDerivAt).div
        (hA.deriv.differentiableAt.hasDerivAt) (by rw [hF₂'0]; exact one_ne_zero)
    rw [hq.deriv, hF₂'0]
    ring
  have hbound := kraus_nehari_coeff (fun w hw => (hF₂an w hw).differentiableAt.differentiableWithinAt)
    hF₂inj hF₂0 hF₂'0
  rw [← hval, hF₂S, hchain, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hpos.le] at hbound
  exact hbound

/-- **Theorem 19.2** (Nehari): a univalent meromorphic function in the unit disc satisfies
`|S_f(z)| (1 - |z|²)² ≤ 6`.

The book cites this (Kraus) without proof.  Here: if `f` has a pole it omits a finite value `w₀`
(Liouville, applied to the inverse of `f` on the punctured disc), so `1/(f - w₀)` is holomorphic
and univalent with the same Schwarzian; a disc automorphism moves `z` to `0` and an affine map
normalises `F(0) = 0`, `F'(0) = 1`, where `S_F(0) = F'''(0) - (3/2) F''(0)²`.  The bound
`|F'''(0) - (3/2) F''(0)²| ≤ 6` is `kraus_nehari_coeff` (`Lemmas/KrausNehari.lean`): the area
theorem for the single coefficient `b₁` of `1/F(1/ζ)`, proved by the change of variables formula,
a two-mode Bessel inequality on circles and a pointwise ellipse containment. -/
theorem thm19_2_nehari {f : ℂ → ℂ} (hf : IsUnivMero f unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖schwarzian f z‖ * (1 - ‖z‖ ^ 2) ^ 2 ≤ 6 := by
  obtain ⟨F, hd, hinj, hS⟩ := knr_exists_holomorphic hf
  rw [← hS z hz]
  exact knr_holomorphic_bound hd hinj hz

/-- The norm `‖S_f‖_D = sup_{z ∈ D} |S_f(z)| η_D(z)⁻²` (§19.3). -/
def schwarzianNorm (f : ℂ → ℂ) (D : Set ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ D, ENNReal.ofReal (‖schwarzian f z‖ / poincareDensity D z ^ 2)

/-- The norm `‖φ‖_D = sup_{z ∈ D} |φ(z)| η_D(z)⁻²` on the space `A(D)` of holomorphic functions. -/
def hyperbolicSupNorm (φ : ℂ → ℂ) (D : Set ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ D, ENNReal.ofReal (‖φ z‖ / poincareDensity D z ^ 2)

/-- (19.4)–(19.5): for univalent `f` in `Δ`, `‖S_f‖_Δ ≤ 3/2`. -/
theorem eq19_5 {f : ℂ → ℂ} (hf : IsUnivMero f unitDisc) :
    schwarzianNorm f unitDisc ≤ ENNReal.ofReal (3 / 2) := by
  refine iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
  have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hη : poincareDensity unitDisc z ^ 2 = 4 / (1 - ‖z‖ ^ 2) ^ 2 := by
    rw [poincareDensity_unitDisc hz, poincareDensityDisc, div_pow]
    norm_num
  rw [hη, div_div_eq_mul_div]
  have hne := thm19_2_nehari hf hz
  linarith

/-- The derivative of the Koebe function: `k' = (1 + z)/(1 - z)³`. -/
theorem hasDerivAt_koebe {z : ℂ} (hz : (1 : ℂ) - z ≠ 0) :
    HasDerivAt (fun w : ℂ => w / (1 - w) ^ 2) ((1 + z) / (1 - z) ^ 3) z := by
  have h0 : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := HasDerivAt.const_sub 1 h0
  have h2 : HasDerivAt (fun w : ℂ => (1 - w) ^ 2) (-2 * (1 - z)) z := by
    convert h1.pow 2 using 1
    push_cast
    ring
  convert h0.div h2 (pow_ne_zero 2 hz) using 1
  field_simp
  ring

/-- The second derivative of the Koebe function: `k'' = (4 + 2z)/(1 - z)⁴`. -/
theorem hasDerivAt_koebe_deriv {z : ℂ} (hz : (1 : ℂ) - z ≠ 0) :
    HasDerivAt (fun w : ℂ => (1 + w) / (1 - w) ^ 3) ((4 + 2 * z) / (1 - z) ^ 4) z := by
  have h0 : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := HasDerivAt.const_sub 1 h0
  have h2 : HasDerivAt (fun w : ℂ => (1 - w) ^ 3) (-3 * (1 - z) ^ 2) z := by
    convert h1.pow 3 using 1
    push_cast
    ring
  have h3 : HasDerivAt (fun w : ℂ => 1 + w) 1 z := HasDerivAt.const_add 1 h0
  convert h3.div h2 (pow_ne_zero 3 hz) using 1
  field_simp
  ring

/-- The derivative of the logarithmic derivative `k''/k' = (4 + 2z)/(1 - z²)` of the Koebe
function. -/
theorem hasDerivAt_koebe_logDeriv {z : ℂ} (hz : (1 : ℂ) - z ^ 2 ≠ 0) :
    HasDerivAt (fun w : ℂ => (4 + 2 * w) / (1 - w ^ 2))
      ((2 + 8 * z + 2 * z ^ 2) / (1 - z ^ 2) ^ 2) z := by
  have h0 : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
  have h1 : HasDerivAt (fun w : ℂ => 4 + 2 * w) 2 z := by
    convert HasDerivAt.const_add 4 (HasDerivAt.const_mul (2 : ℂ) h0) using 1
    ring
  have h2 : HasDerivAt (fun w : ℂ => 1 - w ^ 2) (-(2 * z)) z := by
    convert HasDerivAt.const_sub 1 (h0.pow 2) using 1
    push_cast
    ring
  convert h1.div h2 hz using 1
  field_simp
  ring

/-- §19.3: the Schwarzian derivative of the Koebe function is `-6/(1 - z²)²`. -/
theorem schwarzian_koebe {z : ℂ} (hz : z ∈ unitDisc) :
    schwarzian (fun w => w / (1 - w) ^ 2) z = -6 / (1 - z ^ 2) ^ 2 := by
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  -- the two linear factors do not vanish on a neighbourhood of `z`
  have hfac : ∀ w : ℂ, ‖w‖ < 1 → (1 : ℂ) - w ≠ 0 ∧ (1 : ℂ) + w ≠ 0 ∧ (1 : ℂ) - w ^ 2 ≠ 0 := by
    intro w hw
    have h1 : (1 : ℂ) - w ≠ 0 := fun hcon => by
      rw [show w = 1 by linear_combination -hcon] at hw; simp at hw
    have h2 : (1 : ℂ) + w ≠ 0 := fun hcon => by
      rw [show w = -1 by linear_combination hcon] at hw; simp at hw
    refine ⟨h1, h2, fun hcon => ?_⟩
    rcases mul_eq_zero.mp (show ((1 : ℂ) - w) * (1 + w) = 0 by linear_combination hcon) with h | h
    · exact h1 h
    · exact h2 h
  have hnear : ∀ᶠ w in 𝓝 z, ‖w‖ < 1 := by
    filter_upwards [isOpen_ball.eventually_mem (show z ∈ ball (0 : ℂ) 1 from hz)] with w hw
    exact mem_ball_zero_iff.mp hw
  -- first derivative, on a neighbourhood
  have hd1 : deriv (fun w : ℂ => w / (1 - w) ^ 2) =ᶠ[𝓝 z] fun w => (1 + w) / (1 - w) ^ 3 := by
    filter_upwards [hnear] with w hw
    exact (hasDerivAt_koebe (hfac w hw).1).deriv
  -- second derivative, on a neighbourhood
  have hd2 : deriv (deriv (fun w : ℂ => w / (1 - w) ^ 2)) =ᶠ[𝓝 z]
      fun w => (4 + 2 * w) / (1 - w) ^ 4 := by
    filter_upwards [hnear, hd1.eventually_nhds] with w hw hev
    have hev' : deriv (fun w : ℂ => w / (1 - w) ^ 2) =ᶠ[𝓝 w] fun v => (1 + v) / (1 - v) ^ 3 := hev
    rw [hev'.deriv_eq]
    exact (hasDerivAt_koebe_deriv (hfac w hw).1).deriv
  -- the logarithmic derivative
  have hq : (fun w => deriv (deriv (fun w : ℂ => w / (1 - w) ^ 2)) w
      / deriv (fun w : ℂ => w / (1 - w) ^ 2) w) =ᶠ[𝓝 z] fun w => (4 + 2 * w) / (1 - w ^ 2) := by
    filter_upwards [hnear, hd1, hd2] with w hw e1 e2
    obtain ⟨h1, h2, h3⟩ := hfac w hw
    rw [e1, e2]
    field_simp
    ring
  obtain ⟨h1, h2, h3⟩ := hfac z hz1
  have hqz : deriv (deriv (fun w : ℂ => w / (1 - w) ^ 2)) z
      / deriv (fun w : ℂ => w / (1 - w) ^ 2) z = (4 + 2 * z) / (1 - z ^ 2) := hq.self_of_nhds
  have hA : AnalyticAt ℂ (fun w : ℂ => w / (1 - w) ^ 2) z :=
    analyticAt_id.div ((analyticAt_const.sub analyticAt_id).pow 2) (pow_ne_zero 2 h1)
  rw [schwarzian_of_analyticAt hA]
  unfold schwarzianHol
  rw [hq.deriv_eq, (hasDerivAt_koebe_logDeriv h3).deriv, hqz]
  field_simp
  ring

/-- §19.3: equality holds in (19.5) for the Koebe function `k(z) = z/(1 - z)²`. -/
theorem koebe_schwarzianNorm :
    IsUnivMero (fun z => z / (1 - z) ^ 2) unitDisc ∧
      schwarzianNorm (fun z => z / (1 - z) ^ 2) unitDisc = ENNReal.ofReal (3 / 2) := by
  have hfac : ∀ w : ℂ, ‖w‖ < 1 → (1 : ℂ) - w ≠ 0 ∧ (1 : ℂ) + w ≠ 0 := by
    intro w hw
    constructor
    · exact fun hcon => by rw [show w = 1 by linear_combination -hcon] at hw; simp at hw
    · exact fun hcon => by rw [show w = -1 by linear_combination hcon] at hw; simp at hw
  have hA : ∀ z ∈ unitDisc, AnalyticAt ℂ (fun w : ℂ => w / (1 - w) ^ 2) z := by
    intro z hz
    exact analyticAt_id.div ((analyticAt_const.sub analyticAt_id).pow 2)
      (pow_ne_zero 2 (hfac z (mem_ball_zero_iff.mp hz)).1)
  have hderiv : ∀ z ∈ unitDisc, deriv (fun w : ℂ => w / (1 - w) ^ 2) z ≠ 0 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hfac z (mem_ball_zero_iff.mp hz)
    rw [(hasDerivAt_koebe h1).deriv]
    exact div_ne_zero (fun hcon => h2 (by linear_combination hcon)) (pow_ne_zero 3 h1)
  refine ⟨⟨⟨fun z hz => (hA z hz).meromorphicAt, fun z hz => Or.inl ⟨hA z hz, hderiv z hz⟩⟩,
    ?_, fun z₁ h₁ _ _ => absurd (hA z₁ h₁.1) h₁.2⟩, ?_⟩
  · -- univalence: equal values force `(z₁ - z₂)(1 - z₁z₂) = 0`
    rintro z₁ ⟨hz₁, -⟩ z₂ ⟨hz₂, -⟩ heq
    have hn₁ : ‖z₁‖ < 1 := mem_ball_zero_iff.mp hz₁
    have hn₂ : ‖z₂‖ < 1 := mem_ball_zero_iff.mp hz₂
    have hcross : z₁ * (1 - z₂) ^ 2 = z₂ * (1 - z₁) ^ 2 :=
      (div_eq_div_iff (pow_ne_zero 2 (hfac z₁ hn₁).1) (pow_ne_zero 2 (hfac z₂ hn₂).1)).mp heq
    have hprod : (1 : ℂ) - z₁ * z₂ ≠ 0 := by
      intro hcon
      have hnorm : ‖z₁‖ * ‖z₂‖ = 1 := by
        rw [← norm_mul, show z₁ * z₂ = 1 by linear_combination -hcon, norm_one]
      nlinarith [norm_nonneg z₁, norm_nonneg z₂]
    rcases mul_eq_zero.mp (show (z₁ - z₂) * (1 - z₁ * z₂) = 0 by linear_combination hcross) with
      h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hprod
  · -- the norm: the value is `3/2 · ((1 - |z|²)/|1 - z²|)²`, at most `3/2`, with equality at `0`
    have hval : ∀ z ∈ unitDisc, ‖schwarzian (fun w : ℂ => w / (1 - w) ^ 2) z‖
        / poincareDensity unitDisc z ^ 2 = 3 / 2 * ((1 - ‖z‖ ^ 2) / ‖1 - z ^ 2‖) ^ 2 := by
      intro z hz
      have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have h3 : (1 : ℂ) - z ^ 2 ≠ 0 := by
        intro hcon
        rcases mul_eq_zero.mp (show ((1 : ℂ) - z) * (1 + z) = 0 by linear_combination hcon) with
          h | h
        · exact (hfac z hn).1 h
        · exact (hfac z hn).2 h
      have hne : ‖1 - z ^ 2‖ ≠ 0 := by simpa using h3
      have hnz : (1 : ℝ) - ‖z‖ ^ 2 ≠ 0 := ne_of_gt hpos
      rw [schwarzian_koebe hz, poincareDensity_unitDisc hz, poincareDensityDisc]
      rw [show ‖(-6 : ℂ) / (1 - z ^ 2) ^ 2‖ = 6 / ‖1 - z ^ 2‖ ^ 2 by
        rw [norm_div, norm_pow]; norm_num]
      field_simp
      ring
    have hle : ∀ z ∈ unitDisc, ‖schwarzian (fun w : ℂ => w / (1 - w) ^ 2) z‖
        / poincareDensity unitDisc z ^ 2 ≤ 3 / 2 := by
      intro z hz
      have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
      have hpos : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
      have hkey : 1 - ‖z‖ ^ 2 ≤ ‖1 - z ^ 2‖ := by
        have h := norm_sub_norm_le (1 : ℂ) (z ^ 2)
        simpa [norm_pow] using h
      have hratio : (1 - ‖z‖ ^ 2) / ‖1 - z ^ 2‖ ≤ 1 :=
        div_le_one_of_le₀ hkey (le_trans (le_of_lt hpos) hkey)
      have hrnn : 0 ≤ (1 - ‖z‖ ^ 2) / ‖1 - z ^ 2‖ :=
        div_nonneg (le_of_lt hpos) (norm_nonneg _)
      rw [hval z hz]
      nlinarith [hratio, hrnn]
    refine le_antisymm (iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal (hle z hz))
      (le_iSup₂_of_le (0 : ℂ) (by simp [unitDisc]) (le_of_eq (congrArg ENNReal.ofReal ?_)))
    rw [hval 0 (by simp [unitDisc])]
    norm_num

/-- (19.6): the outer radius of univalence (单叶性外径) `σ₂(D) = sup ‖S_f‖_D` over univalent `f`. -/
def outerUnivalenceRadius (D : Set ℂ) : ℝ≥0∞ :=
  ⨆ (f : ℂ → ℂ) (_ : IsUnivMero f D), schwarzianNorm f D

/-- (19.7): `σ₁(D) = ‖S_φ‖_D` for a conformal map `φ : D → Δ`. -/
def sigmaOne (D : Set ℂ) : ℝ≥0∞ :=
  ⨆ (φ : ℂ → ℂ) (_ : IsConformalOnto φ D unitDisc), schwarzianNorm φ D

/-- A conformal map of an open set is locally univalent meromorphic there: it is analytic, and
its derivative cannot vanish (`deriv_ne_zero_of_injOn`). -/
theorem isLocUnivMero_of_isConformalOnto {f : ℂ → ℂ} {D V : Set ℂ} (hD : IsOpen D)
    (hf : IsConformalOnto f D V) : IsLocUnivMero f D := by
  have hA : ∀ z ∈ D, AnalyticAt ℂ f z := fun z hz => hf.1.analyticAt (hD.mem_nhds hz)
  exact ⟨fun z hz => (hA z hz).meromorphicAt,
    fun z hz => Or.inl ⟨hA z hz, deriv_ne_zero_of_injOn hD hf.1 hf.2.1 hz⟩⟩

/-- `σ₁(D)` does not depend on the conformal map `φ : D → Δ`.

Two conformal maps `φ, ψ : D → Δ` satisfy `ψ = (ψ ∘ φ⁻¹) ∘ φ`, where `ψ ∘ φ⁻¹` is a conformal
self-map of `Δ` — `IsConformalOnto.symm` supplies the inverse — hence a Möbius map by
`exists_mobius_of_isConformalOnto_unitDisc`.  Germ invariance of the Schwarzian
(`schwarzian_congr`) transfers that identity from `D` to a punctured neighbourhood of each point,
and `schwarzian_mobius_comp` then gives `S_ψ = S_φ` on `D`.  Both norms divide by the same
`poincareDensity D`, so no §14 density theorem is needed. -/
theorem sigmaOne_eq {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ D unitDisc) : sigmaOne D = schwarzianNorm φ D := by
  have hDo : IsOpen D := hD.1
  have hloc : IsLocUnivMero φ D := isLocUnivMero_of_isConformalOnto hDo hφ
  have key : ∀ ψ : ℂ → ℂ, IsConformalOnto ψ D unitDisc →
      schwarzianNorm ψ D = schwarzianNorm φ D := by
    intro ψ hψ
    have hσ : IsConformalOnto (Function.invFunOn φ D) unitDisc D := hφ.symm hDo
    obtain ⟨A, B, C, E, hdet, hEq⟩ := exists_mobius_of_isConformalOnto_unitDisc (hψ.comp hσ)
    -- on `D` the competitor is a Möbius function of `φ`
    have hpt : ∀ z ∈ D, ψ z = (A * φ z + B) / (C * φ z + E) := by
      intro z hz
      have h1 := hEq (hφ.mapsTo hz)
      rw [Function.comp_apply, hφ.2.1.leftInvOn_invFunOn hz] at h1
      exact h1
    have hS : ∀ z ∈ D, schwarzian ψ z = schwarzian φ z := by
      intro z hz
      have hgerm : ψ =ᶠ[𝓝[≠] z] fun w => (A * φ w + B) / (C * φ w + E) := by
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [hDo.mem_nhds hz] with w hw
        exact hpt w hw
      rw [schwarzian_congr hgerm, schwarzian_mobius_comp hloc hdet hz]
    unfold schwarzianNorm
    exact iSup_congr fun z => iSup_congr fun hz => by rw [hS z hz]
  exact le_antisymm (iSup₂_le fun ψ hψ => le_of_eq (key ψ hψ)) (le_iSup₂_of_le φ hφ le_rfl)

/-! ### Lehto's theorem `σ₂(D) = 3/2 + σ₁(D)` (`lehto_`)

`σ₂(D)` is the supremum of `‖S_f‖_D` over the univalent meromorphic `f` in `D`, and
`σ₁(D) = ‖S_φ‖_D` for any conformal `φ : D → Δ` (`sigmaOne_eq`).  Both directions rest on the
chain rule `S_f = (S_{f∘φ⁻¹} ∘ φ) φ'² + S_φ` and on `η_D = 2|φ'|/(1 - |φ|²)`.  For `≤`, `f` is
first replaced (as in Theorem 19.2) by a univalent holomorphic function with the same Schwarzian,
so that `f ∘ φ⁻¹` is univalent holomorphic in `Δ` and Theorem 19.2 applies to it.  For `≥`, the
Koebe function composed with a disc automorphism and a rotation aligned with `S_φ(z₀)` realises
`3/2 + |S_φ(z₀)|/η_D(z₀)²` at any given `z₀ ∈ D`. -/

/-- The Riemann mapping theorem for a hyperbolic simply connected domain. -/
theorem lehto_exists_conformal {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ D unitDisc := by
  obtain ⟨hDo, hDc, hDs, hDne⟩ := hD
  haveI : SimplyConnectedSpace ↥D := hDs
  obtain ⟨z₀, hz₀⟩ := hDc.nonempty
  obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hDo hDc
    (Set.nonempty_compl.2 hDne) (RMT.hasHolomorphicSqrt_of_simplyConnected hDo hDc) hz₀
  exact ⟨f, hf.diff, hf.injOn, hfb.image_eq⟩

/-- An injective holomorphic map of an open subset of a domain conformally equivalent to `Δ`
omits a value (Liouville, applied to the conformal map composed with the inverse). -/
theorem lehto_exists_omitted {f φ : ℂ → ℂ} {U D : Set ℂ} (hU : IsOpen U) (hUD : U ⊆ D)
    (hDo : IsOpen D) (hφ : IsConformalOnto φ D unitDisc) (hd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) : ∃ w₀ : ℂ, ∀ w ∈ U, f w ≠ w₀ := by
  by_contra hcon
  simp only [not_exists, not_forall, not_not, exists_prop] at hcon
  have himg : f '' U = univ := Set.eq_univ_of_forall fun v => hcon v
  have hconf : IsConformalOnto f U univ := ⟨hd, hinj, himg⟩
  obtain ⟨hψd, -, hψimg⟩ := hconf.symm hU
  have hψ : Differentiable ℂ (Function.invFunOn f U) := differentiableOn_univ.1 hψd
  have hψmem : ∀ v, Function.invFunOn f U v ∈ U := fun v => by
    have : Function.invFunOn f U v ∈ Function.invFunOn f U '' univ := ⟨v, mem_univ _, rfl⟩
    rwa [hψimg] at this
  have hcomp : Differentiable ℂ (φ ∘ Function.invFunOn f U) := fun v =>
    (hφ.1.differentiableAt (hDo.mem_nhds (hUD (hψmem v)))).comp v (hψ v)
  have hb : Bornology.IsBounded (Set.range (φ ∘ Function.invFunOn f U)) := by
    refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1)).subset ?_
    rintro _ ⟨v, rfl⟩
    exact hφ.mapsTo (hUD (hψmem v))
  have h01 := hcomp.apply_eq_apply_of_bounded hb 0 1
  have h01' : Function.invFunOn f U 0 = Function.invFunOn f U 1 :=
    hφ.2.1 (hUD (hψmem 0)) (hUD (hψmem 1)) h01
  have e0 : f (Function.invFunOn f U 0) = 0 := Function.invFunOn_eq (hcon 0)
  have e1 : f (Function.invFunOn f U 1) = 1 := Function.invFunOn_eq (hcon 1)
  rw [h01'] at e0
  exact zero_ne_one (e0.symm.trans e1)

/-- A univalent meromorphic `f` in `D` is, up to a Möbius transformation, a univalent holomorphic
function with the same Schwarzian (the argument of `knr_exists_holomorphic`, in `D`). -/
theorem lehto_exists_holomorphic {f φ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hφ : IsConformalOnto φ D unitDisc) (hf : IsUnivMero f D) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F D ∧ InjOn F D ∧
      ∀ w ∈ D, schwarzian F w = schwarzian f w := by
  obtain ⟨hloc, hinj, hpole⟩ := hf
  by_cases hall : ∀ w ∈ D, AnalyticAt ℂ f w
  · refine ⟨f, fun w hw => (hall w hw).differentiableAt.differentiableWithinAt, ?_, fun _ _ => rfl⟩
    intro w₁ hw₁ w₂ hw₂ he
    exact hinj ⟨hw₁, hall w₁ hw₁⟩ ⟨hw₂, hall w₂ hw₂⟩ he
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨z₀, hz₀, hA₀⟩ := hall
    have hana : ∀ w ∈ D, w ≠ z₀ → AnalyticAt ℂ f w := fun w hw hne => by
      by_contra hA
      exact hne (hpole ⟨hw, hA⟩ ⟨hz₀, hA₀⟩)
    obtain ⟨u, hu, hu', -, hchart⟩ := exists_chart_of_isLocUnivMero hloc hz₀
    have hord : meromorphicOrderAt f z₀ < 0 := by
      rcases hloc.2 z₀ hz₀ with ⟨hA, -⟩ | ⟨h, -, -⟩
      · exact absurd hA hA₀
      · exact h
    have hfu : f =ᶠ[𝓝[≠] z₀] fun y => (u y)⁻¹ := by
      rcases hchart with h | h
      · exfalso
        rw [meromorphicOrderAt_congr h] at hord
        exact absurd hord (not_lt.2 hu.meromorphicOrderAt_nonneg)
      · exact h
    have hu0 : u z₀ = 0 := by
      by_contra hne
      rw [meromorphicOrderAt_congr hfu] at hord
      exact absurd hord (not_lt.2 (hu.inv hne).meromorphicOrderAt_nonneg)
    have hune : ∀ᶠ y in 𝓝[≠] z₀, u y ≠ 0 := by
      refine hu.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hcon => hu' ?_
      have hz0 : u =ᶠ[𝓝 z₀] fun _ => (0 : ℂ) := hcon
      rw [hz0.deriv_eq, deriv_const]
    have hUo : IsOpen (D \ {z₀}) := hDo.sdiff isClosed_singleton
    obtain ⟨w₀, hw₀⟩ := lehto_exists_omitted hUo Set.diff_subset hDo hφ
      (fun w hw => (hana w hw.1 hw.2).differentiableAt.differentiableWithinAt)
      (fun w₁ hw₁ w₂ hw₂ he => hinj ⟨hw₁.1, hana _ hw₁.1 hw₁.2⟩ ⟨hw₂.1, hana _ hw₂.1 hw₂.2⟩ he)
    have hne_w₀ : ∀ w ∈ D, w ≠ z₀ → f w - w₀ ≠ 0 := fun w hw hne =>
      sub_ne_zero.2 (hw₀ w ⟨hw, hne⟩)
    have hFeq : ∀ w, w ≠ z₀ → Function.update (fun y => (f y - w₀)⁻¹) z₀ 0 w = (f w - w₀)⁻¹ :=
      fun w hw => Function.update_of_ne hw _ _
    have hFz₀ : Function.update (fun y => (f y - w₀)⁻¹) z₀ 0 z₀ = 0 := Function.update_self _ _ _
    have hgerm : ∀ w ∈ D, Function.update (fun y => (f y - w₀)⁻¹) z₀ 0 =ᶠ[𝓝[≠] w]
        fun y => (0 * f y + 1) / (1 * f y + -w₀) := by
      intro w _
      have hev : ∀ᶠ y in 𝓝[≠] w, y ≠ z₀ := by
        rcases eq_or_ne w z₀ with rfl | hne
        · exact self_mem_nhdsWithin
        · exact (eventually_ne_nhds hne).filter_mono nhdsWithin_le_nhds
      filter_upwards [hev] with y hy
      rw [hFeq y hy]
      simp only [zero_mul, zero_add, one_mul, one_div, sub_eq_add_neg]
    have hS : ∀ w ∈ D, schwarzian (Function.update (fun y => (f y - w₀)⁻¹) z₀ 0) w =
        schwarzian f w := fun w hw => by
      rw [schwarzian_congr (hgerm w hw),
        schwarzian_mobius_comp hloc (by norm_num : (0 : ℂ) * -w₀ - 1 * 1 ≠ 0) hw]
    have hFan : ∀ w ∈ D, AnalyticAt ℂ (Function.update (fun y => (f y - w₀)⁻¹) z₀ 0) w := by
      intro w hw
      rcases eq_or_ne w z₀ with rfl | hne
      · have hG : AnalyticAt ℂ (fun y => u y / (1 - w₀ * u y)) w :=
          hu.div (analyticAt_const.sub (analyticAt_const.mul hu)) (by rw [hu0]; simp)
        refine hG.congr ?_
        have h1' : ∀ᶠ y in 𝓝[≠] w,
            u y / (1 - w₀ * u y) = Function.update (fun y => (f y - w₀)⁻¹) w 0 y := by
          filter_upwards [hfu, hune, self_mem_nhdsWithin] with y hy hy0 hyw
          rw [hFeq y hyw, hy]
          field_simp
        have h1 := eventually_nhdsWithin_iff.1 h1'
        filter_upwards [h1] with y hy
        by_cases hyw : y = w
        · subst hyw
          simp [hu0]
        · exact hy hyw
      · have hA := hana w hw hne
        refine ((hA.sub analyticAt_const).inv (hne_w₀ w hw hne)).congr ?_
        filter_upwards [eventually_ne_nhds hne] with y hy
        exact (hFeq y hy).symm
    have hFinj : InjOn (Function.update (fun y => (f y - w₀)⁻¹) z₀ 0) D := by
      intro w₁ hw₁ w₂ hw₂ he
      rcases eq_or_ne w₁ z₀ with h1 | h1 <;> rcases eq_or_ne w₂ z₀ with h2 | h2
      · rw [h1, h2]
      · rw [h1, hFz₀, hFeq w₂ h2, eq_comm, inv_eq_zero] at he
        exact absurd he (hne_w₀ w₂ hw₂ h2)
      · rw [h2, hFz₀, hFeq w₁ h1, inv_eq_zero] at he
        exact absurd he (hne_w₀ w₁ hw₁ h1)
      · rw [hFeq w₁ h1, hFeq w₂ h2, inv_inj, sub_left_inj] at he
        exact hinj ⟨hw₁, hana _ hw₁ h1⟩ ⟨hw₂, hana _ hw₂ h2⟩ he
    exact ⟨_, fun w hw => (hFan w hw).differentiableAt.differentiableWithinAt, hFinj, hS⟩

theorem lehto_norm_lt_one {φ : ℂ → ℂ} {D : Set ℂ} (hφ : IsConformalOnto φ D unitDisc) {z : ℂ}
    (hz : z ∈ D) : ‖φ z‖ < 1 :=
  mem_ball_zero_iff.1 (hφ.mapsTo hz)

/-- `X / η_D(z)²` in terms of a conformal map `φ : D → Δ`. -/
theorem lehto_div_density_sq {φ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hφ : IsConformalOnto φ D unitDisc) {z : ℂ} (hz : z ∈ D) (X : ℝ) :
    X / poincareDensity D z ^ 2 = X * (1 - ‖φ z‖ ^ 2) ^ 2 / (4 * ‖deriv φ z‖ ^ 2) := by
  have hB : ‖deriv φ z‖ ≠ 0 := norm_ne_zero_iff.2 (deriv_ne_zero_of_injOn hDo hφ.1 hφ.2.1 hz)
  have hd : 0 < 1 - ‖φ z‖ ^ 2 := by nlinarith [lehto_norm_lt_one hφ hz, norm_nonneg (φ z)]
  rw [(poincareDensity_well_defined hDo hφ hφ hz).2]
  field_simp
  ring

/-- The chain rule `S_{g∘φ} = (S_g∘φ) φ'² + S_φ` at a point of `D`, for `g` analytic on `Δ`. -/
theorem lehto_chain {g φ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hφ : IsConformalOnto φ D unitDisc) (hg : ∀ w ∈ unitDisc, AnalyticAt ℂ g w)
    (hg' : ∀ w ∈ unitDisc, deriv g w ≠ 0) {z : ℂ} (hz : z ∈ D) :
    schwarzian (g ∘ φ) z = schwarzian g (φ z) * deriv φ z ^ 2 + schwarzian φ z :=
  eq19_1_chain_rule (hφ.1.analyticAt (hDo.mem_nhds hz)) (deriv_ne_zero_of_injOn hDo hφ.1 hφ.2.1 hz)
    (hg _ (hφ.mapsTo hz)) (hg' _ (hφ.mapsTo hz))

/-- A holomorphic injective map of `Δ` is univalent meromorphic (no poles). -/
theorem lehto_isUnivMero_of_isConformalOnto {g : ℂ → ℂ} {V : Set ℂ}
    (hg : IsConformalOnto g unitDisc V) : IsUnivMero g unitDisc :=
  ⟨isLocUnivMero_of_isConformalOnto isOpen_ball hg, fun _ hw₁ _ hw₂ he => hg.2.1 hw₁.1 hw₂.1 he,
    fun _ hw₁ => absurd (hg.1.analyticAt (isOpen_ball.mem_nhds hw₁.1)) hw₁.2⟩

/-- The pointwise bound for `≤`: for univalent holomorphic `F` in `D`,
`|S_F(z)|/η_D(z)² ≤ 3/2 + |S_φ(z)|/η_D(z)²`. -/
theorem lehto_le_pointwise {F φ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hφ : IsConformalOnto φ D unitDisc) (hF : DifferentiableOn ℂ F D) (hFinj : InjOn F D)
    {z : ℂ} (hz : z ∈ D) :
    ‖schwarzian F z‖ / poincareDensity D z ^ 2 ≤
      3 / 2 + ‖schwarzian φ z‖ / poincareDensity D z ^ 2 := by
  have hψ : IsConformalOnto (Function.invFunOn φ D) unitDisc D := hφ.symm hDo
  have hFc : IsConformalOnto F D (F '' D) := ⟨hF, hFinj, rfl⟩
  have hg : IsConformalOnto (F ∘ Function.invFunOn φ D) unitDisc (F '' D) := hFc.comp hψ
  have hgan : ∀ w ∈ unitDisc, AnalyticAt ℂ (F ∘ Function.invFunOn φ D) w := fun w hw =>
    hg.1.analyticAt (isOpen_ball.mem_nhds hw)
  have hg' : ∀ w ∈ unitDisc, deriv (F ∘ Function.invFunOn φ D) w ≠ 0 := fun w hw =>
    deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.1 hw
  -- `F = g ∘ φ` near `z`, and the chain rule
  have hFg : schwarzian F z = schwarzian ((F ∘ Function.invFunOn φ D) ∘ φ) z := by
    refine schwarzian_congr ?_
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [hDo.mem_nhds hz] with y hy
    simp only [Function.comp_apply, hφ.2.1.leftInvOn_invFunOn hy]
  rw [hFg, lehto_chain hDo hφ hgan hg' hz]
  have h6 := thm19_2_nehari (lehto_isUnivMero_of_isConformalOnto hg) (hφ.mapsTo hz)
  have hB : 0 < ‖deriv φ z‖ := norm_pos_iff.2 (deriv_ne_zero_of_injOn hDo hφ.1 hφ.2.1 hz)
  have hd : 0 < 1 - ‖φ z‖ ^ 2 := by nlinarith [lehto_norm_lt_one hφ hz, norm_nonneg (φ z)]
  rw [lehto_div_density_sq hDo hφ hz, lehto_div_density_sq hDo hφ hz]
  have htri : ‖schwarzian (F ∘ Function.invFunOn φ D) (φ z) * deriv φ z ^ 2 + schwarzian φ z‖ ≤
      ‖schwarzian (F ∘ Function.invFunOn φ D) (φ z)‖ * ‖deriv φ z‖ ^ 2 + ‖schwarzian φ z‖ := by
    calc _ ≤ ‖schwarzian (F ∘ Function.invFunOn φ D) (φ z) * deriv φ z ^ 2‖ +
          ‖schwarzian φ z‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, norm_pow]
  have hAd : ‖schwarzian (F ∘ Function.invFunOn φ D) (φ z)‖ * (1 - ‖φ z‖ ^ 2) ^ 2 / 4 ≤ 3 / 2 := by
    linarith
  calc ‖schwarzian (F ∘ Function.invFunOn φ D) (φ z) * deriv φ z ^ 2 + schwarzian φ z‖ *
        (1 - ‖φ z‖ ^ 2) ^ 2 / (4 * ‖deriv φ z‖ ^ 2)
      ≤ (‖schwarzian (F ∘ Function.invFunOn φ D) (φ z)‖ * ‖deriv φ z‖ ^ 2 + ‖schwarzian φ z‖) *
        (1 - ‖φ z‖ ^ 2) ^ 2 / (4 * ‖deriv φ z‖ ^ 2) := by gcongr
    _ = ‖schwarzian (F ∘ Function.invFunOn φ D) (φ z)‖ * (1 - ‖φ z‖ ^ 2) ^ 2 / 4 +
        ‖schwarzian φ z‖ * (1 - ‖φ z‖ ^ 2) ^ 2 / (4 * ‖deriv φ z‖ ^ 2) := by
        field_simp
    _ ≤ 3 / 2 + ‖schwarzian φ z‖ * (1 - ‖φ z‖ ^ 2) ^ 2 / (4 * ‖deriv φ z‖ ^ 2) := by linarith

/-- The Koebe function is analytic in `Δ`. -/
theorem lehto_koebe_analyticAt {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ (fun w : ℂ => w / (1 - w) ^ 2) w := by
  have h1 : (1 : ℂ) - w ≠ 0 := fun hcon => by
    rw [show w = 1 by linear_combination -hcon] at hw
    simp at hw
  exact analyticAt_id.div ((analyticAt_const.sub analyticAt_id).pow 2) (pow_ne_zero 2 h1)

/-- A unit complex number with a prescribed square. -/
theorem lehto_exists_sqrt {v : ℂ} (hv : ‖v‖ = 1) : ∃ c : ℂ, ‖c‖ = 1 ∧ c ^ 2 = v := by
  have hv0 : v ≠ 0 := by
    rw [← norm_pos_iff, hv]
    exact one_pos
  refine ⟨Complex.exp (Complex.log v / 2), ?_, ?_⟩
  · rw [Complex.norm_exp, Complex.div_ofNat_re, Complex.log_re, hv, Real.log_one, zero_div,
      Real.exp_zero]
  · rw [← Complex.exp_nat_mul]
    push_cast
    rw [show (2 : ℂ) * (Complex.log v / 2) = Complex.log v by ring, Complex.exp_log hv0]

/-- The pointwise construction for `≥`: at `z₀ ∈ D`, the Koebe function composed with a disc
automorphism and a rotation gives a univalent `f` with
`|S_f(z₀)|/η_D(z₀)² = 3/2 + |S_φ(z₀)|/η_D(z₀)²`. -/
theorem lehto_ge_pointwise {φ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hφ : IsConformalOnto φ D unitDisc) {z₀ : ℂ} (hz₀ : z₀ ∈ D) :
    ∃ f : ℂ → ℂ, IsUnivMero f D ∧ ‖schwarzian f z₀‖ / poincareDensity D z₀ ^ 2 =
      3 / 2 + ‖schwarzian φ z₀‖ / poincareDensity D z₀ ^ 2 := by
  have hw₀ : ‖φ z₀‖ < 1 := lehto_norm_lt_one hφ hz₀
  have hφ' : deriv φ z₀ ≠ 0 := deriv_ne_zero_of_injOn hDo hφ.1 hφ.2.1 hz₀
  have hB : 0 < ‖deriv φ z₀‖ := norm_pos_iff.2 hφ'
  have hd : 0 < 1 - ‖φ z₀‖ ^ 2 := by nlinarith [norm_nonneg (φ z₀)]
  have hdc : ((1 - ‖φ z₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.ne'
  -- the direction `u` of `S_φ(z₀)`
  obtain ⟨u, hu1, hu⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ (‖schwarzian φ z₀‖ : ℂ) * u = schwarzian φ z₀ := by
    by_cases hS : schwarzian φ z₀ = 0
    · exact ⟨1, norm_one, by rw [hS, norm_zero]; simp⟩
    · have hS' : (‖schwarzian φ z₀‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hS)
      refine ⟨schwarzian φ z₀ / ‖schwarzian φ z₀‖, ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          div_self (norm_ne_zero_iff.2 hS)]
      · field_simp
  -- the rotation `c`, `c² = -u conj(φ'(z₀))/φ'(z₀)`
  obtain ⟨c, hc1, hc2⟩ := lehto_exists_sqrt (v := -u * conj (deriv φ z₀) / deriv φ z₀) (by
    rw [norm_div, norm_mul, norm_neg, hu1, Complex.norm_conj, one_mul, div_self hB.ne'])
  have hc0 : c ≠ 0 := by
    rw [← norm_pos_iff, hc1]
    exact one_pos
  -- the disc automorphism `m = c · blaschke (φ z₀)`
  have hmmaps : ∀ w ∈ unitDisc, c * blaschke (φ z₀) w ∈ unitDisc := fun w hw => by
    rw [unitDisc, mem_ball_zero_iff, norm_mul, hc1, one_mul]
    exact blaschke_mem_unitDisc hw₀ (mem_ball_zero_iff.1 hw)
  have hman : ∀ w ∈ unitDisc, AnalyticAt ℂ (fun w => c * blaschke (φ z₀) w) w := fun w hw =>
    analyticAt_const.mul ((differentiableOn_blaschke hw₀).analyticAt (isOpen_ball.mem_nhds hw))
  have hminj : InjOn (fun w => c * blaschke (φ z₀) w) unitDisc := by
    intro w₁ hw₁ w₂ hw₂ he
    have he' : blaschke (φ z₀) w₁ = blaschke (φ z₀) w₂ := mul_left_cancel₀ hc0 he
    have := congrArg (blaschke (-φ z₀)) he'
    rwa [blaschke_neg_blaschke hw₀ (mem_ball_zero_iff.1 hw₁),
      blaschke_neg_blaschke hw₀ (mem_ball_zero_iff.1 hw₂)] at this
  have hm0 : c * blaschke (φ z₀) (φ z₀) = 0 := by simp [blaschke]
  have hm' : deriv (fun w => c * blaschke (φ z₀) w) (φ z₀) = c / ((1 - ‖φ z₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [((hasDerivAt_blaschke hw₀ hw₀).const_mul c).deriv, Complex.mul_conj', Complex.conj_mul']
    push_cast
    field_simp
  have hmmob : (fun w => c * blaschke (φ z₀) w) =
      fun w => (c * w + -(c * φ z₀)) / (-conj (φ z₀) * w + 1) := by
    funext w
    simp only [blaschke]
    ring
  have hmS : schwarzian (fun w => c * blaschke (φ z₀) w) (φ z₀) = 0 := by
    rw [hmmob]
    refine schwarzian_mobius ?_ _
    have e : c * 1 - -(c * φ z₀) * -conj (φ z₀) = c * ((1 - ‖φ z₀‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.mul_conj']
      ring
    rw [e]
    exact mul_ne_zero hc0 hdc
  -- `g = k ∘ m`, `f = g ∘ φ`
  have hkoebe := koebe_schwarzianNorm.1
  have hgan : ∀ w ∈ unitDisc, AnalyticAt ℂ (fun w => (c * blaschke (φ z₀) w) /
      (1 - c * blaschke (φ z₀) w) ^ 2) w := fun w hw =>
    AnalyticAt.comp (g := fun w : ℂ => w / (1 - w) ^ 2) (f := fun w => c * blaschke (φ z₀) w)
      (lehto_koebe_analyticAt (mem_ball_zero_iff.1 (hmmaps w hw))) (hman w hw)
  have hginj : InjOn (fun w => (c * blaschke (φ z₀) w) / (1 - c * blaschke (φ z₀) w) ^ 2)
      unitDisc := by
    intro w₁ hw₁ w₂ hw₂ he
    refine hminj hw₁ hw₂ (hkoebe.2.1 ⟨hmmaps w₁ hw₁, ?_⟩ ⟨hmmaps w₂ hw₂, ?_⟩ he)
    · exact lehto_koebe_analyticAt (mem_ball_zero_iff.1 (hmmaps w₁ hw₁))
    · exact lehto_koebe_analyticAt (mem_ball_zero_iff.1 (hmmaps w₂ hw₂))
  have hgc : IsConformalOnto (fun w => (c * blaschke (φ z₀) w) / (1 - c * blaschke (φ z₀) w) ^ 2)
      unitDisc ((fun w => (c * blaschke (φ z₀) w) / (1 - c * blaschke (φ z₀) w) ^ 2) '' unitDisc) :=
    ⟨fun w hw => (hgan w hw).differentiableAt.differentiableWithinAt, hginj, rfl⟩
  have hg' : ∀ w ∈ unitDisc, deriv (fun w => (c * blaschke (φ z₀) w) /
      (1 - c * blaschke (φ z₀) w) ^ 2) w ≠ 0 := fun w hw =>
    deriv_ne_zero_of_injOn isOpen_ball hgc.1 hgc.2.1 hw
  have hfc : IsConformalOnto ((fun w => (c * blaschke (φ z₀) w) /
      (1 - c * blaschke (φ z₀) w) ^ 2) ∘ φ) D ((fun w => (c * blaschke (φ z₀) w) /
      (1 - c * blaschke (φ z₀) w) ^ 2) '' unitDisc) := hgc.comp hφ
  refine ⟨_, ⟨isLocUnivMero_of_isConformalOnto hDo hfc,
    fun w₁ hw₁ w₂ hw₂ he => hfc.2.1 hw₁.1 hw₂.1 he,
    fun w₁ hw₁ => absurd (hfc.1.analyticAt (hDo.mem_nhds hw₁.1)) hw₁.2⟩, ?_⟩
  -- the Schwarzian of `f` at `z₀`
  rw [lehto_chain hDo hφ hgan hg' hz₀]
  have hgS : schwarzian (fun w => (c * blaschke (φ z₀) w) / (1 - c * blaschke (φ z₀) w) ^ 2)
      (φ z₀) = -6 * (c / ((1 - ‖φ z₀‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
    have hk0 : AnalyticAt ℂ (fun w : ℂ => w / (1 - w) ^ 2) (c * blaschke (φ z₀) (φ z₀)) := by
      rw [hm0]
      exact lehto_koebe_analyticAt (by simp)
    have hk0' : deriv (fun w : ℂ => w / (1 - w) ^ 2) (c * blaschke (φ z₀) (φ z₀)) ≠ 0 := by
      rw [hm0, (hasDerivAt_koebe (by simp)).deriv]
      norm_num
    have hm'0 : deriv (fun w => c * blaschke (φ z₀) w) (φ z₀) ≠ 0 := by
      rw [hm']
      exact div_ne_zero hc0 hdc
    have := eq19_1_chain_rule (hman _ (hφ.mapsTo hz₀)) hm'0 hk0 hk0'
    rw [Function.comp_def] at this
    rw [this, hm0, schwarzian_koebe (mem_ball_self one_pos), hmS, hm']
    norm_num
  rw [hgS]
  -- `-6 c² φ'² /(1-|w₀|²)² = 6 u |φ'|²/(1-|w₀|²)²`
  have hkey : -6 * (c / ((1 - ‖φ z₀‖ ^ 2 : ℝ) : ℂ)) ^ 2 * deriv φ z₀ ^ 2 + schwarzian φ z₀ =
      u * ((6 * ‖deriv φ z₀‖ ^ 2 / (1 - ‖φ z₀‖ ^ 2) ^ 2 + ‖schwarzian φ z₀‖ : ℝ) : ℂ) := by
    have hc2' : c ^ 2 * deriv φ z₀ = -u * conj (deriv φ z₀) := by
      rw [hc2]
      field_simp
    have e : conj (deriv φ z₀) * deriv φ z₀ = (‖deriv φ z₀‖ : ℂ) ^ 2 := Complex.conj_mul' _
    rw [div_pow]
    push_cast
    linear_combination (-6 * deriv φ z₀ / (1 - (‖φ z₀‖ : ℂ) ^ 2) ^ 2) * hc2' +
      (6 * u / (1 - (‖φ z₀‖ : ℂ) ^ 2) ^ 2) * e - hu
  rw [hkey, norm_mul, hu1, one_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    lehto_div_density_sq hDo hφ hz₀, lehto_div_density_sq hDo hφ hz₀]
  field_simp
  ring

/-- The pointwise bound `|S_φ(z)|/η_D(z)² ≤ 3/2` for a conformal `φ : D → Δ`, from Theorem 19.2
applied to `φ⁻¹` and the chain rule for `φ⁻¹ ∘ φ = id`. -/
theorem lehto_sigmaOne_pointwise {φ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (hφ : IsConformalOnto φ D unitDisc) {z : ℂ} (hz : z ∈ D) :
    ‖schwarzian φ z‖ / poincareDensity D z ^ 2 ≤ 3 / 2 := by
  have hψ : IsConformalOnto (Function.invFunOn φ D) unitDisc D := hφ.symm hDo
  have hψan : ∀ w ∈ unitDisc, AnalyticAt ℂ (Function.invFunOn φ D) w := fun w hw =>
    hψ.1.analyticAt (isOpen_ball.mem_nhds hw)
  have hψ' : ∀ w ∈ unitDisc, deriv (Function.invFunOn φ D) w ≠ 0 := fun w hw =>
    deriv_ne_zero_of_injOn isOpen_ball hψ.1 hψ.2.1 hw
  have h6 := thm19_2_nehari (lehto_isUnivMero_of_isConformalOnto hψ) (hφ.mapsTo hz)
  have hchain := lehto_chain hDo hφ hψan hψ' hz
  have hid : schwarzian (Function.invFunOn φ D ∘ φ) z = 0 := by
    have hev : (Function.invFunOn φ D ∘ φ) =ᶠ[𝓝[≠] z] fun w => (1 * w + 0) / (0 * w + 1) := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hDo.mem_nhds hz] with y hy
      simp [hφ.2.1.leftInvOn_invFunOn hy]
    rw [schwarzian_congr hev, schwarzian_mobius (by norm_num : (1 : ℂ) * 1 - 0 * 0 ≠ 0) z]
  rw [hid] at hchain
  have hSφ : schwarzian φ z = -(schwarzian (Function.invFunOn φ D) (φ z) * deriv φ z ^ 2) := by
    linear_combination -hchain
  have hnorm : ‖schwarzian φ z‖ =
      ‖schwarzian (Function.invFunOn φ D) (φ z)‖ * ‖deriv φ z‖ ^ 2 := by
    rw [hSφ, norm_neg, norm_mul, norm_pow]
  have hB : 0 < ‖deriv φ z‖ := norm_pos_iff.2 (deriv_ne_zero_of_injOn hDo hφ.1 hφ.2.1 hz)
  have hd : 0 < 1 - ‖φ z‖ ^ 2 := by nlinarith [lehto_norm_lt_one hφ hz, norm_nonneg (φ z)]
  rw [lehto_div_density_sq hDo hφ hz, hnorm]
  have e : ‖schwarzian (Function.invFunOn φ D) (φ z)‖ * ‖deriv φ z‖ ^ 2 * (1 - ‖φ z‖ ^ 2) ^ 2 /
      (4 * ‖deriv φ z‖ ^ 2) =
      ‖schwarzian (Function.invFunOn φ D) (φ z)‖ * (1 - ‖φ z‖ ^ 2) ^ 2 / 4 := by
    field_simp
  rw [e]
  linarith

/-- **Theorem 19.3** (Lehto): `σ₂(D) = 3/2 + σ₁(D)`.

With a conformal map `φ : D → Δ` (`lehto_exists_conformal`, the Riemann mapping theorem),
`σ₁(D) = ‖S_φ‖_D` and `η_D = 2|φ'|/(1 - |φ|²)`.  For `≤`, a univalent meromorphic `f` is first
replaced by a univalent holomorphic `F` with the same Schwarzian (a Möbius transformation, as in
Theorem 19.2), and the chain rule `S_F = (S_{F∘φ⁻¹}∘φ) φ'² + S_φ` with Theorem 19.2 for `F ∘ φ⁻¹`
gives `|S_F|/η_D² ≤ 3/2 + |S_φ|/η_D²`.  For `≥`, at each `z₀ ∈ D` the Koebe function composed
with the disc automorphism sending `φ(z₀)` to `0` and a rotation aligned with `S_φ(z₀)` is
univalent with `|S_f(z₀)|/η_D(z₀)² = 3/2 + |S_φ(z₀)|/η_D(z₀)²`. -/
theorem thm19_3 {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) :
    outerUnivalenceRadius D = ENNReal.ofReal (3 / 2) + sigmaOne D := by
  obtain ⟨φ, hφ⟩ := lehto_exists_conformal hD
  have hDo : IsOpen D := hD.1
  have hDne : D.Nonempty := hD.2.1.nonempty
  rw [sigmaOne_eq hD hφ]
  apply le_antisymm
  · -- `≤`: every univalent `f` is bounded by `3/2 + ‖S_φ‖_D`
    unfold outerUnivalenceRadius
    refine iSup₂_le fun f hf => ?_
    obtain ⟨F, hF, hFinj, hS⟩ := lehto_exists_holomorphic hDo hφ hf
    rw [schwarzianNorm]
    refine iSup₂_le fun z hz => ?_
    rw [← hS z hz]
    calc ENNReal.ofReal (‖schwarzian F z‖ / poincareDensity D z ^ 2)
        ≤ ENNReal.ofReal (3 / 2 + ‖schwarzian φ z‖ / poincareDensity D z ^ 2) :=
          ENNReal.ofReal_le_ofReal (lehto_le_pointwise hDo hφ hF hFinj hz)
      _ = ENNReal.ofReal (3 / 2) +
          ENNReal.ofReal (‖schwarzian φ z‖ / poincareDensity D z ^ 2) :=
          ENNReal.ofReal_add (by norm_num) (by positivity)
      _ ≤ ENNReal.ofReal (3 / 2) + schwarzianNorm φ D := by
          gcongr
          unfold schwarzianNorm
          exact le_iSup₂ (f := fun z (_ : z ∈ D) =>
            ENNReal.ofReal (‖schwarzian φ z‖ / poincareDensity D z ^ 2)) z hz
  · -- `≥`: the extremal functions at each point
    rw [schwarzianNorm, ENNReal.add_biSup hDne]
    refine iSup₂_le fun z hz => ?_
    obtain ⟨f, hf, heq⟩ := lehto_ge_pointwise hDo hφ hz
    unfold outerUnivalenceRadius
    refine le_iSup₂_of_le (f := fun f (_ : IsUnivMero f D) => schwarzianNorm f D) f hf ?_
    unfold schwarzianNorm
    refine le_iSup₂_of_le (f := fun z (_ : z ∈ D) =>
      ENNReal.ofReal (‖schwarzian f z‖ / poincareDensity D z ^ 2)) z hz ?_
    rw [heq, ENNReal.ofReal_add (by norm_num) (by positivity)]

/-- **Theorem 19.3, Corollary**: `σ₂(D) ≤ 3`.

By Theorem 19.3 this is `σ₁(D) ≤ 3/2`: the chain rule for `φ⁻¹ ∘ φ = id` gives
`S_φ = -(S_{φ⁻¹}∘φ) φ'²`, and Theorem 19.2 for the univalent `φ⁻¹ : Δ → D` bounds
`|S_φ(z)|/η_D(z)² = |S_{φ⁻¹}(φ z)| (1 - |φ z|²)²/4` by `6/4`. -/
theorem thm19_3_cor {D : Set ℂ} (hD : IsHyperbolicSimplyConnected D) :
    outerUnivalenceRadius D ≤ 3 := by
  obtain ⟨φ, hφ⟩ := lehto_exists_conformal hD
  rw [thm19_3 hD, sigmaOne_eq hD hφ]
  have h1 : schwarzianNorm φ D ≤ ENNReal.ofReal (3 / 2) := by
    unfold schwarzianNorm
    exact iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal (lehto_sigmaOne_pointwise hD.1 hφ hz)
  calc ENNReal.ofReal (3 / 2) + schwarzianNorm φ D
      ≤ ENNReal.ofReal (3 / 2) + ENNReal.ofReal (3 / 2) := by gcongr
    _ = 3 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
          show (3 / 2 : ℝ) + 3 / 2 = 3 by norm_num, ENNReal.ofReal_ofNat]

end LiZhongQC
