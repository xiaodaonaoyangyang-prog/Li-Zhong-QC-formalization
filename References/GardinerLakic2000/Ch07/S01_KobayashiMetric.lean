import References.GardinerLakic2000.Ch06.S07_HamiltonKrushkal

/-!
# Gardiner–Lakic 2000, Ch. 7 §7.1 Kobayashi's metric

Chapter 7 *Kobayashi's metric on Teichmüller space*, §7.1 (and the chapter introduction, l. 6132–6143, no items);
source `teichmuller.txt`, lines 6145–6224.

* Definition (Poincaré's metric `σ_Δ` of curvature −4, (7.1), l. 6146–6154) — exists: `LiZhongQC.discPoincareDist`
  (½ log((1 + r)/(1 − r)) = tanh⁻¹ r, r = |(z − w)/(1 − w̄z)|) [CORRECTION, see below]
* Definition 1 (Kobayashi's pseudometric, l. 6158) — `kobayashiPseudo`
* Definition (`d₁` and `d_n`, (7.2), l. 6164–6178) — `kobayashiD1`, `kobayashiDn`
* Theorem 1 (`σ_M = lim d_n`, l. 6180) — `thm7_1`
* Unlabelled (§7.1, l. 6205; used l. 6227: holomorphic maps contract Kobayashi's pseudometric) — `para7_1_contraction`
* Unlabelled (Example 4, (7.3), l. 6217; used l. 6237: `σ_M(0, v) = tanh⁻¹ ‖v‖` on the unit ball of a complex Banach
  space) — `para7_1_unit_ball`

Not items (DESIGN §3): Examples 1–3 (l. 6209–6213, not cited), the remark `σ = d₁` when `d₁` is a pseudometric
(l. 6207).

**[CORRECTION] (7.1), (7.3)** (l. 6150, 6221; GL8:5993, 6065). The book prints `σ_Δ(z, w) = ½ tanh⁻¹|(z − w)/(1 −
w̄z)|` and `σ_M(0, v) = ½ tanh⁻¹ ‖v‖`. Poincaré's metric of curvature −4 (l. 6146), `|dz|/(1 − |z|²)`, has distance
`tanh⁻¹|(z − w)/(1 − w̄z)| = ½ log((1 + r)/(1 − r))`, and the chapter's theorem `σ = d` needs
`σ(0, [μ]) = ½ log K₀ = tanh⁻¹ ‖μ‖∞` (l. 4583; Exercise 2, l. 6519). The statements use `tanh⁻¹`, i.e.
`LiZhongQC.discPoincareDist`. Leader-verified (calibration of Part B). [misprint] Example 4 says "unit ball in a
complex Banach manifold `B`": a Banach space.

**Conventions (B0.5).** Kobayashi's pseudometric is defined for any set `D` of "holomorphic discs" `f : ℂ → X` (only
`f|Δ` matters), with values in `ℝ≥0∞`: the largest `ℝ≥0∞`-valued pseudometric for which every `f ∈ D` is a
contraction from `(Δ, σ_Δ)`. For a complex Banach manifold `M` (Mathlib: `ChartedSpace E M`,
`IsManifold 𝓘(ℂ, E) ω M`) `D` is the set of holomorphic maps of `Δ` into `M` (`holDiscs`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (unitDisc discPoincareDist)

/-- Helper for Definition 1. `δ` is an `ℝ≥0∞`-valued pseudometric on `X` for which every disc `f ∈ D` is a
contraction: `δ(f z, f w) ≤ σ_Δ(z, w)` for `z, w ∈ Δ`. -/
def IsKobayashiAdmissible {X : Type*} (D : Set (ℂ → X)) (δ : X → X → ℝ≥0∞) : Prop :=
  (∀ x, δ x x = 0) ∧ (∀ x y, δ x y = δ y x) ∧ (∀ x y z, δ x z ≤ δ x y + δ y z) ∧
    ∀ f ∈ D, ∀ z ∈ unitDisc, ∀ w ∈ unitDisc, δ (f z) (f w) ≤ ENNReal.ofReal (discPoincareDist z w)

/-- **Definition 1** (Kobayashi's pseudometric, §7.1, l. 6158). The largest pseudometric `σ_M` on `M` with
`σ_M(f(z), f(w)) ≤ σ_Δ(z, w)` for all `z, w ∈ Δ` and all holomorphic `f : Δ → M` (here: all `f ∈ D`). -/
def kobayashiPseudo {X : Type*} (D : Set (ℂ → X)) (P Q : X) : ℝ≥0∞ :=
  ⨆ (δ : X → X → ℝ≥0∞) (_ : IsKobayashiAdmissible D δ), δ P Q

/-- **Definition** (§7.1, l. 6164–6168). `d₁(P, Q) = inf σ_Δ(z, w)` over the `z, w ∈ Δ` for which some disc
`f ∈ D` has `f(z) = P` and `f(w) = Q` (`∞` if there is none). -/
def kobayashiD1 {X : Type*} (D : Set (ℂ → X)) (P Q : X) : ℝ≥0∞ :=
  ⨅ (f : ℂ → X) (z : ℂ) (w : ℂ) (_ : f ∈ D ∧ z ∈ unitDisc ∧ w ∈ unitDisc ∧ f z = P ∧ f w = Q),
    ENNReal.ofReal (discPoincareDist z w)

/-- **Definition** ((7.2), §7.1, l. 6174). `d_n(P, Q) = inf Σ_{i=1}^n d₁(P_{i−1}, P_i)` over the chains
`P₀ = P, P₁, …, P_n = Q`. -/
def kobayashiDn {X : Type*} (D : Set (ℂ → X)) (n : ℕ) (P Q : X) : ℝ≥0∞ :=
  ⨅ (c : Fin (n + 1) → X) (_ : c 0 = P ∧ c (Fin.last n) = Q),
    ∑ i : Fin n, kobayashiD1 D (c i.castSucc) (c i.succ)

/-- The holomorphic discs of a complex manifold `M` modelled on the complex Banach space `E`: the maps holomorphic
on the unit disc. -/
def holDiscs (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (M : Type*) [TopologicalSpace M]
    [ChartedSpace E M] : Set (ℂ → M) :=
  {f | MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ, E) f unitDisc}

/-- Helper for §7.1. Poincaré's distance is symmetric: `|1 − z̄w| = |1 − w̄z|`. -/
theorem gl7_dist_comm (z w : ℂ) : discPoincareDist z w = discPoincareDist w z := by
  have h : ‖(z - w) / (1 - conj z * w)‖ = ‖(w - z) / (1 - conj w * z)‖ := by
    rw [norm_div, norm_div, norm_sub_rev z w]
    congr 1
    rw [← Complex.norm_conj (1 - conj w * z)]
    congr 1
    simp only [map_sub, map_one, map_mul, Complex.conj_conj]
    ring
  show (1 / 2) * Real.log ((1 + ‖(z - w) / (1 - conj z * w)‖) / (1 - ‖(z - w) / (1 - conj z * w)‖)) =
    (1 / 2) * Real.log ((1 + ‖(w - z) / (1 - conj w * z)‖) / (1 - ‖(w - z) / (1 - conj w * z)‖))
  rw [h]

/-- Helper for §7.1. `σ_Δ(z, z) = 0`. -/
theorem gl7_dist_self (z : ℂ) : discPoincareDist z z = 0 := by
  show (1 / 2) * Real.log ((1 + ‖(z - z) / (1 - conj z * z)‖) / (1 - ‖(z - z) / (1 - conj z * z)‖)) = 0
  simp

/-- Helper for §7.1. Kobayashi's pseudometric is itself admissible (a supremum of admissible pseudometrics). -/
theorem gl7_admissible {X : Type*} (D : Set (ℂ → X)) : IsKobayashiAdmissible D (kobayashiPseudo D) := by
  refine ⟨fun x => ?_, fun x y => ?_, fun x y z => ?_, fun f hf z hz w hw => ?_⟩
  · exact le_antisymm (iSup₂_le fun δ hδ => by exact (hδ.1 x).le) zero_le
  · exact iSup_congr fun δ => iSup_congr fun hδ => hδ.2.1 x y
  · exact iSup₂_le fun δ hδ => (hδ.2.2.1 x y z).trans (add_le_add
      (le_iSup₂ (f := fun δ (_ : IsKobayashiAdmissible D δ) => δ x y) δ hδ)
      (le_iSup₂ (f := fun δ (_ : IsKobayashiAdmissible D δ) => δ y z) δ hδ))
  · exact iSup₂_le fun δ hδ => by exact hδ.2.2.2 f hf z hz w hw

/-- Helper for Theorem 1. A pseudometric is bounded by the length of any chain: `δ(c₀, cₙ) ≤ Σ δ(cᵢ, cᵢ₊₁)`. -/
theorem gl7_chain_le {X : Type*} {δ : X → X → ℝ≥0∞} (hrefl : ∀ x, δ x x = 0)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) :
    ∀ (n : ℕ) (c : Fin (n + 1) → X), δ (c 0) (c (Fin.last n)) ≤ ∑ i : Fin n, δ (c i.castSucc) (c i.succ) := by
  intro n
  induction n with
  | zero =>
    intro c
    show δ (c 0) (c 0) ≤ _
    rw [hrefl]
    exact zero_le
  | succ n ih =>
    intro c
    rw [Fin.sum_univ_castSucc]
    refine (htri _ (c (Fin.last n).castSucc) _).trans (add_le_add ?_ le_rfl)
    have h := ih (fun i => c i.castSucc)
    simpa only [Fin.castSucc_zero, Fin.succ_castSucc] using h

/-- Helper for Theorem 1. `d₁(x, x) = 0` when the constant discs belong to `D`. -/
theorem gl7_d1_self {X : Type*} {D : Set (ℂ → X)} (hconst : ∀ x : X, (fun _ : ℂ => x) ∈ D) (x : X) :
    kobayashiD1 D x x = 0 := by
  refine le_antisymm ?_ zero_le
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  refine iInf_le_of_le (fun _ : ℂ => x) (iInf_le_of_le 0 (iInf_le_of_le 0
    (iInf_le_of_le ⟨hconst x, h0, h0, rfl, rfl⟩ ?_)))
  rw [gl7_dist_self, ENNReal.ofReal_zero]

/-- Helper for Theorem 1. `d₁` is symmetric (exchange `z` and `w`). -/
theorem gl7_d1_comm {X : Type*} (D : Set (ℂ → X)) (x y : X) : kobayashiD1 D x y = kobayashiD1 D y x := by
  have h : ∀ x y : X, kobayashiD1 D x y ≤ kobayashiD1 D y x := fun x y =>
    le_iInf fun f => le_iInf fun z => le_iInf fun w => le_iInf fun h =>
      iInf_le_of_le f (iInf_le_of_le w (iInf_le_of_le z
        (iInf_le_of_le ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩ (by rw [gl7_dist_comm]))))
  exact le_antisymm (h x y) (h y x)

/-- Helper for Theorem 1. A disc of `D` gives `d₁(f z, f w) ≤ σ_Δ(z, w)`. -/
theorem gl7_d1_le {X : Type*} {D : Set (ℂ → X)} {f : ℂ → X} (hf : f ∈ D) {z w : ℂ} (hz : z ∈ unitDisc)
    (hw : w ∈ unitDisc) : kobayashiD1 D (f z) (f w) ≤ ENNReal.ofReal (discPoincareDist z w) :=
  iInf_le_of_le f (iInf_le_of_le z (iInf_le_of_le w (iInf_le_of_le ⟨hf, hz, hw, rfl, rfl⟩ le_rfl)))

/-- Helper for Theorem 1. Every admissible pseudometric is bounded by `d₁`. -/
theorem gl7_adm_le_d1 {X : Type*} {D : Set (ℂ → X)} {δ : X → X → ℝ≥0∞} (hδ : IsKobayashiAdmissible D δ)
    (x y : X) : δ x y ≤ kobayashiD1 D x y :=
  le_iInf fun f => le_iInf fun z => le_iInf fun w => le_iInf fun h => by
    obtain ⟨hf, hz, hw, rfl, rfl⟩ := h
    exact hδ.2.2.2 f hf z hz w hw

/-- Helper for Theorem 1. Every admissible pseudometric is bounded by every `d_n` (triangle inequality along the
chain). -/
theorem gl7_adm_le_dn {X : Type*} {D : Set (ℂ → X)} {δ : X → X → ℝ≥0∞} (hδ : IsKobayashiAdmissible D δ)
    (n : ℕ) (x y : X) : δ x y ≤ kobayashiDn D n x y :=
  le_iInf fun c => le_iInf fun hc => by
    rw [← hc.1, ← hc.2]
    exact (gl7_chain_le hδ.1 hδ.2.2.1 n c).trans (Finset.sum_le_sum fun i _ => gl7_adm_le_d1 hδ _ _)

/-- Helper for Theorem 1. `d_{n+1} ≤ d_n`: a chain is extended by repeating its end point (`d₁(y, y) = 0`). -/
theorem gl7_dn_succ_le {X : Type*} {D : Set (ℂ → X)} (hconst : ∀ x : X, (fun _ : ℂ => x) ∈ D) (n : ℕ)
    (x y : X) : kobayashiDn D (n + 1) x y ≤ kobayashiDn D n x y := by
  refine le_iInf fun c => le_iInf fun hc => ?_
  refine iInf_le_of_le (Fin.snoc c y : Fin (n + 2) → X) (iInf_le_of_le ⟨?_, ?_⟩ ?_)
  · rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from rfl, Fin.snoc_castSucc]
    exact hc.1
  · exact Fin.snoc_last _ _
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hc.2, gl7_d1_self hconst,
      add_zero, le_refl]

/-- Helper for Theorem 1. `d_n` is symmetric (reverse the chain). -/
theorem gl7_dn_comm {X : Type*} (D : Set (ℂ → X)) (n : ℕ) (x y : X) :
    kobayashiDn D n x y = kobayashiDn D n y x := by
  have h : ∀ x y : X, kobayashiDn D n x y ≤ kobayashiDn D n y x := by
    intro x y
    refine le_iInf fun c => le_iInf fun hc => ?_
    refine iInf_le_of_le (fun i => c (Fin.rev i)) (iInf_le_of_le ⟨?_, ?_⟩ ?_)
    · simp only [Fin.rev_zero]
      exact hc.2
    · simp only [Fin.rev_last]
      exact hc.1
    · refine le_of_eq ?_
      simp only [Fin.rev_castSucc, Fin.rev_succ]
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev]
      exact gl7_d1_comm D _ _
  exact le_antisymm (h x y) (h y x)

/-- Helper for Theorem 1. Concatenation of chains: `d_{n+m}(x, z) ≤ d_n(x, y) + d_m(y, z)`. -/
theorem gl7_dn_add {X : Type*} (D : Set (ℂ → X)) (n m : ℕ) (x y z : X) :
    kobayashiDn D (n + m) x z ≤ kobayashiDn D n x y + kobayashiDn D m y z := by
  unfold kobayashiDn
  rw [ENNReal.iInf_add]
  refine le_iInf fun c => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hc => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun c' => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hc' => ?_
  set e : Fin (n + m + 1) → X := fun k =>
    if h : (k : ℕ) ≤ n then c ⟨k, by omega⟩ else c' ⟨k - n, by omega⟩ with hedef
  have e1 : ∀ i : Fin n, e (Fin.castAdd m i).castSucc = c i.castSucc := fun i => by
    have hi : ((Fin.castAdd m i).castSucc : ℕ) ≤ n := by have := i.isLt; show (i : ℕ) ≤ n; omega
    simp only [hedef, hi, dite_true]
    congr 1
  have e2 : ∀ i : Fin n, e (Fin.castAdd m i).succ = c i.succ := fun i => by
    have hi : ((Fin.castAdd m i).succ : ℕ) ≤ n := by have := i.isLt; show (i : ℕ) + 1 ≤ n; omega
    simp only [hedef, hi, dite_true]
    congr 1
  have e3 : ∀ j : Fin m, e (Fin.natAdd n j).castSucc = c' j.castSucc := fun j => by
    by_cases hj : (j : ℕ) = 0
    · have hi : ((Fin.natAdd n j).castSucc : ℕ) ≤ n := by show n + (j : ℕ) ≤ n; omega
      simp only [hedef, hi, dite_true]
      have h1 : (⟨((Fin.natAdd n j).castSucc : ℕ), by omega⟩ : Fin (n + 1)) = Fin.last n := by
        ext; simp; omega
      have h2 : j.castSucc = 0 := by ext; simp [hj]
      rw [h1, hc.2, h2, hc'.1]
    · have hi : ¬ ((Fin.natAdd n j).castSucc : ℕ) ≤ n := by show ¬ n + (j : ℕ) ≤ n; omega
      simp only [hedef, hi, dite_false]
      congr 1
      ext
      simp
  have e4 : ∀ j : Fin m, e (Fin.natAdd n j).succ = c' j.succ := fun j => by
    have hi : ¬ ((Fin.natAdd n j).succ : ℕ) ≤ n := by show ¬ n + (j : ℕ) + 1 ≤ n; omega
    simp only [hedef, hi, dite_false]
    congr 1
    ext
    simp
    omega
  refine iInf_le_of_le e (iInf_le_of_le ⟨?_, ?_⟩ ?_)
  · have hi : ((0 : Fin (n + m + 1)) : ℕ) ≤ n := by simp
    simp only [hedef, hi, dite_true]
    rw [← hc.1]
    rfl
  · by_cases hm : m = 0
    · subst hm
      have hi : ((Fin.last (n + 0)) : ℕ) ≤ n := by simp
      simp only [hedef, hi, dite_true]
      have h1 : (⟨((Fin.last (n + 0)) : ℕ), by omega⟩ : Fin (n + 1)) = Fin.last n := by ext; simp
      rw [h1, hc.2, ← hc'.1, ← hc'.2]
      rfl
    · have hi : ¬ ((Fin.last (n + m)) : ℕ) ≤ n := by simp; omega
      simp only [hedef, hi, dite_false]
      rw [← hc'.2]
      congr 1
      ext
      simp
  · rw [Fin.sum_univ_add]
    simp only [e1, e2, e3, e4]
    exact le_rfl

/-- Helper for Theorem 1. `d_∞ = inf_n d_n` is admissible: a pseudometric (constant chains, reversed chains,
concatenated chains) for which every disc is a contraction (`d_∞ ≤ d_1 ≤ d₁`). -/
theorem gl7_dinf_adm {X : Type*} {D : Set (ℂ → X)} (hconst : ∀ x : X, (fun _ : ℂ => x) ∈ D) :
    IsKobayashiAdmissible D fun x y => ⨅ n, kobayashiDn D n x y := by
  have hanti : ∀ x y : X, Antitone fun n => kobayashiDn D n x y := fun x y =>
    antitone_nat_of_succ_le fun n => gl7_dn_succ_le hconst n x y
  refine ⟨fun x => ?_, fun x y => ?_, fun x y z => ?_, fun f hf z hz w hw => ?_⟩
  · refine le_antisymm (iInf_le_of_le 0 ?_) zero_le
    unfold kobayashiDn
    refine (iInf₂_le (fun _ : Fin 1 => x) ⟨rfl, rfl⟩).trans ?_
    simp
  · exact iInf_congr fun n => gl7_dn_comm D n x y
  · rw [ENNReal.iInf_add_iInf fun i j => ⟨max i j, add_le_add (hanti x y (le_max_left i j))
      (hanti y z (le_max_right i j))⟩]
    exact le_iInf fun a => (iInf_le _ (a + a)).trans (gl7_dn_add D a a x y z)
  · refine (iInf_le _ 1).trans ?_
    unfold kobayashiDn
    refine (iInf₂_le (![f z, f w] : Fin 2 → X) ⟨rfl, rfl⟩).trans ?_
    simpa using gl7_d1_le hf hz hw

/-- **Theorem 1** (§7.1, l. 6180). On a connected complex manifold `M` modelled on a complex Banach space,
`σ_M(P, Q) = lim_{n → ∞} d_n(P, Q)` for any `P, Q ∈ M`. -/
theorem thm7_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] [ConnectedSpace M] (P Q : M) :
    Tendsto (fun n => kobayashiDn (holDiscs E M) n P Q) atTop (𝓝 (kobayashiPseudo (holDiscs E M) P Q)) := by
  -- connectedness (finiteness of `σ_M`) and completeness of `E` are not needed for the limit in `ℝ≥0∞`
  have _hc : ConnectedSpace M := inferInstance
  have _hE : CompleteSpace E := inferInstance
  have hconst : ∀ x : M, (fun _ : ℂ => x) ∈ holDiscs E M := fun x => mdifferentiableOn_const
  have hanti : Antitone fun n => kobayashiDn (holDiscs E M) n P Q :=
    antitone_nat_of_succ_le fun n => gl7_dn_succ_le hconst n P Q
  have e : ⨅ n, kobayashiDn (holDiscs E M) n P Q = kobayashiPseudo (holDiscs E M) P Q := by
    refine le_antisymm ?_ (iSup₂_le fun δ hδ => le_iInf fun n => gl7_adm_le_dn hδ n P Q)
    exact le_iSup₂ (f := fun δ (_ : IsKobayashiAdmissible (holDiscs E M) δ) => δ P Q)
      (fun x y => ⨅ n, kobayashiDn (holDiscs E M) n x y) (gl7_dinf_adm hconst)
  rw [← e]
  exact tendsto_atTop_iInf hanti

/-- **Unlabelled** (§7.1, l. 6205). A holomorphic map `F : M → N` of complex Banach manifolds is a contraction for
Kobayashi's pseudometrics: `σ_N(F(P), F(Q)) ≤ σ_M(P, Q)`. -/
theorem para7_1_contraction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [CompleteSpace E'] {N : Type*} [TopologicalSpace N] [ChartedSpace E' N]
    [IsManifold 𝓘(ℂ, E') ω N] {F : M → N} (hF : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E') F) (P Q : M) :
    kobayashiPseudo (holDiscs E' N) (F P) (F Q) ≤ kobayashiPseudo (holDiscs E M) P Q := by
  -- completeness of `E`, `E'` is not needed
  have _hE : CompleteSpace E := inferInstance
  have _hE' : CompleteSpace E' := inferInstance
  have h := gl7_admissible (holDiscs E' N)
  have hadm : IsKobayashiAdmissible (holDiscs E M)
      fun x y => kobayashiPseudo (holDiscs E' N) (F x) (F y) :=
    ⟨fun x => h.1 (F x), fun x y => h.2.1 (F x) (F y), fun x y z => h.2.2.1 (F x) (F y) (F z),
      fun f hf z hz w hw => h.2.2.2 (F ∘ f) (hF.comp_mdifferentiableOn hf) z hz w hw⟩
  exact le_iSup₂ (f := fun δ (_ : IsKobayashiAdmissible (holDiscs E M) δ) => δ P Q) _ hadm

/-- Helper for Example 4. The triangle inequality for `σ_Δ` on `Δ` (`Pommerenke1992.eq1_2_6` for `λ = hypDistD`,
which is `σ_Δ` by `Pommerenke1992.eq1_2_8`). -/
theorem gl7_dist_triangle {z w u : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) (hu : u ∈ unitDisc) :
    discPoincareDist z u ≤ discPoincareDist z w + discPoincareDist w u := by
  have e : ∀ {a b : ℂ}, a ∈ unitDisc → b ∈ unitDisc → discPoincareDist a b = Pommerenke1992.hypDistD a b :=
    fun {a b} ha hb => by
      rw [Pommerenke1992.eq1_2_8 ha hb]
      show (1 / 2) * Real.log ((1 + ‖(a - b) / (1 - conj a * b)‖) / (1 - ‖(a - b) / (1 - conj a * b)‖)) = _
      rw [norm_div]
  rw [e hz hu, e hz hw, e hw hu]
  exact Pommerenke1992.eq1_2_6 hz hw hu

/-- **Unlabelled** (Example 4, (7.3), §7.1, l. 6217). Let `M` be the unit ball of a complex Banach space `B`. Then
`σ_M(0, v) = tanh⁻¹ ‖v‖` for `v ∈ M` [CORRECTION of the printed `½ tanh⁻¹`]. Modelling: the holomorphic discs of `M`
are the holomorphic maps of `Δ` into the ball. -/
theorem para7_1_unit_ball {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (v : ball (0 : B) 1) :
    kobayashiPseudo {f : ℂ → ball (0 : B) 1 | DifferentiableOn ℂ (fun t => (f t : B)) unitDisc}
        ⟨0, mem_ball_self one_pos⟩ v =
      ENNReal.ofReal (discPoincareDist 0 (‖(v : B)‖ : ℂ)) := by
  -- completeness of `B` is not needed
  have _hB : CompleteSpace B := inferInstance
  have h0 : (0 : ℂ) ∈ unitDisc := mem_ball_self one_pos
  have hv1 : ‖(v : B)‖ < 1 := mem_ball_zero_iff.1 v.2
  have hvD : ((‖(v : B)‖ : ℝ) : ℂ) ∈ unitDisc := by
    rw [unitDisc, mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact hv1
  have hball : ∀ (ℓ : B →L[ℂ] ℂ), ‖ℓ‖ ≤ 1 → ∀ x : ball (0 : B) 1, ℓ x ∈ unitDisc := fun ℓ hℓ x => by
    rw [unitDisc, mem_ball_zero_iff]
    calc ‖ℓ x‖ ≤ ‖ℓ‖ * ‖(x : B)‖ := ℓ.le_opNorm _
      _ ≤ 1 * ‖(x : B)‖ := mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact mem_ball_zero_iff.1 x.2
  apply le_antisymm
  · -- every admissible `δ` is bounded through the disc `t ↦ t v/‖v‖`
    refine iSup₂_le fun δ hδ => ?_
    by_cases hv : (v : B) = 0
    · have : v = ⟨0, mem_ball_self one_pos⟩ := Subtype.ext hv
      rw [this, hδ.1]
      exact zero_le
    set u : B := ((‖(v : B)‖ : ℂ))⁻¹ • (v : B) with hu
    have hun : ‖u‖ = 1 := by
      rw [hu, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
    set f : ℂ → ball (0 : B) 1 := fun t =>
      if h : ‖t‖ < 1 then ⟨t • u, by rw [mem_ball_zero_iff, norm_smul, hun, mul_one]; exact h⟩
      else ⟨0, mem_ball_self one_pos⟩ with hfdef
    have hfv : ∀ t ∈ unitDisc, (f t : B) = t • u := fun t ht => by
      have h : ‖t‖ < 1 := mem_ball_zero_iff.1 ht
      simp only [hfdef, h, dite_true]
    have hfD : f ∈ {f : ℂ → ball (0 : B) 1 | DifferentiableOn ℂ (fun t => (f t : B)) unitDisc} :=
      (differentiable_id.smul_const u).differentiableOn.congr fun t ht => hfv t ht
    have hf0 : f 0 = ⟨0, mem_ball_self one_pos⟩ := Subtype.ext (by rw [hfv 0 h0, zero_smul])
    have hf1 : f ((‖(v : B)‖ : ℝ) : ℂ) = v := Subtype.ext (by
      rw [hfv _ hvD, hu, smul_smul, mul_inv_cancel₀ (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv)), one_smul])
    have h := hδ.2.2.2 f hfD 0 h0 _ hvD
    rwa [hf0, hf1] at h
  · -- the Carathéodory-type pseudometric `sup_{‖ℓ‖ ≤ 1} σ_Δ(ℓ x, ℓ y)` is admissible
    set δ : ball (0 : B) 1 → ball (0 : B) 1 → ℝ≥0∞ := fun x y =>
      ⨆ (ℓ : B →L[ℂ] ℂ) (_ : ‖ℓ‖ ≤ 1), ENNReal.ofReal (discPoincareDist (ℓ x) (ℓ y)) with hδdef
    have hadm : IsKobayashiAdmissible
        {f : ℂ → ball (0 : B) 1 | DifferentiableOn ℂ (fun t => (f t : B)) unitDisc} δ := by
      refine ⟨fun x => ?_, fun x y => ?_, fun x y z => ?_, fun f hf z hz w hw => ?_⟩
      · refine le_antisymm (iSup₂_le fun ℓ _ => ?_) zero_le
        rw [gl7_dist_self, ENNReal.ofReal_zero]
      · exact iSup_congr fun ℓ => iSup_congr fun _ => by rw [gl7_dist_comm]
      · refine iSup₂_le fun ℓ hℓ => ?_
        calc ENNReal.ofReal (discPoincareDist (ℓ x) (ℓ z))
            ≤ ENNReal.ofReal (discPoincareDist (ℓ x) (ℓ y) + discPoincareDist (ℓ y) (ℓ z)) :=
              ENNReal.ofReal_le_ofReal (gl7_dist_triangle (hball ℓ hℓ x) (hball ℓ hℓ y) (hball ℓ hℓ z))
          _ ≤ ENNReal.ofReal (discPoincareDist (ℓ x) (ℓ y)) + ENNReal.ofReal (discPoincareDist (ℓ y) (ℓ z)) :=
              ENNReal.ofReal_add_le
          _ ≤ δ x y + δ y z := add_le_add
              (le_iSup₂ (f := fun (ℓ : B →L[ℂ] ℂ) (_ : ‖ℓ‖ ≤ 1) =>
                ENNReal.ofReal (discPoincareDist (ℓ x) (ℓ y))) ℓ hℓ)
              (le_iSup₂ (f := fun (ℓ : B →L[ℂ] ℂ) (_ : ‖ℓ‖ ≤ 1) =>
                ENNReal.ofReal (discPoincareDist (ℓ y) (ℓ z))) ℓ hℓ)
      · refine iSup₂_le fun ℓ hℓ => ENNReal.ofReal_le_ofReal ?_
        have hgd : DifferentiableOn ℂ (fun t => ℓ (f t : B)) unitDisc :=
          ℓ.differentiable.comp_differentiableOn hf
        have hgm : MapsTo (fun t => ℓ (f t : B)) unitDisc unitDisc := fun t _ => hball ℓ hℓ (f t)
        exact (lemma2_1_b hgd hgm).1 z hz w hw
    refine (le_trans ?_ (le_iSup₂ (f := fun δ (_ : IsKobayashiAdmissible
      {f : ℂ → ball (0 : B) 1 | DifferentiableOn ℂ (fun t => (f t : B)) unitDisc} δ) =>
        δ ⟨0, mem_ball_self one_pos⟩ v) δ hadm))
    obtain ⟨ℓ, hℓ1, hℓv⟩ := exists_dual_vector'' ℂ (v : B)
    refine le_trans ?_ (le_iSup₂ (f := fun (ℓ : B →L[ℂ] ℂ) (_ : ‖ℓ‖ ≤ 1) =>
      ENNReal.ofReal (discPoincareDist (ℓ (0 : B)) (ℓ (v : B)))) ℓ hℓ1)
    rw [map_zero, hℓv]
    exact le_rfl

end GardinerLakic2000
