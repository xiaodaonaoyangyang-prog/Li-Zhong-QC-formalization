import LiZhongQC.Lemmas.SchottkyGenusBridge7
import LiZhongQC.Lemmas.SchottkyGenusBridge8
import LiZhongQC.Lemmas.SchottkyGenusBridge9
import LiZhongQC.Lemmas.SchottkyClosedSurface2

open Set Metric Topology unitInterval DifferentialGeometry.Topology.VanKampen

universe u

namespace LiZhongQC

section chain_sets

variable {X : Type u} [TopologicalSpace X] [T2Space X] {m : ℕ}
  (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
  (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
  (hdisj : Pairwise fun i j => Disjoint
    (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
  (Ω : ℕ → Set X)
  (hΩ : ∀ k, Ω k = (⋃ (j : Fin m) (_ : k ≤ j.val), v j '' closedBall (0 : ℂ) (1 / R j))ᶜ)

include hR hΩ in
theorem s78dg_chain_mem (k : ℕ) (x : X) :
    x ∈ Ω k ↔ ∀ i : Fin m, k ≤ i.val → x ∉ v i '' closedBall (0 : ℂ) (1 / R i) := by
  rw [hΩ]
  simp

include hR hs hΩ in
theorem s78dg_chain_open (k : ℕ) : IsOpen (Ω k) := by
  rw [hΩ, isOpen_compl_iff]
  refine isClosed_iUnion_of_finite (fun j => isClosed_iUnion_of_finite (fun _ => ?_))
  have hR0 : 0 < 1 / R j := by have := hR j; positivity
  have hsub : closedBall (0 : ℂ) (1 / R j) ⊆ (v j).source := by
    refine (closedBall_subset_closedBall ?_).trans (hs j)
    have := hR j
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact ((isCompact_closedBall (0 : ℂ) (1 / R j)).image_of_continuousOn
    ((v j).continuousOn.mono hsub)).isClosed

include hΩ in
theorem s78dg_chain_mono {k l : ℕ} (h : k ≤ l) : Ω k ⊆ Ω l := by
  intro x hx
  rw [hΩ] at hx ⊢
  intro hmem
  apply hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
  obtain ⟨hjl, hjx⟩ := mem_iUnion.mp hj
  exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨h.trans hjl, hjx⟩⟩

include hΩ in
theorem s78dg_chain_top : Ω m = univ := by
  rw [hΩ]
  ext x
  simp only [mem_compl_iff, mem_iUnion, not_exists, mem_univ, iff_true]
  intro j hj
  exact absurd j.2 (not_lt.mpr hj)

include hR hs hdisj hΩ in
theorem s78dg_chain_succ (k : ℕ) (hk : k < m) :
    Ω (k + 1) = Ω k ∪ v ⟨k, hk⟩ '' ball (0 : ℂ) (R ⟨k, hk⟩) ∧
    Ω k ∩ v ⟨k, hk⟩ '' ball (0 : ℂ) (R ⟨k, hk⟩) =
      v ⟨k, hk⟩ '' {z : ℂ | 1 / R ⟨k, hk⟩ < ‖z‖ ∧ ‖z‖ < R ⟨k, hk⟩} := by
  have hmem := s78dg_chain_mem v R hR Ω hΩ
  have hball : ∀ i, ball (0 : ℂ) (R i) ⊆ (v i).source :=
    fun i => ball_subset_closedBall.trans (hs i)
  have hr : ∀ i, 1 / R i < R i := by
    intro i
    have := hR i
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hDO : ∀ i, v i '' closedBall (0 : ℂ) (1 / R i) ⊆ v i '' ball (0 : ℂ) (R i) :=
    fun i => image_mono (closedBall_subset_ball (hr i))
  have hOd : ∀ i j : Fin m, i ≠ j →
      Disjoint (v i '' ball (0 : ℂ) (R i)) (v j '' ball (0 : ℂ) (R j)) := fun i j hij =>
    (hdisj hij).mono (image_mono ball_subset_closedBall) (image_mono ball_subset_closedBall)
  have hinj : ∀ i, ∀ w ∈ ball (0 : ℂ) (R i), ∀ w' ∈ ball (0 : ℂ) (R i), v i w = v i w' → w = w' :=
    fun i w hw w' hw' h => (v i).injOn (hball i hw) (hball i hw') h
  refine ⟨?_, ?_⟩
  · ext x
    constructor
    · intro hx
      by_cases hxk : x ∈ Ω k
      · exact Or.inl hxk
      · right
        have : ∃ i : Fin m, k ≤ i.val ∧ x ∈ v i '' closedBall (0 : ℂ) (1 / R i) := by
          by_contra h
          exact hxk ((hmem k x).2 (fun i hi hxi => h ⟨i, hi, hxi⟩))
        obtain ⟨i, hi, hxi⟩ := this
        have hik : i = ⟨k, hk⟩ := by
          apply Fin.ext
          by_contra hne
          have hne' : (i : ℕ) ≠ k := hne
          exact ((hmem (k + 1) x).1 hx) i (by omega) hxi
        subst hik
        exact hDO _ hxi
    · rintro (hx | hx)
      · exact s78dg_chain_mono v R Ω hΩ (Nat.le_succ k) hx
      · rw [hmem]
        intro i hi hxi
        have hne : i ≠ ⟨k, hk⟩ := by
          intro h
          rw [h] at hi
          simp at hi
        exact Set.disjoint_left.mp (hOd i _ hne) (hDO i hxi) hx
  · ext x
    constructor
    · rintro ⟨hxk, z, hz, rfl⟩
      refine ⟨z, ⟨?_, mem_ball_zero_iff.mp hz⟩, rfl⟩
      by_contra hle
      rw [not_lt] at hle
      exact ((hmem k _).1 hxk) ⟨k, hk⟩ le_rfl ⟨z, mem_closedBall_zero_iff.mpr hle, rfl⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      have hz : z ∈ ball (0 : ℂ) (R ⟨k, hk⟩) := mem_ball_zero_iff.mpr h2
      refine ⟨?_, ⟨z, hz, rfl⟩⟩
      rw [hmem]
      intro i hi hxi
      by_cases hij : i = ⟨k, hk⟩
      · subst hij
        obtain ⟨w, hw, he⟩ := hxi
        have hw' : w ∈ ball (0 : ℂ) (R ⟨k, hk⟩) := closedBall_subset_ball (hr _) hw
        have := hinj _ w hw' z hz he
        rw [this] at hw
        exact absurd (mem_closedBall_zero_iff.mp hw) (not_le.mpr h1)
      · exact Set.disjoint_left.mp (hOd i _ hij) (hDO i hxi) ⟨z, hz, rfl⟩

include hR hs hdisj hΩ in
theorem s78dg_chain_annulus_mem (j : Fin m) (z : ℂ) (h1 : 1 / R j < ‖z‖) (h2 : ‖z‖ < R j) :
    v j z ∈ Ω 0 := by
  have hmem := s78dg_chain_mem v R hR Ω hΩ
  have hball : ∀ i, ball (0 : ℂ) (R i) ⊆ (v i).source :=
    fun i => ball_subset_closedBall.trans (hs i)
  have hr : ∀ i, 1 / R i < R i := by
    intro i
    have := hR i
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hz : z ∈ ball (0 : ℂ) (R j) := mem_ball_zero_iff.mpr h2
  rw [hmem]
  intro i _ hxi
  by_cases hij : i = j
  · subst hij
    obtain ⟨w, hw, he⟩ := hxi
    have hw' : w ∈ ball (0 : ℂ) (R i) := closedBall_subset_ball (hr _) hw
    have := (v i).injOn (hball i hw') (hball i hz) he
    rw [this] at hw
    exact absurd (mem_closedBall_zero_iff.mp hw) (not_le.mpr h1)
  · exact Set.disjoint_left.mp
      ((hdisj hij).mono (image_mono ((closedBall_subset_ball (hr i)).trans ball_subset_closedBall))
        (image_mono ((ball_subset_closedBall : ball (0 : ℂ) (R j) ⊆ _))))
      hxi ⟨z, hz, rfl⟩

include hR hs hdisj hΩ in
theorem s78dg_chain_pc (h0 : IsPathConnected (Ω 0)) : ∀ k, k ≤ m → IsPathConnected (Ω k) := by
  intro k
  induction k with
  | zero => intro _; exact h0
  | succ k ih =>
    intro hk
    have hk' : k < m := hk
    have hih := ih hk'.le
    obtain ⟨hu, hi⟩ := s78dg_chain_succ v R hR hs hdisj Ω hΩ k hk'
    have hball : ball (0 : ℂ) (R ⟨k, hk'⟩) ⊆ (v ⟨k, hk'⟩).source :=
      ball_subset_closedBall.trans (hs _)
    have hV : IsPathConnected (v ⟨k, hk'⟩ '' ball (0 : ℂ) (R ⟨k, hk'⟩)) :=
      ((convex_ball (0 : ℂ) _).isPathConnected ⟨0, mem_ball_self (by have := hR ⟨k, hk'⟩; linarith)⟩).image'
        ((v ⟨k, hk'⟩).continuousOn.mono hball)
    have h1 : (1 : ℂ) ∈ {z : ℂ | 1 / R ⟨k, hk'⟩ < ‖z‖ ∧ ‖z‖ < R ⟨k, hk'⟩} := by
      have := hR ⟨k, hk'⟩
      refine ⟨?_, by simpa using this⟩
      simp only [norm_one]
      exact (div_lt_one (by linarith)).mpr this
    have hne : (Ω k ∩ v ⟨k, hk'⟩ '' ball (0 : ℂ) (R ⟨k, hk'⟩)).Nonempty := by
      rw [hi]
      exact ⟨_, mem_image_of_mem _ h1⟩
    rw [hu]
    exact hih.union hV hne

end chain_sets

section chain_ind

variable {X : Type u} [TopologicalSpace X] [T2Space X] {m : ℕ}
  (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
  (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
  (hdisj : Pairwise fun i j => Disjoint
    (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
  (Ω : ℕ → Set X)
  (hΩ : ∀ k, Ω k = (⋃ (j : Fin m) (_ : k ≤ j.val), v j '' closedBall (0 : ℂ) (1 / R j))ᶜ)

include hR hs hdisj hΩ in
/-- **The kernel of `π₁(Ω₀) → π₁(Ω_k)` is normally generated by the first `k` unit circles.** -/
theorem s78dg_chain_induct (h0 : IsPathConnected (Ω 0)) (x : ↥(Ω 0))
    (z : Fin m → ↥(Ω 0)) (hz : ∀ j, ((z j : ↥(Ω 0)) : X) = v j 1)
    (a : ∀ j : Fin m, Path x (z j)) (ℓ : ∀ j : Fin m, Path (z j) (z j))
    (hℓ : ∀ (j : Fin m) (t : I), ((ℓ j t : ↥(Ω 0)) : X) = v j (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ)) :
    ∀ k (hk : k ≤ m),
      Function.Surjective (FundamentalGroup.map
        (⟨Set.inclusion (s78dg_chain_mono v R Ω hΩ (Nat.zero_le k)),
          continuous_inclusion _⟩ : C(↥(Ω 0), ↥(Ω k))) x) ∧
      ∀ δ, FundamentalGroup.map
        (⟨Set.inclusion (s78dg_chain_mono v R Ω hΩ (Nat.zero_le k)),
          continuous_inclusion _⟩ : C(↥(Ω 0), ↥(Ω k))) x δ = 1 ↔
        δ ∈ Subgroup.normalClosure {t : FundamentalGroup ↥(Ω 0) x | ∃ j : Fin m, (j : ℕ) < k ∧
          t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (((a j).trans (ℓ j)).trans (a j).symm))} := by
  intro k
  induction k with
  | zero =>
    intro _
    have hb : Function.Bijective (FundamentalGroup.map
        (⟨Set.inclusion (s78dg_chain_mono v R Ω hΩ (Nat.zero_le 0)),
          continuous_inclusion _⟩ : C(↥(Ω 0), ↥(Ω 0))) x) :=
      s78dg_pi1_homeo_bijective (Homeomorph.refl _) x
    refine ⟨hb.2, fun δ => ?_⟩
    have hT : {t : FundamentalGroup ↥(Ω 0) x | ∃ j : Fin m, (j : ℕ) < 0 ∧
        t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (((a j).trans (ℓ j)).trans (a j).symm))} = ∅ := by
      ext t
      simp
    rw [hT, Subgroup.normalClosure_empty, Subgroup.mem_bot]
    constructor
    · intro h
      exact hb.1 (h.trans (map_one _).symm)
    · intro h
      rw [h, map_one]
  | succ k ih =>
    intro hk
    have hk' : k < m := Nat.lt_of_succ_le hk
    obtain ⟨ihs, ihk⟩ := ih hk'.le
    let j : Fin m := ⟨k, hk'⟩
    let ιk : C(↥(Ω 0), ↥(Ω k)) :=
      ⟨Set.inclusion (s78dg_chain_mono v R Ω hΩ (Nat.zero_le k)), continuous_inclusion _⟩
    have hsub : Ω k ⊆ Ω (k + 1) := s78dg_chain_mono v R Ω hΩ (Nat.le_succ k)
    let ιk' : C(↥(Ω k), ↥(Ω (k + 1))) := ⟨Set.inclusion hsub, continuous_inclusion hsub⟩
    let ιk1 : C(↥(Ω 0), ↥(Ω (k + 1))) :=
      ⟨Set.inclusion (s78dg_chain_mono v R Ω hΩ (Nat.zero_le (k + 1))), continuous_inclusion _⟩
    obtain ⟨hu, hi⟩ := s78dg_chain_succ v R hR hs hdisj Ω hΩ k hk'
    have hpcs := s78dg_chain_pc v R hR hs hdisj Ω hΩ h0 k hk'.le
    haveI hpck : PathConnectedSpace ↥(Ω k) := isPathConnected_iff_pathConnectedSpace.mp hpcs
    let yk : ↥(Ω k) := ιk (z j)
    obtain ⟨ℓ', hℓ', hs1, hk1⟩ := s78dg_chain_step (v j) (R j) (hR j) (hs j) (Ω k) (Ω (k + 1))
      (s78dg_chain_open v R hR hs Ω hΩ k) hsub hu hi hpck yk (hz j)
    let p : Path (ιk x) yk := (a j).map ιk.continuous
    obtain ⟨hbs, hbk⟩ := s78dg_bc_kernel ιk' p ℓ' hs1 hk1
    have hm : ∀ δ, FundamentalGroup.map ιk1 x δ =
        FundamentalGroup.map ιk' (ιk x) (FundamentalGroup.map ιk x δ) := by
      intro δ
      induction δ using Quotient.inductionOn with
      | h c => rfl
    let tj : FundamentalGroup ↥(Ω 0) x := FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((a j).trans (ℓ j)).trans (a j).symm))
    have hπt : FundamentalGroup.map ιk x tj = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((p.trans ℓ').trans p.symm)) := by
      have hℓeq : (ℓ j).map ιk.continuous = ℓ' := by
        ext t
        exact (hℓ j t).trans (hℓ' t).symm
      show Path.Homotopic.Quotient.mk ((((a j).trans (ℓ j)).trans (a j).symm).map ιk.continuous) = _
      rw [Path.map_trans, Path.map_trans, Path.map_symm, hℓeq]
    have hι : ∀ h, FundamentalGroup.map ιk' (ιk x) h = 1 ↔
        h ∈ Subgroup.normalClosure ({FundamentalGroup.map ιk x tj} : Set _) := by
      intro h
      rw [hπt]
      exact hbk h
    have hkc := s78dg_ker_comp (FundamentalGroup.map ιk x) (FundamentalGroup.map ιk' (ιk x))
      {t : FundamentalGroup ↥(Ω 0) x | ∃ j : Fin m, (j : ℕ) < k ∧
        t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (((a j).trans (ℓ j)).trans (a j).symm))} tj ihs ihk hι
    refine ⟨?_, fun δ => ?_⟩
    · have hfun : (FundamentalGroup.map ιk1 x : _ → _) =
          (FundamentalGroup.map ιk' (ιk x)) ∘ (FundamentalGroup.map ιk x) := funext hm
      rw [hfun]
      exact hbs.comp ihs
    · have hset : {t : FundamentalGroup ↥(Ω 0) x | ∃ j' : Fin m, (j' : ℕ) < k + 1 ∧
          t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (((a j').trans (ℓ j')).trans (a j').symm))} =
          insert tj {t : FundamentalGroup ↥(Ω 0) x | ∃ j' : Fin m, (j' : ℕ) < k ∧
            t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
              (((a j').trans (ℓ j')).trans (a j').symm))} := by
        ext t
        constructor
        · rintro ⟨j', hj', rfl⟩
          by_cases hjk : (j' : ℕ) = k
          · left
            have : j' = j := Fin.ext hjk
            subst this
            rfl
          · right
            exact ⟨j', by omega, rfl⟩
        · rintro (rfl | ⟨j', hj', rfl⟩)
          · exact ⟨j, Nat.lt_succ_self _, rfl⟩
          · exact ⟨j', by omega, rfl⟩
      rw [hset, ← hkc, hm]

end chain_ind

/-- **The kernel of `π₁(Core) → π₁(X)` is normally generated by the boundary circles.**  Core is the
complement of the open unit discs of disjoint charts; each boundary circle `|z| = 1`, joined to the
base point by an arbitrary path of the core, is a normal generator. -/
theorem s78dg_core_kernel_generic {X : Type u} [TopologicalSpace X] [T2Space X] {m : ℕ}
    (v : Fin m → OpenPartialHomeomorph ℂ X) (R : Fin m → ℝ) (hR : ∀ j, 1 < R j)
    (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (C : Set X) (hC : C = (⋃ j, v j '' ball (0 : ℂ) 1)ᶜ) (hCpc : IsPathConnected C) (x : ↥C)
    (z : Fin m → ↥C) (hz : ∀ j, ((z j : ↥C) : X) = v j 1)
    (a : ∀ j : Fin m, Path x (z j)) (ℓ : ∀ j : Fin m, Path (z j) (z j))
    (hℓ : ∀ (j : Fin m) (t : I),
      ((ℓ j t : ↥C) : X) = v j (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ)) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥C, X)) x) ∧
    ∀ δ, FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(↥C, X)) x δ = 1 ↔
      δ ∈ Subgroup.normalClosure {t : FundamentalGroup ↥C x | ∃ j : Fin m,
        t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (((a j).trans (ℓ j)).trans (a j).symm))} := by
  let Ω : ℕ → Set X := fun k => (⋃ (j : Fin m) (_ : k ≤ j.val), v j '' closedBall (0 : ℂ) (1 / R j))ᶜ
  have hΩ : ∀ k, Ω k = (⋃ (j : Fin m) (_ : k ≤ j.val), v j '' closedBall (0 : ℂ) (1 / R j))ᶜ :=
    fun k => rfl
  have hΩ0 : Ω 0 = (⋃ j, v j '' closedBall (0 : ℂ) ((fun j => 1 / R j) j))ᶜ := by
    ext y
    simp [Ω]
  have hρ0 : ∀ j, 0 < (fun j => 1 / R j) j := fun j => by
    have := hR j
    show 0 < 1 / R j
    positivity
  have hρ1 : ∀ j, (fun j => 1 / R j) j < 1 := fun j => by
    show 1 / R j < 1
    exact (div_lt_one (by have := hR j; linarith)).mpr (hR j)
  obtain ⟨e, he, hebij, hepc⟩ :=
    s78dg_inner_pi1 v R hR hs hdisj (fun j => 1 / R j) hρ0 hρ1 (Ω 0) C hΩ0 hC
  haveI hCpc' : PathConnectedSpace ↥C := isPathConnected_iff_pathConnectedSpace.mp hCpc
  haveI hΩpc : PathConnectedSpace ↥(Ω 0) := hepc hCpc'
  have h0 : IsPathConnected (Ω 0) := isPathConnected_iff_pathConnectedSpace.mpr hΩpc
  have hz' : ∀ j, ((e (z j) : ↥(Ω 0)) : X) = v j 1 := fun j => (he _).trans (hz j)
  have hℓ' : ∀ (j : Fin m) (t : I),
      ((((ℓ j).map e.continuous) t : ↥(Ω 0)) : X) =
        v j (Circle.exp (2 * Real.pi * (t : ℝ)) : ℂ) := fun j t => (he _).trans (hℓ j t)
  obtain ⟨hsm, hkm⟩ := s78dg_chain_induct v R hR hs hdisj Ω hΩ h0 (e x) (fun j => e (z j)) hz'
    (fun j => (a j).map e.continuous) (fun j => (ℓ j).map e.continuous) hℓ' m le_rfl
  let ιm : C(↥(Ω 0), ↥(Ω m)) :=
    ⟨Set.inclusion (s78dg_chain_mono v R Ω hΩ (Nat.zero_le m)), continuous_inclusion _⟩
  let H : ↥(Ω m) ≃ₜ X :=
    (Homeomorph.setCongr (s78dg_chain_top v R Ω hΩ)).trans (Homeomorph.Set.univ X)
  let Hc : C(↥(Ω m), X) := ⟨H, H.continuous⟩
  have hcomp : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥C, X)) = Hc.comp (ιm.comp e) := by
    ext y
    exact (he y).symm
  suffices key : ∀ (f : C(↥C, X)) (hf : f = Hc.comp (ιm.comp e)),
      Function.Surjective (FundamentalGroup.map f x) ∧ ∀ δ, FundamentalGroup.map f x δ = 1 ↔
        δ ∈ Subgroup.normalClosure {t : FundamentalGroup ↥C x | ∃ j : Fin m,
          t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (((a j).trans (ℓ j)).trans (a j).symm))} from key _ hcomp
  intro f hf
  subst hf
  have hm : ∀ δ, FundamentalGroup.map (Hc.comp (ιm.comp e)) x δ =
      FundamentalGroup.map Hc (ιm (e x)) (FundamentalGroup.map ιm (e x)
        (FundamentalGroup.map e x δ)) := by
    intro δ
    induction δ using Quotient.inductionOn with
    | h c => rfl
  have hHb : Function.Bijective (FundamentalGroup.map Hc (ιm (e x))) :=
    s78dg_pi1_homeo_bijective H (ιm (e x))
  refine ⟨?_, fun δ => ?_⟩
  · have hfun : (FundamentalGroup.map (Hc.comp (ιm.comp e)) x : _ → _) =
        (FundamentalGroup.map Hc (ιm (e x))) ∘ (FundamentalGroup.map ιm (e x)) ∘
          (FundamentalGroup.map e x) := funext hm
    rw [hfun]
    exact hHb.2.comp (hsm.comp (hebij x).2)
  · have himg : Subgroup.normalClosure {t : FundamentalGroup ↥(Ω 0) (e x) | ∃ j : Fin m,
          (j : ℕ) < m ∧ t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            ((((a j).map e.continuous).trans ((ℓ j).map e.continuous)).trans
              ((a j).map e.continuous).symm))} =
        (Subgroup.normalClosure {t : FundamentalGroup ↥C x | ∃ j : Fin m,
          t = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (((a j).trans (ℓ j)).trans (a j).symm))}).map (FundamentalGroup.map e x) := by
      rw [Subgroup.map_normalClosure _ _ (hebij x).2]
      congr 1
      ext t
      constructor
      · rintro ⟨j, -, rfl⟩
        refine ⟨_, ⟨j, rfl⟩, ?_⟩
        show FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((((a j).trans (ℓ j)).trans (a j).symm).map e.continuous)) = _
        rw [Path.map_trans, Path.map_trans, Path.map_symm]
      · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
        refine ⟨j, j.2, ?_⟩
        show FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          ((((a j).trans (ℓ j)).trans (a j).symm).map e.continuous)) = _
        rw [Path.map_trans, Path.map_trans, Path.map_symm]
    rw [hm, ← map_one (FundamentalGroup.map Hc (ιm (e x))), hHb.1.eq_iff]
    refine (hkm (FundamentalGroup.map e x δ)).trans ?_
    rw [himg]
    exact Subgroup.mem_map_iff_mem (hebij x).1

end LiZhongQC
