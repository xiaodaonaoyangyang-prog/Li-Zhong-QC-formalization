import LiZhongExternal.DifferentialGeometry.SchottkyVanKampen

universe u

namespace LiZhongQC

open Set unitInterval DifferentialGeometry.Topology.VanKampen

/-- A prefix of a path, as a class from the base point: composition of consecutive subpaths. -/
theorem s78dg_gen_pre {X : Type u} [TopologicalSpace X] {a b x : X} (γ : Path a b)
    (h : x = γ 0) (t u : I) :
    Path.Homotopic.Quotient.mk ((γ.subpath 0 u).cast h rfl) =
      (Path.Homotopic.Quotient.mk ((γ.subpath 0 t).cast h rfl)).trans
        (Path.Homotopic.Quotient.mk (γ.subpath t u)) := by
  subst h
  simp only [Path.cast_rfl_rfl]
  exact (Path.Homotopic.mk_subpath_trans_mk_subpath γ 0 t u).symm

theorem s78dg_gen_cancel {X : Type u} [TopologicalSpace X] {a b c d : X}
    (u : Path.Homotopic.Quotient a c) (v : Path.Homotopic.Quotient b c)
    (w : Path.Homotopic.Quotient c d) :
    (u.trans v.symm).trans (v.trans w) = u.trans w := by
  rw [Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.trans_assoc v.symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

theorem s78dg_gen_cancel2 {X : Type u} [TopologicalSpace X] {x y w : X}
    (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient y w) :
    a.symm.trans (a.trans b) = b := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem s78dg_gen_lam_alg {X : Type u} [TopologicalSpace X] {x z q : X}
    (u u' : Path.Homotopic.Quotient x z) (m m' : Path.Homotopic.Quotient x q)
    (α : Path.Homotopic.Quotient q z) :
    ((u.trans α.symm).trans m.symm).trans ((m.trans m'.symm).trans ((m'.trans α).trans u'.symm)) =
      u.trans u'.symm := by
  simp only [Path.Homotopic.Quotient.trans_assoc, s78dg_gen_cancel2]

theorem s78dg_gen_alg2 {X : Type u} [TopologicalSpace X] {x q : X}
    (m m' β β' : Path.Homotopic.Quotient x q) :
    ((m.trans β.symm).trans (β.trans β'.symm)).trans (β'.trans m'.symm) = m.trans m'.symm := by
  simp only [Path.Homotopic.Quotient.trans_assoc, s78dg_gen_cancel2]

theorem s78dg_gen_alg {X : Type u} [TopologicalSpace X] {x y y' z : X}
    (h : Path.Homotopic.Quotient x z) (A A0 : Path.Homotopic.Quotient z y)
    (π : Path.Homotopic.Quotient y y') (A1 : Path.Homotopic.Quotient z y') :
    (h.trans A).trans π =
      ((h.trans (A.trans A0.symm)).trans ((A0.trans π).trans A1.symm)).trans A1 := by
  rw [Path.Homotopic.Quotient.trans_assoc _ _ A1, Path.Homotopic.Quotient.trans_assoc _ A1.symm A1,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl,
    Path.Homotopic.Quotient.trans_assoc h A π,
    Path.Homotopic.Quotient.trans_assoc h (A.trans A0.symm) (A0.trans π), s78dg_gen_cancel]

/-- **Generation by a two-set cover.**  Let `sd true`, `sd false` be open sets covering `X`, with
chosen connecting paths `c s y` from `x₀` to each `y ∈ sd s` inside `sd s`.  A predicate `P` on
loop classes at `x₀` which is closed under composition, holds for all loops inside one set, and
holds for the "connector loops" `c s z · (c s' z)⁻¹` (`z` in both sets), holds for every path
class `x₀ → b` once it is corrected by a connector. -/
theorem s78dg_gen_two_cover {X : Type u} [TopologicalSpace X] (sd : Bool → Set X)
    (hopen : ∀ s, IsOpen (sd s)) (hcover : sd true ∪ sd false = univ) (x₀ : X)
    (c : ∀ (s : Bool) (y : X), y ∈ sd s → Path x₀ y)
    (hc : ∀ s y hy, range (c s y hy) ⊆ sd s)
    (P : Path.Homotopic.Quotient x₀ x₀ → Prop)
    (hP : ∀ a b, P a → P b → P (a.trans b))
    (hPs : ∀ s (ℓ : Path x₀ x₀), range ℓ ⊆ sd s → P (Path.Homotopic.Quotient.mk ℓ))
    (hlam : ∀ s s' z (hz : z ∈ sd s) (hz' : z ∈ sd s'),
      P ((Path.Homotopic.Quotient.mk (c s z hz)).trans
        (Path.Homotopic.Quotient.mk (c s' z hz')).symm))
    {b : X} (p : Path x₀ b) :
    ∃ s, ∃ hb : b ∈ sd s, ∃ h, P h ∧
      Path.Homotopic.Quotient.mk p =
        h.trans (Path.Homotopic.Quotient.mk (c s b hb)) := by
  obtain ⟨n, hn, hcov⟩ := DifferentialGeometry.Topology.VanKampen.Path.exists_isCovered p
    (hopen true) (hopen false) hcover
  have base : ∀ u : I, u = 0 → ∃ s, ∃ hy : p u ∈ sd s, ∃ h, P h ∧
      Path.Homotopic.Quotient.mk ((p.subpath 0 u).cast p.source.symm rfl) =
        h.trans (Path.Homotopic.Quotient.mk (c s (p u) hy)) := by
    intro u hu
    subst hu
    have hx : x₀ ∈ sd true ∪ sd false := by rw [hcover]; trivial
    have hsd : ∃ s, x₀ ∈ sd s := by
      rcases hx with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    obtain ⟨s, hs⟩ := hsd
    have hy : p 0 ∈ sd s := by rw [p.source]; exact hs
    refine ⟨s, hy, (Path.Homotopic.Quotient.mk ((Path.refl (p 0)).cast p.source.symm rfl)).trans
      (Path.Homotopic.Quotient.mk (c s (p 0) hy)).symm, ?_, ?_⟩
    · rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans]
      apply hPs s
      rw [Path.trans_range, Path.symm_range]
      refine union_subset ?_ (hc s _ hy)
      rintro _ ⟨t, rfl⟩
      simpa using hy
    · rw [Path.subpath_self, Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  have key : ∀ j : Fin (n + 1), ∃ s, ∃ hy : p (standardTime n j) ∈ sd s, ∃ h, P h ∧
      Path.Homotopic.Quotient.mk ((p.subpath 0 (standardTime n j)).cast p.source.symm rfl) =
        h.trans (Path.Homotopic.Quotient.mk (c s (p (standardTime n j)) hy)) := by
    intro j
    induction j using Fin.induction with
    | zero => exact base _ (standardTime_zero n)
    | succ i ih =>
      obtain ⟨s, hy, h, hPh, heq⟩ := ih
      have hside : ∃ s', range (standardSubpath p i) ⊆ sd s' := by
        rcases hcov i with h1 | h1
        · exact ⟨true, h1⟩
        · exact ⟨false, h1⟩
      obtain ⟨s', hs'⟩ := hside
      have hy0 : p (standardTime n i.castSucc) ∈ sd s' :=
        hs' ⟨0, (standardSubpath p i).source⟩
      have hy1 : p (standardTime n i.succ) ∈ sd s' :=
        hs' ⟨1, (standardSubpath p i).target⟩
      refine ⟨s', hy1, ((h.trans ((Path.Homotopic.Quotient.mk (c s _ hy)).trans
        (Path.Homotopic.Quotient.mk (c s' _ hy0)).symm)).trans
        (Path.Homotopic.Quotient.mk (((c s' _ hy0).trans (standardSubpath p i)).trans
          (c s' _ hy1).symm))), ?_, ?_⟩
      · refine hP _ _ (hP _ _ hPh (hlam _ _ _ hy hy0)) ?_
        apply hPs s'
        rw [Path.trans_range, Path.trans_range, Path.symm_range]
        exact union_subset (union_subset (hc s' _ hy0) hs') (hc s' _ hy1)
      · rw [s78dg_gen_pre p p.source.symm (standardTime n i.castSucc) (standardTime n i.succ),
          heq]
        have hπ : Path.Homotopic.Quotient.mk (p.subpath (standardTime n i.castSucc)
            (standardTime n i.succ)) = Path.Homotopic.Quotient.mk (standardSubpath p i) := rfl
        rw [hπ, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
          Path.Homotopic.Quotient.mk_symm]
        apply s78dg_gen_alg
  obtain ⟨s, hy, h, hPh, heq⟩ := key (Fin.last n)
  have hu : standardTime n (Fin.last n) = 1 := standardTime_last hn
  have e : p (standardTime n (Fin.last n)) = b := by rw [hu]; exact p.target
  have conv : ∀ (y' : X) (e : y' = p (standardTime n (Fin.last n))) (hy' : y' ∈ sd s),
      Path.Homotopic.Quotient.mk
        (((p.subpath 0 (standardTime n (Fin.last n))).cast p.source.symm rfl).cast rfl e) =
        h.trans (Path.Homotopic.Quotient.mk (c s y' hy')) := by
    intro y' e'
    subst e'
    intro hy'
    simpa only [Path.cast_rfl_rfl] using heq
  have hb : b ∈ sd s := e ▸ hy
  refine ⟨s, hb, h, hPh, ?_⟩
  have hpp : (((p.subpath 0 (standardTime n (Fin.last n))).cast p.source.symm rfl).cast rfl e.symm) =
      p := by
    ext t
    simp [Path.subpath, hu]
  rw [← hpp]
  exact conv b e.symm hb


end LiZhongQC
