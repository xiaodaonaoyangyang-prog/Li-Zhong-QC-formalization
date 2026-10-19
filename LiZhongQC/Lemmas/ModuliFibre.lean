import LiZhongQC.Lemmas.DehnTwist
import LiZhongQC.Lemmas.UniformizedTeichmuller

/-!
# Full M3 proposal: moduli fibres and the exact amended book theorem

STATIC ONLY: UNFROZEN, UNELABORATED and UNPROVED. M2 is archive-only.
All six theorem bodies remain sorry. The original M3 bridge docstring/header
and installed S28 book docstring/header are copied byte-exact. The book proof
will be assembled only after leader freeze. No new definition or import beyond
the two authorized imports is proposed. Planned module: Lemmas/ModuliFibre.
-/

open Set Topology
open scoped Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

/-- Infinitely many distinct homotopy classes of QC self-homeomorphisms give
an infinite fibre over any genus-g surface admitting a QC marking. The finite
biholomorphic automorphism group absorbs only finitely many such classes per
point of Teichmuller space. No false converse of markedRS_equiv_same_surface is used. -/
theorem s28m_infinite_fibre_of_twist {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {g : ℕ} (hg : 1 < g) (X : ClosedRS.{u}) (hX : HasGenus X.carrier g)
    (f₀ : S ≃ₜ X.carrier) (hf₀ : IsQCRS f₀)
    (T : ℤ → (S ≃ₜ S)) (hT : ∀ k : ℤ, IsQCRS (T k))
    (hsep : ∀ m n : ℤ,
      ContinuousMap.Homotopic (T m : C(S, S)) (T n : C(S, S)) → m = n) :
    Set.Infinite {q : TeichSpace S | LiesOver q (Quot.mk _ ⟨X, hX⟩ : ModuliSpace.{u} g)} := by
  classical
  let F : ℕ → (S ≃ₜ X.carrier) := fun n => (T (n : ℤ)).trans f₀
  have hF : ∀ n, IsQCRS (F n) := fun n => s28q_isQCRS_trans (hT _) hf₀
  let q : ℕ → TeichSpace S := fun n => Quot.mk _ (⟨X, F n, hF n⟩ : MarkedRS S)
  let B : Set (TeichSpace S) :=
    {p | LiesOver p (Quot.mk _ ⟨X, hX⟩ : ModuliSpace.{u} g)}
  have hq : ∀ n, q n ∈ B := fun n => ⟨⟨X, F n, hF n⟩, hX, rfl, rfl⟩
  change ¬ B.Finite
  intro hB
  letI : Finite B := hB.to_subtype
  let Q : ℕ → B := fun n => ⟨q n, hq n⟩
  -- First pigeonhole: infinitely many indices have the same marked point.
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber Q
  let A : Set ℕ := Q ⁻¹' {b}
  have hA : A.Infinite := Set.infinite_coe_iff.1 hb
  obtain ⟨n₀, hn₀⟩ := hA.nonempty
  have hsame : ∀ n : A, q n.1 = q n₀ := by
    intro n
    have hn : Q n.1 = b := Set.mem_singleton_iff.1 n.2
    have h0 : Q n₀ = b := Set.mem_singleton_iff.1 hn₀
    exact congrArg Subtype.val (hn.trans h0.symm)
  -- Quotient equality yields an actual conformal automorphism, not a direct
  -- homotopy between the two markings.
  have hauto : ∀ n : A, ∃ c : X.carrier ≃ₜ X.carrier, IsBiholomorphic c ∧
      ContinuousMap.Homotopic
        (((F n.1).trans c : S ≃ₜ X.carrier) : C(S, X.carrier))
        (F n₀ : C(S, X.carrier)) := by
    intro n
    exact s28q_equiv_of_mk_eq (hsame n)
  choose c hc hhom using hauto
  let Aut : Set (X.carrier ≃ₜ X.carrier) := {φ | IsBiholomorphic φ}
  letI : Finite Aut := (hurwitz_finite hg hX).to_subtype
  letI : Infinite A := hA.to_subtype
  let C : A → Aut := fun n => ⟨c n, hc n⟩
  -- Second pigeonhole: two distinct indices have the very same correction.
  obtain ⟨n, m, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite C
  have hcm : c n = c m := congrArg Subtype.val heq
  have hm := hhom m
  rw [← hcm] at hm
  have hpair := (hhom n).trans hm.symm
  let e : S ≃ₜ X.carrier := f₀.trans (c n)
  have hcancel : ∀ k : ℕ, (e.symm : C(X.carrier, S)).comp
      (((F k).trans (c n) : S ≃ₜ X.carrier) : C(S, X.carrier)) =
        (T (k : ℤ) : C(S, S)) := by
    intro k
    ext x
    simp [e, F]
  have hcancelled :=
    (ContinuousMap.Homotopic.refl (e.symm : C(X.carrier, S))).comp hpair
  have htwist : ContinuousMap.Homotopic
      (T (n.1 : ℤ) : C(S, S)) (T (m.1 : ℤ) : C(S, S)) := by
    simpa only [hcancel] using hcancelled
  apply hne
  apply Subtype.ext
  exact Int.ofNat_inj.mp (hsep _ _ htwist)

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- Every point over the fixed moduli representative `[X]` has a QC marking into
this very same X. Equality in the moduli quotient yields a biholomorphic map
from its representative to X; transport the marking and use Quot.sound.
This does not infer a homotopy from equality of same-surface marked points. -/
theorem s28m_fibre_fixed_target [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g : ℕ} (X : ClosedRS.{u}) (hX : HasGenus X.carrier g) {q : TeichSpace S₀}
    (hq : LiesOver q (Quot.mk _ ⟨X, hX⟩ : ModuliSpace.{u} g)) :
    ∃ (f : S₀ ≃ₜ X.carrier) (hf : IsQCRS f),
      q = Quot.mk _ (⟨X, f, hf⟩ : MarkedRS S₀) := by
  obtain ⟨m, hm, hqm, hrm⟩ := hq
  have hconf : RSConformallyEquivalent m.X.carrier X.carrier :=
    utm_y_rsce_of_eq (X := ⟨m.X, hm⟩) (Y := ⟨X, hX⟩) hrm.symm
  obtain ⟨c, hc⟩ := utm_y_homeo_of_rsce hconf
  have hcq : IsQCRS c := ⟨1, (isKQCRS_one_iff c).2 hc⟩
  have hf : IsQCRS (m.marking.trans c) := s28q_isQCRS_trans m.qc hcq
  refine ⟨m.marking.trans c, hf, hqm.trans ?_⟩
  exact Quot.sound ⟨c, hc, ContinuousMap.Homotopic.refl _⟩

/-- The points represented by K-QC markings into one fixed closed genus-g
surface form a finite set. An infinite set supplies an injective sequence of
marked points; KL yields a homotopic pair of their chosen markings, and the
valid forward implication of markedRS_equiv_same_surface identifies the points.
No finite automorphism correction or false converse is needed in this direction. -/
theorem s28m_bounded_fibre_finite [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (X : ClosedRS.{u}) (hX : HasGenus X.carrier g) (K : ℝ) :
    Set.Finite {q : TeichSpace S₀ |
      ∃ (f : S₀ ≃ₜ X.carrier) (hf : IsKQCRS f K),
        q = Quot.mk _ (⟨X, f, ⟨K, hf⟩⟩ : MarkedRS S₀)} := by
  classical
  letI : CompactSpace S₀ := hS.1
  let A : Set (TeichSpace S₀) := {q |
    ∃ (f : S₀ ≃ₜ X.carrier) (hf : IsKQCRS f K),
      q = Quot.mk _ (⟨X, f, ⟨K, hf⟩⟩ : MarkedRS S₀)}
  change A.Finite
  by_contra hA
  let e := Set.Infinite.natEmbedding A hA
  have hex : ∀ n : ℕ, ∃ (f : S₀ ≃ₜ X.carrier) (hf : IsKQCRS f K),
      (e n).1 = Quot.mk _ (⟨X, f, ⟨K, hf⟩⟩ : MarkedRS S₀) := fun n => (e n).2
  choose f hf hq using hex
  obtain ⟨Γ₀, p₀, _hFuchsian₀, _hFree₀, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  obtain ⟨ΓX, pX, _hFuchsianX, _hFreeX, hpX⟩ :=
    s22hg_exists_fuchsian_uniformization (S := X.carrier) hg hX
  obtain ⟨n, m, hne, hhom⟩ := utm_y_kl hp₀ hpX f hf
  apply hne
  apply e.injective
  apply Subtype.ext
  rw [hq n, hq m]
  exact Quot.sound
    (markedRS_equiv_same_surface X (f n) (f m) ⟨K, hf n⟩ ⟨K, hf m⟩ hg hX hhom)

/-- The full fibre over `[X]` is countable. First transport each marking into
the fixed target X. Its finite QC constant is bounded by a natural number;
the finite sets in s28m_bounded_fibre_finite therefore cover the fibre through
a countable union. The selected QC bound is allowed to depend on the point. -/
theorem s28m_fibre_countable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (X : ClosedRS.{u}) (hX : HasGenus X.carrier g) :
    Set.Countable {q : TeichSpace S₀ |
      LiesOver q (Quot.mk _ ⟨X, hX⟩ : ModuliSpace.{u} g)} := by
  classical
  let A : ℕ → Set (TeichSpace S₀) := fun n => {q |
    ∃ (f : S₀ ≃ₜ X.carrier) (hf : IsKQCRS f (n : ℝ)),
      q = Quot.mk _ (⟨X, f, ⟨(n : ℝ), hf⟩⟩ : MarkedRS S₀)}
  have hA : ∀ n, (A n).Countable := fun n =>
    (s28m_bounded_fibre_finite hg hS X hX (n : ℝ)).countable
  refine (Set.countable_iUnion hA).mono ?_
  intro q hq
  obtain ⟨f, hf, rfl⟩ := s28m_fibre_fixed_target X hX hq
  obtain ⟨n, hn⟩ := exists_nat_ge (max 1 (maxDilatationRS f).toReal)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := (le_max_left _ _).trans hn
  have hnd : (maxDilatationRS f).toReal ≤ (n : ℝ) := (le_max_right _ _).trans hn
  -- QC rules out the totalized infinity-toReal branch before using this identity.
  have hD : maxDilatationRS f ≤ ENNReal.ofReal (n : ℝ) := by
    calc
      maxDilatationRS f = ENNReal.ofReal (maxDilatationRS f).toReal :=
        (ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hf)).symm
      _ ≤ ENNReal.ofReal (n : ℝ) := ENNReal.ofReal_le_ofReal hnd
  have hfn : IsKQCRS f (n : ℝ) := s29_m_isKQCRS_of_le hf hn1 hD
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  exact ⟨f, hfn, rfl⟩

/-- Surjectivity of the forgetful relation, using precisely the user's
classification premise. On a quotient representative X, hcl supplies a
preserving marking and exists_qc_in_homotopy_class supplies a QC marking.
This helper also holds in genera zero and one; it does not need hg. -/
theorem s28m_liesOver_surjective [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {g : ℕ} (hS : HasGenus S₀ g)
    (hcl : ∀ X : ClosedRS.{u}, HasGenus X.carrier g →
      ∃ f : S₀ ≃ₜ X.carrier, IsOrientationPreservingRS f) :
    ∀ r : ModuliSpace.{u} g, ∃ q : TeichSpace S₀, LiesOver q r := by
  intro r
  refine Quot.inductionOn r ?_
  intro z
  obtain ⟨f, hf⟩ := hcl z.1 z.2
  obtain ⟨f₀, hqc, _hhom⟩ := exists_qc_in_homotopy_class hS z.2 f hf
  refine ⟨Quot.mk _ (⟨z.1, f₀, hqc⟩ : MarkedRS S₀), ?_⟩
  exact ⟨⟨z.1, f₀, hqc⟩, z.2, rfl, rfl⟩

/-- §28.1: the map `T(S₀) → R_g` is well defined and surjective; every `[S] ∈ R_g` corresponds to
infinitely (countably) many points `[S, f] ∈ T(S₀)`, `f` running through the homotopy classes of
homeomorphisms `S₀ → S`.

**Statement change (2026-10-13, user decision).**  The hypothesis `hcl` was added: every closed surface of
genus `g` is orientation-preservingly homeomorphic to `S₀`.  This is the topological classification of
closed surfaces, which the book uses and which is not formalized (`HasGenus` gives only
`π₁ ≅ surfaceGroup g`). -/
theorem liesOver_wellDefined_surjective [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g)
    (hcl : ∀ X : ClosedRS.{u}, HasGenus X.carrier g → ∃ f : S₀ ≃ₜ X.carrier, IsOrientationPreservingRS f) :
    (∀ (p : TeichSpace S₀) (r r' : ModuliSpace.{u} g), LiesOver p r → LiesOver p r' → r = r') ∧
      (∀ r : ModuliSpace.{u} g, ∃ p : TeichSpace S₀, LiesOver p r) ∧
      ∀ r : ModuliSpace.{u} g, (Set.Infinite {p : TeichSpace S₀ | LiesOver p r} ∧
        Set.Countable {p : TeichSpace S₀ | LiesOver p r}) := by
  refine ⟨?_, s28m_liesOver_surjective hS hcl, ?_⟩
  · intro p r r' hr hr'
    exact s28q_liesOver_wellDefined hr hr'
  · intro r
    refine Quot.inductionOn r ?_
    intro z
    obtain ⟨f, hf⟩ := hcl z.1 z.2
    obtain ⟨f₀, hqc, _hhom⟩ := exists_qc_in_homotopy_class hS z.2 f hf
    obtain ⟨T, _hzero, _hadd, hT, hsep⟩ := s28m_dehn_twist_family hg hS
    -- This assembly depends on the still-unproved, Root-frozen M2 family.
    -- It is a development draft, not an axiom-clean book proof delivery.
    exact ⟨s28m_infinite_fibre_of_twist hg z.1 z.2 f₀ hqc T hT hsep,
      s28m_fibre_countable hg hS z.1 z.2⟩

end LiZhongQC
