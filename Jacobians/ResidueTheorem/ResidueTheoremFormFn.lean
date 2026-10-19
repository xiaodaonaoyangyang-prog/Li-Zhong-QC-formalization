/-
  THE 1-FORM RESIDUE THEOREM, ALL GENERA: `∑ a ∈ poles, Res_a(ω₀·g) = 0`.

  `ω₀` is a global holomorphic 1-form and `g` a meromorphic function on the compact Riemann
  surface `X`; the residue is the canonical-chart `formFnResidue` of `FormCoeff.lean`.  This is
  the `formFnResidue`-shaped headline consumed by the period-lattice development
  (`Jacobians/PeriodLattice/PeriodLatticeDiscrete.lean`).

  Proof = reduction to the planar-Stokes pair-form residue theorem
  `StokesResidue.residueSum_pairForm_eq_zero_unconditional`
  (`Jacobians/ResidueTheorem/ResidueTheoremStokes.lean`) — the REVERSE of the classical
  ω₀-factorization (Miranda Ch. VI pp. 186–188):

  1. `ω₀ = 0`: every integrand has the `coeffAt 0 = 0` factor, so each residue vanishes.
  2. `ω₀ ≠ 0`: pick a nonconstant meromorphic `g₀` (`exists_nonconstant_meromorphicFunction`)
     and set `q := dg₀/ω₀` (`derivQuotientFn`).  The KEY LEMMA
     (`derivQuotientFn_orderW_ne_top`) says `q` is nowhere germ-zero: were its chart read
     eventually `0` near some point, `dg₀`'s would be too (the `coeffAt ω₀` factor has isolated
     zeros), so `dg₀ = 0` everywhere by the form identity theorem
     (`MeromorphicOneForm.formOrderW_ne_top_of_exists`), making `g₀` germ-constant
     (`differentialForm_ne_zero`) — contradiction.
  3. Apply the pair theorem to `(g₀, h := g·q⁻¹)` over the pole set enlarged by the finite
     `¬ReadsAnalyticAt` locus; convert each term by the bridge
     `pairFormResidue_eq_formFnResidue` (`Res_a(h·dg₀) = Res_a((h·q)·ω₀)`) and repair the germ
     `(g·q⁻¹·q).toFun = g.toFun` off the (eventually avoided) zeros of `q`.
  4. The enlargement terms vanish by `formFnResidue_eq_zero_of_analyticAt` + `hpoles`.

  Everything here is complete and depends on no unproved lemma.
-/
import Jacobians.ResidueTheorem.ResidueTheoremStokes
import Jacobians.CanonicalForms.CanonicalFormDifferential
import Jacobians.Meromorphic.MeromorphicInverse

open scoped Manifold ContDiff Topology
open Filter


namespace Jacobians.Dolbeault

open Jacobians Jacobians.Dolbeault.StokesResidue

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **KEY LEMMA: the quotient `q = dg₀/ω₀` of a nonconstant `g₀` by a nonzero `ω₀` is nowhere
germ-zero** (`orderW ≠ ⊤` at every point).  If the chart read of `q` were eventually `0` near
some `a`, then — since `q`'s read agrees off the centre with `(g₀∘chart⁻¹)′ / coeffAt ω₀ a`
(`derivQuotient_eventuallyEq_chart`) and `coeffAt ω₀ a` is eventually nonzero (isolated zeros,
`ω₀ ≠ 0`) — the derivative `(g₀∘chart⁻¹)′` would vanish on a punctured neighbourhood, i.e.
`formOrderW (dg₀) a = ⊤`; the form identity theorem
(`MeromorphicOneForm.formOrderW_ne_top_of_exists`) then contradicts `dg₀ ≠ 0`
(`differentialForm_ne_zero`, from `¬ IsGermConstant g₀`). -/
theorem derivQuotientFn_orderW_ne_top (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0)
    {g₀ : MeromorphicFunction X} (hg₀ : ¬ IsGermConstant g₀) (a : X) :
    (derivQuotientFn ω₀ g₀).orderW a ≠ ⊤ := by
  intro htop
  -- the chart read of `q` is eventually `0` off the centre
  have hq0 : ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
      derivQuotient ω₀ g₀ ((chartAt (H := ℂ) a).symm z) = 0 := by
    have h := meromorphicOrderAt_eq_top_iff.mp htop
    simpa [Function.comp_def] using h
  -- hence `(g₀∘chart⁻¹)′` is eventually `0` (the `coeffAt` factor is eventually nonzero)
  have hderiv0 : ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
      deriv (g₀.toFun ∘ (chartAt (H := ℂ) a).symm) z = 0 := by
    filter_upwards [hq0, derivQuotient_eventuallyEq_chart ω₀ g₀ a,
      coeffAt_eventually_ne_zero ω₀ hω₀ a] with z hz hcoh hC
    rw [hcoh] at hz
    simpa [Function.comp_def] using (div_eq_zero_iff.mp hz).resolve_right hC
  -- so `dg₀` has germ-order `⊤` at `a` — contradicting the form identity theorem
  have hd : (differentialForm g₀).formOrderW a = ⊤ := by
    rw [formOrderW_differentialForm, meromorphicOrderAt_eq_top_iff]
    exact hderiv0
  exact MeromorphicOneForm.formOrderW_ne_top_of_exists (differentialForm g₀)
    (differentialForm_ne_zero hg₀) a hd

/-- **THE 1-FORM RESIDUE THEOREM, ALL GENERA** (Forster GTM 81, 10.21): for a global holomorphic
1-form `ω₀` and a meromorphic `g` on the compact Riemann surface `X`, the total residue over any
finite set containing the poles vanishes,

  `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`,

provided `g`'s chart read is honestly `AnalyticAt` at every chart centre off `poles`.
NO genus hypothesis: reduction to the planar-Stokes pair-form theorem
`residueSum_pairForm_eq_zero_unconditional` via the reverse ω₀-factorization `ω₀·g = h·dg₀`,
`h := g·(dg₀/ω₀)⁻¹`, for a nonconstant `g₀` (`derivQuotientFn_orderW_ne_top` supplies the
eventual nonvanishing that repairs the germ `g·q⁻¹·q = g`). -/
theorem residueTheorem_formFn_unconditional [Nonempty X]
    (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X) (poles : Finset X)
    (hpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 := by
  classical
  rcases eq_or_ne ω₀ 0 with rfl | hω₀
  -- `ω₀ = 0`: every integrand carries the `coeffAt 0 = 0` factor
  · refine Finset.sum_eq_zero fun a _ => ?_
    have hcoeff : ∀ z : ℂ, coeffAt (0 : HolomorphicOneForms X) a z = 0 := fun z => rfl
    have hint : (fun z => coeffAt (0 : HolomorphicOneForms X) a z
        * g.toFun ((chartAt ℂ a).symm z)) = fun _ => (0 : ℂ) :=
      funext fun z => by rw [hcoeff z, zero_mul]
    show resAt _ _ = 0
    rw [hint]
    exact resAt_eq_zero_of_analyticAt analyticAt_const
  -- `ω₀ ≠ 0`: reverse ω₀-factorization through the pair-form Stokes engine
  · obtain ⟨g₀, hg₀⟩ := exists_nonconstant_meromorphicFunction (X := X)
    set q : MeromorphicFunction X := derivQuotientFn ω₀ g₀ with hq_def
    set h : MeromorphicFunction X := g * q⁻¹ with hh_def
    set poles' : Finset X := poles ∪ (finite_not_readsAnalyticAt g₀ h).toFinset with hp'_def
    have hsub : poles ⊆ poles' := Finset.subset_union_left
    -- the pair-form engine over the enlarged pole set
    have hzero : ∑ a ∈ poles', pairFormResidue g₀ h a = 0 := by
      refine residueSum_pairForm_eq_zero_unconditional g₀ h poles' fun x hx => ?_
      have hgood : ReadsAnalyticAt g₀ h x := by
        by_contra hbad
        exact hx (Finset.mem_union_right _
          ((finite_not_readsAnalyticAt g₀ h).mem_toFinset.mpr hbad))
      exact analyticAt_pairRead hgood (mem_chart_source ℂ x)
    -- term-by-term conversion: bridge to `(h·q)·ω₀`, then repair the germ `g·q⁻¹·q = g`
    have hloc : ∀ a : X, pairFormResidue g₀ h a = formFnResidue ω₀ g.toFun a := by
      intro a
      rw [pairFormResidue_eq_formFnResidue ω₀ hω₀ g₀ h a, ← hq_def]
      refine resAt_congr ?_
      have hne_top : meromorphicOrderAt (q.toFun ∘ (chartAt (H := ℂ) a).symm)
          ((chartAt (H := ℂ) a) a) ≠ ⊤ :=
        derivQuotientFn_orderW_ne_top ω₀ hω₀ hg₀ a
      have hqne : ∀ᶠ z in 𝓝[≠] ((chartAt (H := ℂ) a) a),
          q.toFun ((chartAt (H := ℂ) a).symm z) ≠ 0 := by
        have h := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
          (q.meromorphic a)).mp hne_top
        simpa [Function.comp_def] using h
      filter_upwards [hqne] with z hz
      simp only [hh_def, MeromorphicFunction.mul_toFun, Pi.mul_apply,
        MeromorphicFunction.inv_toFun, Pi.inv_apply]
      rw [inv_mul_cancel_right₀ hz]
    -- pole-set bookkeeping: the enlargement terms vanish off `poles`
    rw [Finset.sum_congr rfl fun a _ => hloc a, ← Finset.sum_sdiff hsub] at hzero
    have hextra : ∑ a ∈ poles' \ poles, formFnResidue ω₀ g.toFun a = 0 :=
      Finset.sum_eq_zero fun a ha =>
        formFnResidue_eq_zero_of_analyticAt ω₀ g.toFun a (hpoles a (Finset.mem_sdiff.mp ha).2)
    rw [hextra, zero_add] at hzero
    exact hzero

end Jacobians.Dolbeault
