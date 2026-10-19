import LiZhongQC.Lemmas.FinitePunctureCompactification

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC

universe u

/-- The trace at a puncture is nontrivial even when other deleted components
have interior. Only their closedness and avoidance of this puncture are used. -/
theorem s31fu_puncture_trace_neBot {A X : Type*}
    [TopologicalSpace X] [T1Space X] [ChartedSpace ℂ X]
    (i : A → X) (P : Finset X) {K : Set X} (hK : IsClosed K)
    (hr : range i = ((↑P : Set X) ∪ K)ᶜ) {p : X} (hpK : p ∉ K) :
    NeBot (comap i (𝓝 p)) := by
  let k : ↥((↑P : Set X)ᶜ) → X := Subtype.val
  have hk : range k = (↑P : Set X)ᶜ := Subtype.range_coe
  have hfinite : ((range k)ᶜ).Finite := by
    rw [hk, compl_compl]
    exact P.finite_toSet
  have hd : DenseRange k := s31cg_denseRange k hfinite
  let di : IsDenseInducing k := ⟨Topology.IsInducing.subtypeVal, hd⟩
  have hne := di.comap_nhds_neBot p
  apply comap_neBot_iff.2
  intro U hU
  obtain ⟨x, hx⟩ := comap_neBot_iff.1 hne (U ∩ Kᶜ)
    (inter_mem hU (hK.isOpen_compl.mem_nhds hpK))
  have hxr : x.val ∈ range i := by
    rw [hr]
    exact fun h => h.elim x.property hx.2
  obtain ⟨a, ha⟩ := hxr
  exact ⟨a, ha.symm ▸ hx.1⟩

/-- Two actual endpoint limits compose through the shared embedded space.
The nontrivial trace is essential: a bottom filter cannot identify an end. -/
theorem s31fu_endpoint_inverse {A X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (i : A → X) (j : A → Y) {x x' : X} {y : Y}
    [NeBot (comap i (𝓝 x))]
    (hxy : Tendsto j (comap i (𝓝 x)) (𝓝 y))
    (hyx : Tendsto i (comap j (𝓝 y)) (𝓝 x')) : x = x' := by
  have hle : comap i (𝓝 x) ≤ comap j (𝓝 y) :=
    (map_le_iff_le_comap).1 hxy
  have hback : Tendsto i (comap i (𝓝 x)) (𝓝 x') :=
    hyx.mono_left hle
  have hself : Tendsto i (comap i (𝓝 x)) (𝓝 x) := map_comap_le
  exact tendsto_nhds_unique hself hback

/-- Choosing actual limits in both directions constructs an equivalence of
the designated finite end sets. No bijection or inverse law is assumed. -/
theorem s31fu_endpoint_equiv {A X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    (i : A → X) (j : A → Y) (P : Finset X) (Q : Finset Y)
    (hi : ∀ x ∈ P, NeBot (comap i (𝓝 x)))
    (hj : ∀ y ∈ Q, NeBot (comap j (𝓝 y)))
    (hij : ∀ x ∈ P, ∃ y ∈ Q, Tendsto j (comap i (𝓝 x)) (𝓝 y))
    (hji : ∀ y ∈ Q, ∃ x ∈ P, Tendsto i (comap j (𝓝 y)) (𝓝 x)) :
    Nonempty (P ≃ Q) ∧ P.card = Q.card := by
  classical
  have hforward : ∀ x : P, ∃ y : Q, Tendsto j (comap i (𝓝 x.val)) (𝓝 y.val) := by
    intro x
    obtain ⟨y, hy, ht⟩ := hij x.val x.property
    exact ⟨⟨y, hy⟩, ht⟩
  have hbackward : ∀ y : Q, ∃ x : P, Tendsto i (comap j (𝓝 y.val)) (𝓝 x.val) := by
    intro y
    obtain ⟨x, hx, ht⟩ := hji y.val y.property
    exact ⟨⟨x, hx⟩, ht⟩
  choose f hf using hforward
  choose g hg using hbackward
  have hgf : Function.LeftInverse g f := by
    intro x
    letI : NeBot (comap i (𝓝 x.val)) := hi x.val x.property
    apply Subtype.ext
    exact (s31fu_endpoint_inverse i j (hf x) (hg (f x))).symm
  have hfg : Function.RightInverse g f := by
    intro y
    letI : NeBot (comap j (𝓝 y.val)) := hj y.val y.property
    apply Subtype.ext
    exact (s31fu_endpoint_inverse j i (hg y) (hf (g y))).symm
  let e : P ≃ Q :=
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg }
  refine ⟨⟨e⟩, ?_⟩
  simpa using Fintype.card_congr e

/-- Genus and the total number of omitted points are intrinsic for arbitrary
topological finite-point embeddings into the two given closed surfaces.
The embeddings produced by shrinking holes need not be holomorphic. -/
theorem s31fu_finite_complement_comparison {S : Type*} [TopologicalSpace S]
    {X Y : ClosedRS.{u}} {g g' : ℕ} (hX : HasGenus X.carrier g)
    (hY : HasGenus Y.carrier g')
    (i : S → X.carrier) (j : S → Y.carrier)
    (hi : Topology.IsEmbedding i) (hj : Topology.IsEmbedding j)
    (hfi : ((range i)ᶜ).Finite) (hfj : ((range j)ᶜ).Finite) :
    g = g' ∧ ((range i)ᶜ).ncard = ((range j)ᶜ).ncard := by
  obtain ⟨H, hH, _⟩ := s31fe_extend_finite_missing i j hi hj
    (s31cg_denseRange i hfi) (s31cg_denseRange j hfj) hfi hfj
    (s31cg_connected_traces i hi hfi) (s31cg_connected_traces j hj hfj)
  exact ⟨closed_surface_genus_unique (hasGenus_of_homeomorph hX H) hY,
    (s31fe_missing_equiv i j H hH).2⟩

end LiZhongQC

