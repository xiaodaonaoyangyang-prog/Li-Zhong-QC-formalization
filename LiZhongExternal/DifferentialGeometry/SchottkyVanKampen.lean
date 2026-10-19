/- Derived from https://github.com/qinz1yang/differential-geometry (commit fd2f07fba4c6c102ba626c59153ad98da8f0d442),
   Apache License 2.0. Modified for LiZhongQC: selected source, imports renamed, local repairs.
   See NOTICE.DifferentialGeometry and LICENSE.Apache-2.0 in this directory. -/
-- Repository: https://github.com/qinz1yang/differential-geometry
-- Commit: fd2f07fba4c6c102ba626c59153ad98da8f0d442
-- BEGIN LICENSE
--                                  Apache License
--                            Version 2.0, January 2004
--                         http://www.apache.org/licenses/
-- 
--    TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION
-- 
--    1. Definitions.
-- 
--       "License" shall mean the terms and conditions for use, reproduction,
--       and distribution as defined by Sections 1 through 9 of this document.
-- 
--       "Licensor" shall mean the copyright owner or entity authorized by
--       the copyright owner that is granting the License.
-- 
--       "Legal Entity" shall mean the union of the acting entity and all
--       other entities that control, are controlled by, or are under common
--       control with that entity. For the purposes of this definition,
--       "control" means (i) the power, direct or indirect, to cause the
--       direction or management of such entity, whether by contract or
--       otherwise, or (ii) ownership of fifty percent (50%) or more of the
--       outstanding shares, or (iii) beneficial ownership of such entity.
-- 
--       "You" (or "Your") shall mean an individual or Legal Entity
--       exercising permissions granted by this License.
-- 
--       "Source" form shall mean the preferred form for making modifications,
--       including but not limited to software source code, documentation
--       source, and configuration files.
-- 
--       "Object" form shall mean any form resulting from mechanical
--       transformation or translation of a Source form, including but
--       not limited to compiled object code, generated documentation,
--       and conversions to other media types.
-- 
--       "Work" shall mean the work of authorship, whether in Source or
--       Object form, made available under the License, as indicated by a
--       copyright notice that is included in or attached to the work
--       (an example is provided in the Appendix below).
-- 
--       "Derivative Works" shall mean any work, whether in Source or Object
--       form, that is based on (or derived from) the Work and for which the
--       editorial revisions, annotations, elaborations, or other modifications
--       represent, as a whole, an original work of authorship. For the purposes
--       of this License, Derivative Works shall not include works that remain
--       separable from, or merely link (or bind by name) to the interfaces of,
--       the Work and Derivative Works thereof.
-- 
--       "Contribution" shall mean any work of authorship, including
--       the original version of the Work and any modifications or additions
--       to that Work or Derivative Works thereof, that is intentionally
--       submitted to Licensor for inclusion in the Work by the copyright owner
--       or by an individual or Legal Entity authorized to submit on behalf of
--       the copyright owner. For the purposes of this definition, "submitted"
--       means any form of electronic, verbal, or written communication sent
--       to the Licensor or its representatives, including but not limited to
--       communication on electronic mailing lists, source code control systems,
--       and issue tracking systems that are managed by, or on behalf of, the
--       Licensor for the purpose of discussing and improving the Work, but
--       excluding communication that is conspicuously marked or otherwise
--       designated in writing by the copyright owner as "Not a Contribution."
-- 
--       "Contributor" shall mean Licensor and any individual or Legal Entity
--       on behalf of whom a Contribution has been received by Licensor and
--       subsequently incorporated within the Work.
-- 
--    2. Grant of Copyright License. Subject to the terms and conditions of
--       this License, each Contributor hereby grants to You a perpetual,
--       worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--       copyright license to reproduce, prepare Derivative Works of,
--       publicly display, publicly perform, sublicense, and distribute the
--       Work and such Derivative Works in Source or Object form.
-- 
--    3. Grant of Patent License. Subject to the terms and conditions of
--       this License, each Contributor hereby grants to You a perpetual,
--       worldwide, non-exclusive, no-charge, royalty-free, irrevocable
--       (except as stated in this section) patent license to make, have made,
--       use, offer to sell, sell, import, and otherwise transfer the Work,
--       where such license applies only to those patent claims licensable
--       by such Contributor that are necessarily infringed by their
--       Contribution(s) alone or by combination of their Contribution(s)
--       with the Work to which such Contribution(s) was submitted. If You
--       institute patent litigation against any entity (including a
--       cross-claim or counterclaim in a lawsuit) alleging that the Work
--       or a Contribution incorporated within the Work constitutes direct
--       or contributory patent infringement, then any patent licenses
--       granted to You under this License for that Work shall terminate
--       as of the date such litigation is filed.
-- 
--    4. Redistribution. You may reproduce and distribute copies of the
--       Work or Derivative Works thereof in any medium, with or without
--       modifications, and in Source or Object form, provided that You
--       meet the following conditions:
-- 
--       (a) You must give any other recipients of the Work or
--           Derivative Works a copy of this License; and
-- 
--       (b) You must cause any modified files to carry prominent notices
--           stating that You changed the files; and
-- 
--       (c) You must retain, in the Source form of any Derivative Works
--           that You distribute, all copyright, patent, trademark, and
--           attribution notices from the Source form of the Work,
--           excluding those notices that do not pertain to any part of
--           the Derivative Works; and
-- 
--       (d) If the Work includes a "NOTICE" text file as part of its
--           distribution, then any Derivative Works that You distribute must
--           include a readable copy of the attribution notices contained
--           within such NOTICE file, excluding those notices that do not
--           pertain to any part of the Derivative Works, in at least one
--           of the following places: within a NOTICE text file distributed
--           as part of the Derivative Works; within the Source form or
--           documentation, if provided along with the Derivative Works; or,
--           within a display generated by the Derivative Works, if and
--           wherever such third-party notices normally appear. The contents
--           of the NOTICE file are for informational purposes only and
--           do not modify the License. You may add Your own attribution
--           notices within Derivative Works that You distribute, alongside
--           or as an addendum to the NOTICE text from the Work, provided
--           that such additional attribution notices cannot be construed
--           as modifying the License.
-- 
--       You may add Your own copyright statement to Your modifications and
--       may provide additional or different license terms and conditions
--       for use, reproduction, or distribution of Your modifications, or
--       for any such Derivative Works as a whole, provided Your use,
--       reproduction, and distribution of the Work otherwise complies with
--       the conditions stated in this License.
-- 
--    5. Submission of Contributions. Unless You explicitly state otherwise,
--       any Contribution intentionally submitted for inclusion in the Work
--       by You to the Licensor shall be under the terms and conditions of
--       this License, without any additional terms or conditions.
--       Notwithstanding the above, nothing herein shall supersede or modify
--       the terms of any separate license agreement you may have executed
--       with Licensor regarding such Contributions.
-- 
--    6. Trademarks. This License does not grant permission to use the trade
--       names, trademarks, service marks, or product names of the Licensor,
--       except as required for reasonable and customary use in describing the
--       origin of the Work and reproducing the content of the NOTICE file.
-- 
--    7. Disclaimer of Warranty. Unless required by applicable law or
--       agreed to in writing, Licensor provides the Work (and each
--       Contributor provides its Contributions) on an "AS IS" BASIS,
--       WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
--       implied, including, without limitation, any warranties or conditions
--       of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
--       PARTICULAR PURPOSE. You are solely responsible for determining the
--       appropriateness of using or redistributing the Work and assume any
--       risks associated with Your exercise of permissions under this License.
-- 
--    8. Limitation of Liability. In no event and under no legal theory,
--       whether in tort (including negligence), contract, or otherwise,
--       unless required by applicable law (such as deliberate and grossly
--       negligent acts) or agreed to in writing, shall any Contributor be
--       liable to You for damages, including any direct, indirect, special,
--       incidental, or consequential damages of any character arising as a
--       result of this License or out of the use or inability to use the
--       Work (including but not limited to damages for loss of goodwill,
--       work stoppage, computer failure or malfunction, or any and all
--       other commercial damages or losses), even if such Contributor
--       has been advised of the possibility of such damages.
-- 
--    9. Accepting Warranty or Additional Liability. While redistributing
--       the Work or Derivative Works thereof, You may choose to offer,
--       and charge a fee for, acceptance of support, warranty, indemnity,
--       or other liability obligations and/or rights consistent with this
--       License. However, in accepting such obligations, You may act only
--       on Your own behalf and on Your sole responsibility, not on behalf
--       of any other Contributor, and only if You agree to indemnify,
--       defend, and hold each Contributor harmless for any liability
--       incurred by, or claims asserted against, such Contributor by reason
--       of your accepting any such warranty or additional liability.
-- 
--    END OF TERMS AND CONDITIONS
-- 
--    APPENDIX: How to apply the Apache License to your work.
-- 
--       To apply the Apache License to your work, attach the following
--       boilerplate notice, with the fields enclosed by brackets "[]"
--       replaced with your own identifying information. (Don't include
--       the brackets!)  The text should be enclosed in the appropriate
--       comment syntax for the file format. We also recommend that a
--       file or class name and description of purpose be included on the
--       same "printed page" as the copyright notice for easier
--       identification within third-party archives.
-- 
--    Copyright [yyyy] [name of copyright owner]
-- 
--    Licensed under the Apache License, Version 2.0 (the "License");
--    you may not use this file except in compliance with the License.
--    You may obtain a copy of the License at
-- 
--        http://www.apache.org/licenses/LICENSE-2.0
-- 
--    Unless required by applicable law or agreed to in writing, software
--    distributed under the License is distributed on an "AS IS" BASIS,
--    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
--    See the License for the specific language governing permissions and
--    limitations under the License.
-- END LICENSE
-- BEGIN NOTICE
-- DifferentialGeometry
-- Copyright 2026 The DifferentialGeometry contributors
-- 
-- The files under DifferentialGeometry/External/Schoenflies derive from
-- https://github.com/alonamaloh/schoenflies-lean
-- Copyright (c) 2026 Álvaro Begué. All rights reserved.
-- Released under the Apache License 2.0.
-- See that directory's LICENSE, MODIFICATIONS.md and provenance records.
-- 
-- The selected source under DifferentialGeometry/External/TauCeti derives from
-- https://github.com/TauCetiProject/TauCeti
-- revision 3358033ba2fd35f321356dceaf2372a0fd6c0bfd.
-- Copyright (c) 2026 Joseph Tooby-Smith and The Tau Ceti contributors.
-- Authors include Joseph Tooby-Smith, Codex and The Tau Ceti contributors,
-- as recorded in the preserved original source headers.
-- Released under the Apache License 2.0.
-- See that directory's LICENSE, SOURCE_MAP.json and MODIFICATIONS.md.
-- Native Sard, Morse, embedding and extension modules consume this external API.
-- 
-- The source under DifferentialGeometry/External/CanonicalTopology is restored
-- from the canonical-topology/Poincare project by Ayush Khaitan and its
-- contributors. See its pinned source archives, SOURCE_MAP.json, LICENSE
-- and MODIFICATIONS.md for exact revisions and declaration-level adaptations.
-- The derivative homotopy includes adapted source from plby/HopfProblem,
-- Solution.lean at 9ac8a456b526527837d7082ff775213ca8bc9809, lines 62156–62228,
-- under Apache-2.0; the nested attribution and license are preserved.
-- 
-- The source under DifferentialGeometry/External/ClassificationOfSurfaces
-- derives from https://github.com/mccorvie/classification-of-surfaces.
-- It includes work by the ClassificationOfSurfaces contributors, Steven Sivek
-- and Kai Lam, as recorded in the original source and nested provenance.
-- Released under the Apache License 2.0. See its LICENSE and MODIFICATIONS.md.
-- END NOTICE

/-
Mechanically bundled from qinz1yang/differential-geometry.
Pinned commit: fd2f07fba4c6c102ba626c59153ad98da8f0d442.
Original copyright headers, namespaces, declarations and proofs follow verbatim.
Only imports are hoisted/deduplicated and file-local sections are added.
See LICENSE, NOTICE, INPUT_MANIFEST.json and LINE_MAP.tsv.
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.GroupTheory.PushoutI
import Mathlib.Topology.Subpath
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Homotopy.Product
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Groupoid.Subgroupoid
import Mathlib.Topology.Connected.PathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Category.ULift

-- BEGIN SOURCE: DifferentialGeometry/Topology/Algebra/Group/AmalgamatedProduct.lean
section svkBundle_001
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

universe u v w

namespace DifferentialGeometry.Algebra.Group

theorem pushoutI_existsUnique_lift {ι : Type u} [Nonempty ι]
    (G : ι → Type v) (H : Type w) [∀ i, Group (G i)] [Group H]
    (φ : ∀ i, H →* G i) {K : Type*} [Group K]
    (f : ∀ i, G i →* K) (k : H →* K) (hf : ∀ i, (f i).comp (φ i) = k) :
    ∃! F : Monoid.PushoutI φ →* K,
      ∀ i, F.comp (Monoid.PushoutI.of i) = f i := by
  refine ⟨Monoid.PushoutI.lift f k hf, ?_, ?_⟩
  · intro i
    ext g
    simp
  · intro F hF
    apply Monoid.PushoutI.hom_ext_nonempty
    intro i
    rw [hF i]
    ext g
    simp

theorem pushoutI_subsingleton_of_factors {ι : Type u} [Nonempty ι]
    (G : ι → Type v) (H : Type w) [∀ i, Group (G i)] [Group H]
    (φ : ∀ i, H →* G i) [∀ i, Subsingleton (G i)] :
    Subsingleton (Monoid.PushoutI φ) := by
  constructor
  intro x y
  suffices htrivial : ∀ z : Monoid.PushoutI φ, z = 1 by
    exact (htrivial x).trans (htrivial y).symm
  intro z
  induction z using Monoid.PushoutI.induction_on with
  | of i g =>
      rw [Subsingleton.elim g 1, map_one]
  | base h =>
      let i : ι := Classical.choice inferInstance
      rw [← Monoid.PushoutI.of_apply_eq_base φ i h]
      rw [Subsingleton.elim (φ i h) 1, map_one]
  | mul a b ha hb =>
      rw [ha, hb, mul_one]

namespace PushoutIdentities

abbrev factor : Bool → Type
  | false => PUnit
  | true => Multiplicative ℤ

instance factorGroup (i : Bool) : Group (factor i) := by
  cases i <;> simp only [factor] <;> infer_instance

def diagram : ∀ i : Bool, Multiplicative ℤ →* factor i
  | false => 1
  | true => MonoidHom.id _

theorem of_true_eq_one (h : Multiplicative ℤ) :
    Monoid.PushoutI.of true h = (1 : Monoid.PushoutI diagram) := by
  calc
    Monoid.PushoutI.of true h = Monoid.PushoutI.base diagram h := by
      simpa [diagram] using Monoid.PushoutI.of_apply_eq_base diagram true h
    _ = Monoid.PushoutI.of false (1 : PUnit) := by
      simpa [diagram] using (Monoid.PushoutI.of_apply_eq_base diagram false h).symm
    _ = 1 := map_one _

theorem of_true_not_injective :
    ¬ Function.Injective
      (Monoid.PushoutI.of (φ := diagram) true :
        Multiplicative ℤ →* Monoid.PushoutI diagram) := by
  intro hinj
  have hEq : Multiplicative.ofAdd (1 : ℤ) = 1 := hinj <| by
    rw [of_true_eq_one]
    exact (map_one _).symm
  have hEq' := congrArg Multiplicative.toAdd hEq
  change (1 : ℤ) = 0 at hEq'
  exact one_ne_zero hEq'

end PushoutIdentities

end DifferentialGeometry.Algebra.Group
end svkBundle_001
-- END SOURCE: DifferentialGeometry/Topology/Algebra/Group/AmalgamatedProduct.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/Subdivision.lean
section svkBundle_002
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open Set unitInterval
open scoped unitInterval

universe u

namespace DifferentialGeometry.Topology.VanKampen

noncomputable def standardTime (n : ℕ) (i : Fin (n + 1)) : I :=
  ⟨(i : ℝ) / (n : ℝ), unitInterval.div_mem (by positivity) (by positivity) (by
    exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩

@[simp]
theorem standardTime_zero (n : ℕ) : standardTime n 0 = 0 := by
  ext
  simp [standardTime]

@[simp]
theorem standardTime_last {n : ℕ} (hn : 0 < n) : standardTime n (Fin.last n) = 1 := by
  ext
  simp [standardTime, Nat.ne_of_gt hn]

theorem standardTime_castSucc_le_succ {n : ℕ} (hn : 0 < n) (i : Fin n) :
    standardTime n i.castSucc ≤ standardTime n i.succ := by
  rw [← Subtype.coe_le_coe]
  simp only [standardTime, Subtype.coe_mk]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (by positivity)

theorem standardTime_succ_sub_castSucc {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (standardTime n i.succ : ℝ) - standardTime n i.castSucc = 1 / (n : ℝ) := by
  simp only [standardTime, Subtype.coe_mk, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
    Nat.cast_one]
  field_simp [Nat.ne_of_gt hn]
  ring

noncomputable def standardSubpath {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n : ℕ} (i : Fin n) :
    Path (p (standardTime n i.castSucc)) (p (standardTime n i.succ)) :=
  p.subpath (standardTime n i.castSucc) (standardTime n i.succ)

def refinedIndex {n k : ℕ} (i : Fin n) (r : Fin k) : Fin (n * k) :=
  ⟨i * k + r, (Nat.add_lt_add_left r.isLt (i * k)).trans_le (by
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr i.isLt))⟩

@[simp]
theorem refinedIndex_val {n k : ℕ} (i : Fin n) (r : Fin k) :
    (refinedIndex i r : ℕ) = i * k + r :=
  rfl

def refinedVertex {n k : ℕ} (i : Fin n) (r : Fin (k + 1)) : Fin (n * k + 1) :=
  ⟨i * k + r, by
    apply Nat.lt_succ_of_le
    calc
      i * k + r ≤ i * k + k := Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) _
      _ = (i + 1) * k := by rw [Nat.add_mul, one_mul]
      _ ≤ n * k := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr i.isLt)⟩

@[simp]
theorem refinedVertex_val {n k : ℕ} (i : Fin n) (r : Fin (k + 1)) :
    (refinedVertex i r : ℕ) = i * k + r :=
  rfl

theorem standardSubpath_refinedVertex {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : Fin n) (r : Fin (k + 1)) :
    standardSubpath p i (standardTime k r) =
      p (standardTime (n * k) (refinedVertex i r)) := by
  apply congrArg p
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb, standardTime, refinedVertex_val, Fin.val_castSucc,
    Fin.val_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp [Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  ring

def firstHalfIndex {n : ℕ} (_hn : 0 < n) (i : Fin n) : Fin (2 * n) :=
  ⟨i, by omega⟩

def secondHalfIndex {n : ℕ} (_hn : 0 < n) (i : Fin n) : Fin (2 * n) :=
  ⟨n + i, by omega⟩

def firstHalfVertex {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) : Fin (2 * n + 1) :=
  ⟨i, by omega⟩

def secondHalfVertex {n : ℕ} (i : Fin (n + 1)) : Fin (2 * n + 1) :=
  ⟨n + i, by omega⟩

theorem trans_standardTime_first {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin (n + 1)) :
    (p.trans q) (standardTime (2 * n) (firstHalfVertex hn i)) =
      p (standardTime n i) := by
  let t := standardTime (2 * n) (firstHalfVertex hn i)
  have ht : (t : ℝ) ≤ 1 / 2 := by
    dsimp only [t]
    simp only [standardTime, firstHalfVertex, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    have hi : (i : ℝ) ≤ n := by
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    linarith
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_le_half p q ht]
  have harg : 2 * (t : ℝ) = (standardTime n i : ℝ) := by
    dsimp only [t]
    simp only [standardTime, firstHalfVertex, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
  rw [harg, Path.extend_apply]

theorem trans_standardTime_second {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin (n + 1)) :
    (p.trans q) (standardTime (2 * n) (secondHalfVertex i)) =
      q (standardTime n i) := by
  let t := standardTime (2 * n) (secondHalfVertex i)
  have ht : 1 / 2 ≤ (t : ℝ) := by
    dsimp only [t]
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    simp only [standardTime, secondHalfVertex, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    linarith
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_half_le p q ht]
  have harg : 2 * (t : ℝ) - 1 = (standardTime n i : ℝ) := by
    dsimp only [t]
    simp only [standardTime, secondHalfVertex, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    ring
  rw [harg, Path.extend_apply]

theorem standardSubpath_trans_first_apply {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin n) (s : I) :
    standardSubpath (p.trans q) (firstHalfIndex hn i) s = standardSubpath p i s := by
  let t := Set.Icc.convexComb
    (standardTime (2 * n) (firstHalfIndex hn i).castSucc)
    (standardTime (2 * n) (firstHalfIndex hn i).succ) s
  have ht : (t : ℝ) ≤ 1 / 2 := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    simp only [standardTime, firstHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    have hi : (i : ℝ) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_iff.mpr i.isLt
    ring_nf
    nlinarith
  change (p.trans q) t = p (Set.Icc.convexComb
    (standardTime n i.castSucc) (standardTime n i.succ) s)
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_le_half p q ht]
  have harg : 2 * (t : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc)
        (standardTime n i.succ) s : ℝ) := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb, Set.Icc.coe_convexComb]
    simp only [standardTime, firstHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
  rw [harg, Path.extend_apply]

theorem standardSubpath_trans_second_apply {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin n) (s : I) :
    standardSubpath (p.trans q) (secondHalfIndex hn i) s = standardSubpath q i s := by
  let t := Set.Icc.convexComb
    (standardTime (2 * n) (secondHalfIndex hn i).castSucc)
    (standardTime (2 * n) (secondHalfIndex hn i).succ) s
  have ht : 1 / 2 ≤ (t : ℝ) := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    simp only [standardTime, secondHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    ring_nf
    nlinarith
  change (p.trans q) t = q (Set.Icc.convexComb
    (standardTime n i.castSucc) (standardTime n i.succ) s)
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_half_le p q ht]
  have harg : 2 * (t : ℝ) - 1 =
      (Set.Icc.convexComb (standardTime n i.castSucc)
        (standardTime n i.succ) s : ℝ) := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb, Set.Icc.coe_convexComb]
    simp only [standardTime, secondHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    ring
  rw [harg, Path.extend_apply]

theorem standardSubpath_refined_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (i : Fin n) (r : Fin k) (s : I) :
    standardSubpath p (refinedIndex i r) s = standardSubpath (standardSubpath p i) r s := by
  change p (Set.Icc.convexComb
      (standardTime (n * k) (refinedIndex i r).castSucc)
      (standardTime (n * k) (refinedIndex i r).succ) s) =
    p (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ)
      (Set.Icc.convexComb (standardTime k r.castSucc) (standardTime k r.succ) s))
  apply congrArg p
  apply Subtype.ext
  simp only [standardTime, Set.Icc.coe_convexComb, refinedIndex_val, Fin.val_castSucc,
    Fin.val_succ, Nat.cast_add, Nat.cast_mul]
  field_simp [Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  ring

theorem range_standardSubpath_refined_subset {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (i : Fin n) (r : Fin k) :
    Set.range (standardSubpath p (refinedIndex i r)) ⊆ Set.range (standardSubpath p i) := by
  rintro _ ⟨s, rfl⟩
  refine ⟨Set.Icc.convexComb (standardTime k r.castSucc) (standardTime k r.succ) s, ?_⟩
  exact (standardSubpath_refined_apply p hn hk i r s).symm

noncomputable def standardConcat {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n : ℕ} (hn : 0 < n) : Path a b :=
  (Path.concat (p ∘ standardTime n) (standardSubpath p)).cast
    (by simp) (by simp [standardTime_last hn])

theorem standardConcat_quotient_eq {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n : ℕ} (hn : 0 < n) :
    Path.Homotopic.Quotient.mk (standardConcat p hn) = Path.Homotopic.Quotient.mk p := by
  rw [Path.Homotopic.Quotient.eq]
  let hx : a = p (standardTime n 0) := by simp
  let hy : b = p (standardTime n (Fin.last n)) := by simp [standardTime_last hn]
  have h := Path.Homotopic.concat_subpath p (standardTime n)
  have hcast :
      ((Path.concat (p ∘ standardTime n) (standardSubpath p)).cast hx hy).Homotopic
        ((p.subpath (standardTime n 0) (standardTime n (Fin.last n))).cast hx hy) :=
    h.pathCast hx hy
  have hright :
      (p.subpath (standardTime n 0) (standardTime n (Fin.last n))).cast hx hy = p := by
    ext s
    simp [Path.subpath, standardTime_last hn]
  rw [hright] at hcast
  simpa only [standardConcat] using hcast

theorem standardSubpath_quotient_eq_refinement {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    Path.Homotopic.Quotient.mk (standardSubpath p i) =
      Path.Homotopic.Quotient.mk (standardConcat (standardSubpath p i) hk) :=
  (standardConcat_quotient_eq (standardSubpath p i) hk).symm

section Regression

example {X : Type u} [TopologicalSpace X] {a b : X} (p : Path a b) :
    Path.Homotopic.Quotient.mk (standardConcat p Nat.zero_lt_one) =
      Path.Homotopic.Quotient.mk p :=
  standardConcat_quotient_eq p Nat.zero_lt_one

end Regression

end DifferentialGeometry.Topology.VanKampen
end svkBundle_002
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/Subdivision.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/CoveredPath.lean
section svkBundle_003
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open Metric Set unitInterval
open scoped unitInterval

universe u

namespace DifferentialGeometry.Topology.VanKampen

namespace Path

def IsCovered {X : Type u} [TopologicalSpace X] {a b : X} (p : _root_.Path a b)
    (U V : Set X) (n : ℕ) : Prop :=
  ∀ i : Fin n, range (standardSubpath p i) ⊆ U ∨ range (standardSubpath p i) ⊆ V

theorem dist_standardTime_le {n : ℕ} (hn : 0 < n) (i : Fin n) (t : I)
    (ht : t ∈ Icc (standardTime n i.castSucc) (standardTime n i.succ)) :
    dist (standardTime n i.castSucc) t ≤ 1 / (n : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos, neg_sub]
  · calc
      (t : ℝ) - standardTime n i.castSucc ≤
          standardTime n i.succ - standardTime n i.castSucc := by
        exact sub_le_sub_right (by exact_mod_cast ht.2) _
      _ = 1 / (n : ℝ) := standardTime_succ_sub_castSucc hn i
  · exact sub_nonpos.mpr (by exact_mod_cast ht.1)

theorem exists_isCovered {X : Type u} [TopologicalSpace X] {a b : X} (p : _root_.Path a b)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    ∃ n : ℕ, 0 < n ∧ IsCovered p U V n := by
  let c : Bool → Set I := fun side ↦ p ⁻¹' if side then U else V
  have hc_open : ∀ side, IsOpen (c side) := by
    intro side
    cases side <;> simp [c, hU, hV, p.continuous.isOpen_preimage]
  have hc_cover : (univ : Set I) ⊆ ⋃ side, c side := by
    intro t _
    have ht : p t ∈ U ∪ V := by rw [hcover]; trivial
    rcases ht with htU | htV
    · exact mem_iUnion.mpr ⟨true, by simpa [c] using htU⟩
    · exact mem_iUnion.mpr ⟨false, by simpa [c] using htV⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := (univ : Set I)) isCompact_univ hc_open hc_cover
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hm
  refine ⟨n, hn, ?_⟩
  intro i
  obtain ⟨side, hside⟩ := hball (standardTime n i.castSucc) (mem_univ _)
  have hinterval : Icc (standardTime n i.castSucc) (standardTime n i.succ) ⊆ c side := by
    intro t ht
    apply hside
    rw [mem_ball]
    simpa [dist_comm] using (dist_standardTime_le hn i t ht).trans_lt hmesh
  have hrange : range (standardSubpath p i) ⊆ if side then U else V := by
    rw [standardSubpath, _root_.Path.range_subpath_of_le _ _ _
      (standardTime_castSucc_le_succ hn i)]
    rintro _ ⟨t, ht, rfl⟩
    exact hinterval ht
  cases side
  · exact Or.inr hrange
  · exact Or.inl hrange

theorem IsCovered.mul {X : Type u} [TopologicalSpace X] {a b : X} {p : _root_.Path a b}
    {U V : Set X} {n k : ℕ} (h : IsCovered p U V n) (hn : 0 < n) (hk : 0 < k) :
    IsCovered p U V (n * k) := by
  intro j
  let i : Fin n := ⟨j / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
  let r : Fin k := ⟨j % k, Nat.mod_lt j hk⟩
  have hj : refinedIndex i r = j := by
    apply Fin.ext
    simpa [refinedIndex, i, r, Nat.mul_comm] using Nat.div_add_mod j k
  rw [← hj]
  rcases h i with hiU | hiV
  · exact Or.inl ((range_standardSubpath_refined_subset p hn hk i r).trans hiU)
  · exact Or.inr ((range_standardSubpath_refined_subset p hn hk i r).trans hiV)

end Path

end DifferentialGeometry.Topology.VanKampen
end svkBundle_003
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/CoveredPath.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/Evaluation.lean
section svkBundle_004
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory Set

universe u v

namespace DifferentialGeometry.Topology.VanKampen

def interToLeft {X : Type u} [TopologicalSpace X] (U V : Set X) : C(↥(U ∩ V), ↥U) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def interToRight {X : Type u} [TopologicalSpace X] (U V : Set X) : C(↥(U ∩ V), ↥V) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

structure LocalFunctorData {X : Type u} [TopologicalSpace X] (U V : Set X)
    (G : Type v) [Groupoid G] where
  left : FundamentalGroupoid U ⥤ G
  right : FundamentalGroupoid V ⥤ G
  compatibility :
    FundamentalGroupoid.map (interToLeft U V) ⋙ left =
      FundamentalGroupoid.map (interToRight U V) ⋙ right

namespace LocalFunctorData

variable {X : Type u} [TopologicalSpace X] {U V : Set X}
  {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)

noncomputable def gluedObj (hcover : U ∪ V = univ) (x : X) : G := by
  classical
  by_cases hx : x ∈ U
  · exact F.left.obj ⟨⟨x, hx⟩⟩
  · have hxV : x ∈ V := by
      have : x ∈ U ∪ V := by rw [hcover]; trivial
      exact this.resolve_left hx
    exact F.right.obj ⟨⟨x, hxV⟩⟩

theorem gluedObj_eq_left (hcover : U ∪ V = univ) {x : X} (hx : x ∈ U) :
    F.gluedObj hcover x = F.left.obj ⟨⟨x, hx⟩⟩ := by
  classical
  simp [gluedObj, hx]

theorem gluedObj_eq_right (hcover : U ∪ V = univ) {x : X} (hx : x ∈ V) :
    F.gluedObj hcover x = F.right.obj ⟨⟨x, hx⟩⟩ := by
  classical
  by_cases hxU : x ∈ U
  · let z : FundamentalGroupoid (↥(U ∩ V)) := ⟨⟨x, hxU, hx⟩⟩
    have h := Functor.congr_obj F.compatibility z
    simp only [gluedObj, hxU, ↓reduceDIte]
    convert h using 1
    · apply congrArg F.left.obj
      ext
      rfl
    · apply congrArg F.right.obj
      ext
      rfl
  · simp [gluedObj, hxU]

def normalizeHom {a a' b b' : G} (ha : a = a') (hb : b = b') (f : a' ⟶ b') : a ⟶ b :=
  eqToHom ha ≫ f ≫ eqToHom hb.symm

@[simp]
theorem normalizeHom_id {a a' : G} (ha : a = a') :
    normalizeHom ha ha (𝟙 a') = 𝟙 a := by
  subst ha
  simp [normalizeHom]

theorem normalizeHom_comp {a a' b b' c c' : G}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (f : a' ⟶ b') (g : b' ⟶ c') :
    normalizeHom ha hc (f ≫ g) = normalizeHom ha hb f ≫ normalizeHom hb hc g := by
  subst ha
  subst hb
  subst hc
  simp [normalizeHom]

theorem normalizeHom_heq {a a' b b' : G} (ha : a = a') (hb : b = b')
    (f : a' ⟶ b') : normalizeHom ha hb f ≍ f :=
  (CategoryTheory.conj_eqToHom_iff_heq _ _ ha hb).1 rfl

theorem normalizeHom_normalizeHom {a a' a'' b b' b'' : G}
    (ha : a = a') (ha' : a' = a'') (hb : b = b') (hb' : b' = b'')
    (f : a'' ⟶ b'') :
    normalizeHom ha hb (normalizeHom ha' hb' f) =
      normalizeHom (ha.trans ha') (hb.trans hb') f := by
  subst a'
  subst a''
  subst b'
  subst b''
  simp [normalizeHom]

theorem normalizeHom_eq_of_heq {a a' a'' b b' b'' : G}
    (ha' : a = a') (ha'' : a = a'') (hb' : b = b') (hb'' : b = b'')
    (f : a' ⟶ b') (g : a'' ⟶ b'') (hfg : f ≍ g) :
    normalizeHom ha' hb' f = normalizeHom ha'' hb'' g := by
  subst a'
  subst a''
  subst b'
  subst b''
  cases hfg
  simp [normalizeHom]

noncomputable def normalizedChain {n : ℕ} (obj localObj : Fin (n + 1) → G)
    (hObj : ∀ i, obj i = localObj i)
    (mapSucc : ∀ i : Fin n, localObj i.castSucc ⟶ localObj i.succ) :
    ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc obj
    (fun i => normalizeHom (hObj i.castSucc) (hObj i.succ) (mapSucc i))

noncomputable def normalizedChainOf {n : ℕ} (obj : Fin (n + 1) → G)
    (L : ComposableArrows G n) (hObj : ∀ i, obj i = L.obj i) : ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc obj
    (fun i => normalizeHom (hObj i.castSucc) (hObj i.succ) (L.map' i (i + 1)))

set_option backward.isDefEq.respectTransparency false in
theorem normalizedChainOf_hom {n : ℕ} (obj : Fin (n + 1) → G)
    (L : ComposableArrows G n) (hObj : ∀ i, obj i = L.obj i) :
    (normalizedChainOf obj L hObj).hom =
      normalizeHom (hObj 0) (hObj (Fin.last n)) L.hom := by
  let N := normalizedChainOf obj L hObj
  let α : N ⟶ L := ComposableArrows.homMk
    (fun i => eqToHom (hObj i)) (by
      intro i hi
      dsimp only [N, normalizedChainOf]
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
      simp [normalizeHom])
  have hnat := ComposableArrows.naturality' α 0 n (Nat.zero_le n) le_rfl
  change N.hom ≫ eqToHom (hObj (Fin.last n)) = eqToHom (hObj 0) ≫ L.hom at hnat
  change N.hom = normalizeHom (hObj 0) (hObj (Fin.last n)) L.hom
  apply (cancel_mono (eqToHom (hObj (Fin.last n)))).1
  rw [hnat]
  simp [normalizeHom]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedChain_hom {n : ℕ} (obj localObj : Fin (n + 1) → G)
    (hObj : ∀ i, obj i = localObj i)
    (mapSucc : ∀ i : Fin n, localObj i.castSucc ⟶ localObj i.succ) :
    (normalizedChain obj localObj hObj mapSucc).hom =
      normalizeHom (hObj 0) (hObj (Fin.last n))
        (ComposableArrows.mkOfObjOfMapSucc localObj mapSucc).hom := by
  let N := normalizedChain obj localObj hObj mapSucc
  let L := ComposableArrows.mkOfObjOfMapSucc localObj mapSucc
  let α : N ⟶ L := ComposableArrows.homMk
    (fun i => eqToHom (hObj i)) (by
      intro i hi
      dsimp only [N, L, normalizedChain]
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
        ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
      simp [normalizeHom])
  have hnat := ComposableArrows.naturality' α 0 n (Nat.zero_le n) le_rfl
  change N.hom ≫ eqToHom (hObj (Fin.last n)) = eqToHom (hObj 0) ≫ L.hom at hnat
  change N.hom = normalizeHom (hObj 0) (hObj (Fin.last n)) L.hom
  apply (cancel_mono (eqToHom (hObj (Fin.last n)))).1
  rw [hnat]
  simp [normalizeHom]

end LocalFunctorData

def pathIn {X : Type u} [TopologicalSpace X] {x y : X} (A : Set X)
    (p : _root_.Path x y) (hp : range p ⊆ A) :
    _root_.Path (⟨x, hp ⟨0, p.source⟩⟩ : A) (⟨y, hp ⟨1, p.target⟩⟩ : A) where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

theorem range_standardSubpath_subset {X : Type u} [TopologicalSpace X] {x y : X}
    {A : Set X} (p : _root_.Path x y) (hp : range p ⊆ A) {n : ℕ} (i : Fin n) :
    range (standardSubpath p i) ⊆ A := by
  rintro z ⟨t, rfl⟩
  exact hp ⟨Set.Icc.convexComb (standardTime n i.castSucc)
    (standardTime n i.succ) t, rfl⟩

theorem pathIn_standardSubpath {X : Type u} [TopologicalSpace X] {x y : X}
    {A : Set X} (p : _root_.Path x y) (hp : range p ⊆ A) {n : ℕ} (i : Fin n) :
    pathIn A (standardSubpath p i) (range_standardSubpath_subset p hp i) =
      standardSubpath (pathIn A p hp) i := by
  apply _root_.Path.ext
  rfl

theorem pathIn_map_interToLeft {X : Type u} [TopologicalSpace X] {x y : X}
    {U V : Set X} (p : _root_.Path x y) (hUV : range p ⊆ U ∩ V)
    (hU : range p ⊆ U) :
    (Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hUV)).map (interToLeft U V) =
      Path.Homotopic.Quotient.mk (pathIn U p hU) := by
  apply congrArg Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  rfl

theorem pathIn_map_interToRight {X : Type u} [TopologicalSpace X] {x y : X}
    {U V : Set X} (p : _root_.Path x y) (hUV : range p ⊆ U ∩ V)
    (hV : range p ⊆ V) :
    (Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hUV)).map (interToRight U V) =
      Path.Homotopic.Quotient.mk (pathIn V p hV) := by
  apply congrArg Path.Homotopic.Quotient.mk
  apply _root_.Path.ext
  rfl

noncomputable def standardPathChain {X : Type u} [TopologicalSpace X] {x y : X}
    (p : _root_.Path x y) (n : ℕ) : ComposableArrows (FundamentalGroupoid X) n where
  obj i := ⟨p (standardTime n i)⟩
  map {i j} _ := Path.Homotopic.Quotient.mk
    (p.subpath (standardTime n i) (standardTime n j))
  map_id i := by
    change Path.Homotopic.Quotient.mk
      (p.subpath (standardTime n i) (standardTime n i)) =
        Path.Homotopic.Quotient.mk (_root_.Path.refl (p (standardTime n i)))
    rw [_root_.Path.subpath_self]
  map_comp f g := by
    change Path.Homotopic.Quotient.mk
      (p.subpath (standardTime n _) (standardTime n _)) =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk
            (p.subpath (standardTime n _) (standardTime n _)))
          (Path.Homotopic.Quotient.mk
            (p.subpath (standardTime n _) (standardTime n _)))
    rw [← Path.Homotopic.Quotient.mk_trans]
    exact Path.Homotopic.Quotient.eq.mpr
      ⟨(_root_.Path.Homotopy.subpathTransSubpath p _ _ _).symm⟩

theorem standardPathChain_hom_heq {X : Type u} [TopologicalSpace X] {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) :
    (standardPathChain p n).hom ≍ Path.Homotopic.Quotient.mk p := by
  change Path.Homotopic.Quotient.mk
    (p.subpath (standardTime n 0) (standardTime n (Fin.last n))) ≍
      Path.Homotopic.Quotient.mk p
  apply _root_.Path.Homotopic.hpath_hext
  intro t
  simp [_root_.Path.subpath, standardTime_last hn]

inductive CoverSide
  | left
  | right
  deriving DecidableEq

def CoverSide.set {X : Type u} (U V : Set X) : CoverSide → Set X
  | .left => U
  | .right => V

def blockEndpointFunctor (n k : ℕ) : Fin (n + 1) ⥤ Fin (n * k + 1) where
  obj i := ⟨i * k, Nat.lt_succ_of_le
    (Nat.mul_le_mul_right k (Nat.le_of_lt_succ i.isLt))⟩
  map {i j} hij := homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Nat.mul_le_mul_right k (Fin.mk_le_mk.mp (leOfHom hij)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def refinedBlockFunctor {n k : ℕ} (i : Fin n) : Fin (k + 1) ⥤ Fin (n * k + 1) where
  obj r := refinedVertex i r
  map {r s} hrs := homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Nat.add_le_add_left (Fin.mk_le_mk.mp (leOfHom hrs)) (i * k))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def firstHalfVertexFunctor {n : ℕ} (hn : 0 < n) : Fin (n + 1) ⥤ Fin (2 * n + 1) where
  obj i := firstHalfVertex hn i
  map {i j} hij := homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Fin.mk_le_mk.mp (leOfHom hij))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def secondHalfVertexFunctor (n : ℕ) : Fin (n + 1) ⥤ Fin (2 * n + 1) where
  obj i := secondHalfVertex i
  map {i j} hij := homOfLE (by
    apply Fin.mk_le_mk.mpr
    exact Nat.add_le_add_left (Fin.mk_le_mk.mp (leOfHom hij)) n)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem standardTime_blockEndpoint {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : Fin (n + 1)) :
    standardTime (n * k) ((blockEndpointFunctor n k).obj i) = standardTime n i := by
  apply Subtype.ext
  simp only [standardTime, blockEndpointFunctor, Nat.cast_mul]
  field_simp [Nat.ne_of_gt hn, Nat.ne_of_gt hk]

theorem refinedBlock_hom_heq_blockEndpoint_map {C : Type u} [Category.{v} C]
    {n k : ℕ} (R : ComposableArrows C (n * k)) (i : Fin n) :
    (R.whiskerLeft (refinedBlockFunctor i)).hom ≍
      (R.whiskerLeft (blockEndpointFunctor n k)).map'
        i (i + 1) (hjn := Nat.succ_le_iff.mpr i.isLt) := by
  let A := refinedBlockFunctor (k := k) i
  let B := blockEndpointFunctor n k
  let f : A.obj 0 ⟶ A.obj (Fin.last k) := A.map (homOfLE (Fin.zero_le _))
  let g : B.obj i.castSucc ⟶ B.obj i.succ :=
    B.map (homOfLE (Fin.mk_le_mk.mpr (Nat.le_succ i)))
  have h0 : A.obj 0 = B.obj i.castSucc := by
    apply Fin.ext
    simp [A, B, refinedBlockFunctor, refinedVertex, blockEndpointFunctor]
  have h1 : A.obj (Fin.last k) = B.obj i.succ := by
    apply Fin.ext
    simp [A, B, refinedBlockFunctor, refinedVertex, blockEndpointFunctor, Nat.add_mul]
  have hfg : f = eqToHom h0 ≫ g ≫ eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

theorem blockEndpoint_hom_heq {C : Type u} [Category.{v} C]
    {n k : ℕ} (R : ComposableArrows C (n * k)) :
    (R.whiskerLeft (blockEndpointFunctor n k)).hom ≍ R.hom := by
  let A := blockEndpointFunctor n k
  let f : A.obj 0 ⟶ A.obj (Fin.last n) := A.map (homOfLE (Fin.zero_le _))
  let g : (0 : Fin (n * k + 1)) ⟶ Fin.last (n * k) := homOfLE (Fin.zero_le _)
  have h0 : A.obj 0 = (0 : Fin (n * k + 1)) := by
    apply Fin.ext
    simp [A, blockEndpointFunctor]
  have h1 : A.obj (Fin.last n) = Fin.last (n * k) := by
    apply Fin.ext
    simp [A, blockEndpointFunctor]
  have hfg : f = eqToHom h0 ≫ g ≫ eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

theorem firstHalf_hom_heq_map_middle {C : Type u} [Category.{v} C]
    {n : ℕ} (hn : 0 < n) (R : ComposableArrows C (2 * n)) :
    (R.whiskerLeft (firstHalfVertexFunctor hn)).hom ≍
      R.map' 0 n (hjn := by omega) := by
  let A := firstHalfVertexFunctor hn
  let m : Fin (2 * n + 1) := ⟨n, by omega⟩
  let f : A.obj 0 ⟶ A.obj (Fin.last n) := A.map (homOfLE (Fin.zero_le _))
  let g : (0 : Fin (2 * n + 1)) ⟶ m := homOfLE (Fin.zero_le _)
  have h0 : A.obj 0 = (0 : Fin (2 * n + 1)) := by
    apply Fin.ext
    rfl
  have h1 : A.obj (Fin.last n) = m := by
    apply Fin.ext
    rfl
  have hfg : f = eqToHom h0 ≫ g ≫ eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

theorem secondHalf_hom_heq_map_middle {C : Type u} [Category.{v} C]
    {n : ℕ} (hn : 0 < n) (R : ComposableArrows C (2 * n)) :
    (R.whiskerLeft (secondHalfVertexFunctor n)).hom ≍
      R.map' n (2 * n) := by
  let A := secondHalfVertexFunctor n
  let m : Fin (2 * n + 1) := ⟨n, by omega⟩
  let f : A.obj 0 ⟶ A.obj (Fin.last n) := A.map (homOfLE (Fin.zero_le _))
  let g : m ⟶ Fin.last (2 * n) := homOfLE (by
    apply Fin.mk_le_mk.mpr
    omega)
  have h0 : A.obj 0 = m := by
    apply Fin.ext
    rfl
  have h1 : A.obj (Fin.last n) = Fin.last (2 * n) := by
    apply Fin.ext
    simp [A, secondHalfVertexFunctor, secondHalfVertex]
    omega
  have hfg : f = eqToHom h0 ≫ g ≫ eqToHom h1.symm := Subsingleton.elim _ _
  change R.map f ≍ R.map g
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg R.obj h0) (congrArg R.obj h1)).mp
  rw [hfg, R.map_comp, R.map_comp]
  simp only [CategoryTheory.eqToHom_map]

structure CoverAssignment {X : Type u} [TopologicalSpace X] {x y : X}
    (p : _root_.Path x y) (U V : Set X) (n : ℕ) where
  side : Fin n → CoverSide
  range_subset : ∀ i, range (standardSubpath p i) ⊆ (side i).set U V

theorem CoverAssignment.isCovered {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} {n : ℕ} (σ : CoverAssignment p U V n) :
    Path.IsCovered p U V n := by
  intro i
  cases h : σ.side i
  · exact Or.inl (by simpa [CoverSide.set, h] using σ.range_subset i)
  · exact Or.inr (by simpa [CoverSide.set, h] using σ.range_subset i)

noncomputable def CoverAssignment.ofIsCovered {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} {n : ℕ} (h : Path.IsCovered p U V n) :
    CoverAssignment p U V n := by
  classical
  refine ⟨fun i => if range (standardSubpath p i) ⊆ U then .left else .right, ?_⟩
  intro i
  by_cases hU : range (standardSubpath p i) ⊆ U
  · simp only [ite_eq_left hU, CoverSide.set]
    exact hU
  · simp only [ite_eq_right hU, CoverSide.set]
    exact (h i).resolve_left hU

def CoverAssignment.constant {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} (n : ℕ) (side : CoverSide)
    (hp : range p ⊆ side.set U V) : CoverAssignment p U V n where
  side _ := side
  range_subset i := range_standardSubpath_subset p hp i

def CoverAssignment.refine {X : Type u} [TopologicalSpace X] {x y : X}
    {p : _root_.Path x y} {U V : Set X} {n : ℕ} (σ : CoverAssignment p U V n)
    {k : ℕ} (hn : 0 < n) (hk : 0 < k) : CoverAssignment p U V (n * k) where
  side j := σ.side ⟨j / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
  range_subset j := by
    let i : Fin n := ⟨j / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
    let r : Fin k := ⟨j % k, Nat.mod_lt j hk⟩
    have hj : refinedIndex i r = j := by
      apply Fin.ext
      simpa [refinedIndex, i, r, Nat.mul_comm] using Nat.div_add_mod j k
    rw [← hj]
    have hidx :
        (⟨(refinedIndex i r : ℕ) / k,
          (Nat.div_lt_iff_lt_mul hk).mpr (refinedIndex i r).isLt⟩ : Fin n) = i := by
      apply Fin.ext
      change (i * k + r) / k = i
      rw [Nat.mul_comm]
      simpa [Nat.div_eq_of_lt r.isLt] using Nat.mul_add_div hk i r
    rw [hidx]
    exact (range_standardSubpath_refined_subset p hn hk i r).trans (σ.range_subset i)

def CoverAssignment.trans {X : Type u} [TopologicalSpace X] {x y z : X}
    {p : _root_.Path x y} {q : _root_.Path y z} {U V : Set X} {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    CoverAssignment (p.trans q) U V (2 * n) where
  side j := if hj : (j : ℕ) < n then σ.side ⟨j, hj⟩ else
    τ.side ⟨j - n, by omega⟩
  range_subset j := by
    split_ifs with hj
    · let i : Fin n := ⟨j, hj⟩
      have hji : firstHalfIndex hn i = j := by
        apply Fin.ext
        rfl
      rintro w ⟨s, rfl⟩
      have hpath : standardSubpath (p.trans q) j s = standardSubpath p i s := by
        rw [← hji]
        exact standardSubpath_trans_first_apply p q hn i s
      rw [hpath]
      exact σ.range_subset ⟨j, hj⟩ ⟨s, rfl⟩
    · let i : Fin n := ⟨j - n, by omega⟩
      rintro w ⟨s, rfl⟩
      have hji : secondHalfIndex hn i = j := by
        apply Fin.ext
        simp [secondHalfIndex, i]
        omega
      have hpath : standardSubpath (p.trans q) j s = standardSubpath q i s := by
        rw [← hji]
        exact standardSubpath_trans_second_apply p q hn i s
      rw [hpath]
      exact τ.range_subset i ⟨s, rfl⟩

namespace LocalFunctorData

variable {X : Type u} [TopologicalSpace X] {U V : Set X}
  {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)

noncomputable def leftPathMap (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ U) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  let px : x ∈ U := hp ⟨0, p.source⟩
  let py : y ∈ U := hp ⟨1, p.target⟩
  normalizeHom (F.gluedObj_eq_left hcover px) (F.gluedObj_eq_left hcover py)
    (F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hp)))

noncomputable def rightPathMap (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ V) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  let px : x ∈ V := hp ⟨0, p.source⟩
  let py : y ∈ V := hp ⟨1, p.target⟩
  normalizeHom (F.gluedObj_eq_right hcover px) (F.gluedObj_eq_right hcover py)
    (F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hp)))

theorem leftPathMap_refl (hcover : U ∪ V = univ) {x : X}
    (hp : range (_root_.Path.refl x) ⊆ U) :
    F.leftPathMap hcover (_root_.Path.refl x) hp = 𝟙 (F.gluedObj hcover x) := by
  let qx : U := ⟨x, hp ⟨0, rfl⟩⟩
  have hq : pathIn U (_root_.Path.refl x) hp = _root_.Path.refl qx := by
    apply _root_.Path.ext
    rfl
  unfold leftPathMap
  rw [hq]
  change normalizeHom _ _ (F.left.map (𝟙 _)) = _
  rw [F.left.map_id]
  apply normalizeHom_id

theorem rightPathMap_refl (hcover : U ∪ V = univ) {x : X}
    (hp : range (_root_.Path.refl x) ⊆ V) :
    F.rightPathMap hcover (_root_.Path.refl x) hp = 𝟙 (F.gluedObj hcover x) := by
  let qx : V := ⟨x, hp ⟨0, rfl⟩⟩
  have hq : pathIn V (_root_.Path.refl x) hp = _root_.Path.refl qx := by
    apply _root_.Path.ext
    rfl
  unfold rightPathMap
  rw [hq]
  change normalizeHom _ _ (F.right.map (𝟙 _)) = _
  rw [F.right.map_id]
  apply normalizeHom_id

noncomputable def leftPathChain {x y : X} (p : _root_.Path x y)
    (hp : range p ⊆ U) (n : ℕ) : ComposableArrows G n :=
  (F.left.mapComposableArrows n).obj (standardPathChain (pathIn U p hp) n)

noncomputable def rightPathChain {x y : X} (p : _root_.Path x y)
    (hp : range p ⊆ V) (n : ℕ) : ComposableArrows G n :=
  (F.right.mapComposableArrows n).obj (standardPathChain (pathIn V p hp) n)

theorem leftPathChain_hom_heq {x y : X} (p : _root_.Path x y)
    (hp : range p ⊆ U) {n : ℕ} (hn : 0 < n) :
    (F.leftPathChain p hp n).hom ≍
      F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hp)) := by
  let qx : U := ⟨x, hp ⟨0, p.source⟩⟩
  let qy : U := ⟨y, hp ⟨1, p.target⟩⟩
  let q : _root_.Path qx qy := pathIn U p hp
  have h0 : (standardPathChain q n).left = FundamentalGroupoid.mk qx := by
    apply FundamentalGroupoid.ext
    change q (standardTime n 0) = qx
    rw [standardTime_zero, q.source]
  have h1 : (standardPathChain q n).right = FundamentalGroupoid.mk qy := by
    apply FundamentalGroupoid.ext
    change q (standardTime n (Fin.last n)) = qy
    rw [standardTime_last hn, q.target]
  have hraw : (standardPathChain q n).hom =
      eqToHom h0 ≫ Path.Homotopic.Quotient.mk q ≫ eqToHom h1.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ h0 h1).2
      (standardPathChain_hom_heq q hn)
  change F.left.map (standardPathChain q n).hom ≍
    F.left.map (Path.Homotopic.Quotient.mk q)
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg F.left.obj h0) (congrArg F.left.obj h1)).mp
  rw [hraw, F.left.map_comp, F.left.map_comp]
  simp only [CategoryTheory.eqToHom_map]

theorem rightPathChain_hom_heq {x y : X} (p : _root_.Path x y)
    (hp : range p ⊆ V) {n : ℕ} (hn : 0 < n) :
    (F.rightPathChain p hp n).hom ≍
      F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hp)) := by
  let qx : V := ⟨x, hp ⟨0, p.source⟩⟩
  let qy : V := ⟨y, hp ⟨1, p.target⟩⟩
  let q : _root_.Path qx qy := pathIn V p hp
  have h0 : (standardPathChain q n).left = FundamentalGroupoid.mk qx := by
    apply FundamentalGroupoid.ext
    change q (standardTime n 0) = qx
    rw [standardTime_zero, q.source]
  have h1 : (standardPathChain q n).right = FundamentalGroupoid.mk qy := by
    apply FundamentalGroupoid.ext
    change q (standardTime n (Fin.last n)) = qy
    rw [standardTime_last hn, q.target]
  have hraw : (standardPathChain q n).hom =
      eqToHom h0 ≫ Path.Homotopic.Quotient.mk q ≫ eqToHom h1.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ h0 h1).2
      (standardPathChain_hom_heq q hn)
  change F.right.map (standardPathChain q n).hom ≍
    F.right.map (Path.Homotopic.Quotient.mk q)
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg F.right.obj h0) (congrArg F.right.obj h1)).mp
  rw [hraw, F.right.map_comp, F.right.map_comp]
  simp only [CategoryTheory.eqToHom_map]

theorem gluedObj_eq_leftPathChain_obj (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ U) (n : ℕ) (i : Fin (n + 1)) :
    F.gluedObj hcover (p (standardTime n i)) = (F.leftPathChain p hp n).obj i := by
  change F.gluedObj hcover (p (standardTime n i)) =
    F.left.obj ⟨(pathIn U p hp) (standardTime n i)⟩
  convert F.gluedObj_eq_left hcover (hp ⟨standardTime n i, rfl⟩) using 1
  apply congrArg F.left.obj
  ext
  rfl

theorem gluedObj_eq_rightPathChain_obj (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ V) (n : ℕ) (i : Fin (n + 1)) :
    F.gluedObj hcover (p (standardTime n i)) = (F.rightPathChain p hp n).obj i := by
  change F.gluedObj hcover (p (standardTime n i)) =
    F.right.obj ⟨(pathIn V p hp) (standardTime n i)⟩
  convert F.gluedObj_eq_right hcover (hp ⟨standardTime n i, rfl⟩) using 1
  apply congrArg F.right.obj
  ext
  rfl

noncomputable def leftNormalizedPathChain (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ U) (n : ℕ) : ComposableArrows G n :=
  normalizedChainOf (fun i => F.gluedObj hcover (p (standardTime n i)))
    (F.leftPathChain p hp n) (F.gluedObj_eq_leftPathChain_obj hcover p hp n)

noncomputable def rightNormalizedPathChain (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ V) (n : ℕ) : ComposableArrows G n :=
  normalizedChainOf (fun i => F.gluedObj hcover (p (standardTime n i)))
    (F.rightPathChain p hp n) (F.gluedObj_eq_rightPathChain_obj hcover p hp n)

theorem leftPathMap_eq_rightPathMap (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hpU : range p ⊆ U) (hpV : range p ⊆ V) :
    F.leftPathMap hcover p hpU = F.rightPathMap hcover p hpV := by
  let hpUV : range p ⊆ U ∩ V := fun z hz => ⟨hpU hz, hpV hz⟩
  let q := Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hpUV)
  have hcompat := Functor.hcongr_hom F.compatibility q
  dsimp only [Functor.comp_map] at hcompat
  change F.left.map (q.map (interToLeft U V)) ≍
    F.right.map (q.map (interToRight U V)) at hcompat
  dsimp only [q] at hcompat
  have hleft :
      F.left.map ((Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hpUV)).map
          (interToLeft U V)) ≍
        F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hpU)) := by
    rw [pathIn_map_interToLeft p hpUV hpU]
    apply HEq.rfl
  have hright :
      F.right.map ((Path.Homotopic.Quotient.mk (pathIn (U ∩ V) p hpUV)).map
          (interToRight U V)) ≍
        F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hpV)) := by
    rw [pathIn_map_interToRight p hpUV hpV]
    apply HEq.rfl
  have hcompat' := hleft.symm.trans (hcompat.trans hright)
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ hcompat'
  · apply F.gluedObj_eq_left
  · apply F.gluedObj_eq_right

noncomputable def sidePathMap (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (side : CoverSide)
    (hp : range p ⊆ side.set U V) : F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  match side with
  | .left => F.leftPathMap hcover p (by simpa [CoverSide.set] using hp)
  | .right => F.rightPathMap hcover p (by simpa [CoverSide.set] using hp)

theorem sidePathMap_eq (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (s t : CoverSide)
    (hs : range p ⊆ s.set U V) (ht : range p ⊆ t.set U V) :
    F.sidePathMap hcover p s hs = F.sidePathMap hcover p t ht := by
  cases s <;> cases t
  · rfl
  · apply F.leftPathMap_eq_rightPathMap
  · symm
    apply F.leftPathMap_eq_rightPathMap
  · rfl

theorem sidePathMap_heq_of_pointwise (hcover : U ∪ V = univ)
    {x y x' y' : X} (p : _root_.Path x y) (q : _root_.Path x' y')
    (s t : CoverSide) (hp : range p ⊆ s.set U V)
    (hq : range q ⊆ t.set U V) (h : ∀ z, p z = q z) :
    F.sidePathMap hcover p s hp ≍ F.sidePathMap hcover q t hq := by
  have hx : x = x' := p.source.symm.trans ((h 0).trans q.source)
  have hy : y = y' := p.target.symm.trans ((h 1).trans q.target)
  subst x'
  subst y'
  have hpq : p = q := by
    apply _root_.Path.ext
    funext z
    exact h z
  subst q
  exact heq_of_eq (F.sidePathMap_eq hcover p s t hp hq)

noncomputable def assignedSegment (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ : CoverAssignment p U V n) (i : Fin n) :
    F.gluedObj hcover (p (standardTime n i.castSucc)) ⟶
      F.gluedObj hcover (p (standardTime n i.succ)) :=
  F.sidePathMap hcover (standardSubpath p i) (σ.side i) (σ.range_subset i)

theorem assignedSegment_eq (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ τ : CoverAssignment p U V n) (i : Fin n) :
    F.assignedSegment hcover p σ i = F.assignedSegment hcover p τ i :=
  F.sidePathMap_eq hcover (standardSubpath p i) (σ.side i) (τ.side i)
    (σ.range_subset i) (τ.range_subset i)

noncomputable def assignedChain (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ : CoverAssignment p U V n) :
    ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i => F.gluedObj hcover (p (standardTime n i)))
    (fun i => F.assignedSegment hcover p σ i)

theorem assignedChain_map_succ (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ : CoverAssignment p U V n)
    (i : ℕ) (hi : i < n) :
    (F.assignedChain hcover p σ).map' i (i + 1) =
      F.assignedSegment hcover p σ ⟨i, hi⟩ := by
  apply ComposableArrows.mkOfObjOfMapSucc_map_succ

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_firstHalf_map_succ (hcover : U ∪ V = univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (τ : CoverAssignment (p.trans q) U V (2 * n))
    (r : ℕ) (hr : r < n) :
    ((F.assignedChain hcover (p.trans q) τ).whiskerLeft
      (firstHalfVertexFunctor hn)).map' r (r + 1) =
      F.assignedSegment hcover (p.trans q) τ (firstHalfIndex hn ⟨r, hr⟩) := by
  unfold assignedChain
  change (ComposableArrows.mkOfObjOfMapSucc
      (fun j => F.gluedObj hcover ((p.trans q) (standardTime (2 * n) j)))
      (fun j => F.assignedSegment hcover (p.trans q) τ j)).map' r (r + 1) = _
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ r (by omega)

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_secondHalf_map_succ (hcover : U ∪ V = univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (τ : CoverAssignment (p.trans q) U V (2 * n))
    (r : ℕ) (hr : r < n) :
    ((F.assignedChain hcover (p.trans q) τ).whiskerLeft
      (secondHalfVertexFunctor n)).map' r (r + 1) =
      F.assignedSegment hcover (p.trans q) τ (secondHalfIndex hn ⟨r, hr⟩) := by
  have hbound : n + r + 1 ≤ 2 * n := by omega
  unfold assignedChain
  change (ComposableArrows.mkOfObjOfMapSucc
      (fun j => F.gluedObj hcover ((p.trans q) (standardTime (2 * n) j)))
      (fun j => F.assignedSegment hcover (p.trans q) τ j)).map'
        (n + r) (n + r + 1) (hjn := hbound) = _
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (n + r)
    (secondHalfIndex hn ⟨r, hr⟩).isLt

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_eq_trans_first (hcover : U ∪ V = univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    F.assignedChain hcover p σ =
      (F.assignedChain hcover (p.trans q) (CoverAssignment.trans hn σ τ)).whiskerLeft
        (firstHalfVertexFunctor hn) := by
  let ξ := CoverAssignment.trans hn σ τ
  let hObj : ∀ i : Fin (n + 1),
      (F.assignedChain hcover p σ).obj i =
        ((F.assignedChain hcover (p.trans q) ξ).whiskerLeft
          (firstHalfVertexFunctor hn)).obj i := by
    intro i
    change F.gluedObj hcover (p (standardTime n i)) =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) (firstHalfVertex hn i)))
    exact congrArg (F.gluedObj hcover) (trans_standardTime_first p q hn i).symm
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover p σ r hr,
    F.assignedChain_firstHalf_map_succ hcover p q hn ξ r hr]
  unfold assignedSegment
  apply F.sidePathMap_heq_of_pointwise
  intro s
  exact (standardSubpath_trans_first_apply p q hn ⟨r, hr⟩ s).symm

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_eq_trans_second (hcover : U ∪ V = univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    F.assignedChain hcover q τ =
      (F.assignedChain hcover (p.trans q) (CoverAssignment.trans hn σ τ)).whiskerLeft
        (secondHalfVertexFunctor n) := by
  let ξ := CoverAssignment.trans hn σ τ
  let hObj : ∀ i : Fin (n + 1),
      (F.assignedChain hcover q τ).obj i =
        ((F.assignedChain hcover (p.trans q) ξ).whiskerLeft
          (secondHalfVertexFunctor n)).obj i := by
    intro i
    change F.gluedObj hcover (q (standardTime n i)) =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) (secondHalfVertex i)))
    exact congrArg (F.gluedObj hcover) (trans_standardTime_second p q hn i).symm
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover q τ r hr,
    F.assignedChain_secondHalf_map_succ hcover p q hn ξ r hr]
  unfold assignedSegment
  apply F.sidePathMap_heq_of_pointwise
  intro s
  exact (standardSubpath_trans_second_apply p q hn ⟨r, hr⟩ s).symm

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_refinedBlock_map_succ (hcover : U ∪ V = univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ}
    (τ : CoverAssignment p U V (n * k)) (i : Fin n)
    (r : ℕ) (hr : r < k) :
    ((F.assignedChain hcover p τ).whiskerLeft (refinedBlockFunctor i)).map'
        r (r + 1) =
      F.assignedSegment hcover p τ (refinedIndex i ⟨r, hr⟩) := by
  have hblock : i * k + r + 1 ≤ n * k := by
    calc
      i * k + r + 1 ≤ i * k + k := by omega
      _ = (i + 1) * k := by rw [Nat.add_mul, one_mul]
      _ ≤ n * k := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr i.isLt)
  unfold assignedChain
  change (ComposableArrows.mkOfObjOfMapSucc
      (fun j => F.gluedObj hcover (p (standardTime (n * k) j)))
      (fun j => F.assignedSegment hcover p τ j)).map'
        (i * k + r) (i * k + r + 1) (hjn := hblock) = _
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ (i * k + r)
    (refinedIndex i ⟨r, hr⟩).isLt

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_standardSubpath_eq_refinedBlock (hcover : U ∪ V = univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) (i : Fin n) :
    F.assignedChain hcover (standardSubpath p i)
        (CoverAssignment.constant k (σ.side i) (σ.range_subset i)) =
      (F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft (refinedBlockFunctor i) := by
  let hObj : ∀ r : Fin (k + 1),
      (F.assignedChain hcover (standardSubpath p i)
        (CoverAssignment.constant k (σ.side i) (σ.range_subset i))).obj r =
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (refinedBlockFunctor i)).obj r := by
    intro r
    change F.gluedObj hcover (standardSubpath p i (standardTime k r)) =
      F.gluedObj hcover (p (standardTime (n * k) (refinedVertex i r)))
    exact congrArg (F.gluedObj hcover) (standardSubpath_refinedVertex p hn hk i r)
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover _ _ r hr]
  rw [F.assignedChain_refinedBlock_map_succ hcover p (σ.refine hn hk) i r hr]
  change F.assignedSegment hcover (standardSubpath p i)
      (CoverAssignment.constant k (σ.side i) (σ.range_subset i)) ⟨r, hr⟩ ≍
    F.assignedSegment hcover p (σ.refine hn hk) (refinedIndex i ⟨r, hr⟩)
  unfold assignedSegment
  apply F.sidePathMap_heq_of_pointwise
  intro s
  exact (standardSubpath_refined_apply p hn hk i ⟨r, hr⟩ s).symm

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_constant_left (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ U) (n : ℕ) :
    F.assignedChain hcover p (CoverAssignment.constant n .left hp) =
      F.leftNormalizedPathChain hcover p hp n := by
  unfold assignedChain leftNormalizedPathChain normalizedChainOf
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_constant_right (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ V) (n : ℕ) :
    F.assignedChain hcover p (CoverAssignment.constant n .right hp) =
      F.rightNormalizedPathChain hcover p hp n := by
  unfold assignedChain rightNormalizedPathChain normalizedChainOf
  congr 1

theorem assignedChain_eq (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (σ τ : CoverAssignment p U V n) :
    F.assignedChain hcover p σ = F.assignedChain hcover p τ := by
  unfold assignedChain
  congr 1
  funext i
  exact F.assignedSegment_eq hcover p σ τ i

noncomputable def assignedEvaluation (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (σ : CoverAssignment p U V n) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  normalizeHom
    (by simp [assignedChain, standardTime_zero])
    (by
      change F.gluedObj hcover y = F.gluedObj hcover (p (standardTime n (Fin.last n)))
      rw [standardTime_last hn, p.target])
    (F.assignedChain hcover p σ).hom

theorem assignedEvaluation_eq (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (σ τ : CoverAssignment p U V n) :
    F.assignedEvaluation hcover p hn σ = F.assignedEvaluation hcover p hn τ := by
  have hchain := F.assignedChain_eq hcover p σ τ
  have hhom : (F.assignedChain hcover p σ).hom ≍
      (F.assignedChain hcover p τ).hom := by
    apply Functor.hcongr_hom hchain
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ hhom

theorem assignedEvaluation_constant_left (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ U) {n : ℕ} (hn : 0 < n) :
    F.assignedEvaluation hcover p hn (CoverAssignment.constant n .left hp) =
      F.leftPathMap hcover p hp := by
  have hchain := F.assignedChain_constant_left hcover p hp n
  have hhom : (F.assignedChain hcover p (CoverAssignment.constant n .left hp)).hom ≍
      (F.leftNormalizedPathChain hcover p hp n).hom := by
    apply Functor.hcongr_hom hchain
  have hnormalized : (F.leftNormalizedPathChain hcover p hp n).hom ≍
      (F.leftPathChain p hp n).hom := by
    unfold leftNormalizedPathChain
    rw [normalizedChainOf_hom]
    apply normalizeHom_heq
  have htotal : (F.assignedChain hcover p (CoverAssignment.constant n .left hp)).hom ≍
      F.left.map (Path.Homotopic.Quotient.mk (pathIn U p hp)) :=
    hhom.trans (hnormalized.trans (F.leftPathChain_hom_heq p hp hn))
  unfold assignedEvaluation leftPathMap
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ htotal

theorem assignedEvaluation_constant_right (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (hp : range p ⊆ V) {n : ℕ} (hn : 0 < n) :
    F.assignedEvaluation hcover p hn (CoverAssignment.constant n .right hp) =
      F.rightPathMap hcover p hp := by
  have hchain := F.assignedChain_constant_right hcover p hp n
  have hhom : (F.assignedChain hcover p (CoverAssignment.constant n .right hp)).hom ≍
      (F.rightNormalizedPathChain hcover p hp n).hom := by
    apply Functor.hcongr_hom hchain
  have hnormalized : (F.rightNormalizedPathChain hcover p hp n).hom ≍
      (F.rightPathChain p hp n).hom := by
    unfold rightNormalizedPathChain
    rw [normalizedChainOf_hom]
    apply normalizeHom_heq
  have htotal : (F.assignedChain hcover p (CoverAssignment.constant n .right hp)).hom ≍
      F.right.map (Path.Homotopic.Quotient.mk (pathIn V p hp)) :=
    hhom.trans (hnormalized.trans (F.rightPathChain_hom_heq p hp hn))
  unfold assignedEvaluation rightPathMap
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ htotal

theorem assignedEvaluation_constant_side (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) (side : CoverSide)
    (hp : range p ⊆ side.set U V) {n : ℕ} (hn : 0 < n) :
    F.assignedEvaluation hcover p hn (CoverAssignment.constant n side hp) =
      F.sidePathMap hcover p side hp := by
  cases side
  · exact F.assignedEvaluation_constant_left hcover p hp hn
  · exact F.assignedEvaluation_constant_right hcover p hp hn

theorem assignedSegment_heq_refinedBlock_hom (hcover : U ∪ V = univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) (i : Fin n) :
    F.assignedSegment hcover p σ i ≍
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (refinedBlockFunctor i)).hom := by
  let q := standardSubpath p i
  let τ := CoverAssignment.constant k (σ.side i) (σ.range_subset i)
  have hchain := F.assignedChain_standardSubpath_eq_refinedBlock hcover p hn hk σ i
  have hhom : (F.assignedChain hcover q τ).hom ≍
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (refinedBlockFunctor i)).hom := by
    apply Functor.hcongr_hom hchain
  have heval : F.assignedEvaluation hcover q hk τ ≍
      (F.assignedChain hcover q τ).hom := by
    unfold assignedEvaluation
    apply normalizeHom_heq
  change F.sidePathMap hcover q (σ.side i) (σ.range_subset i) ≍ _
  exact (heq_of_eq (F.assignedEvaluation_constant_side hcover q (σ.side i)
    (σ.range_subset i) hk).symm).trans (heval.trans hhom)

set_option backward.isDefEq.respectTransparency false in
theorem assignedChain_eq_refinement (hcover : U ∪ V = univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) :
    F.assignedChain hcover p σ =
      (F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (blockEndpointFunctor n k) := by
  let hObj : ∀ i : Fin (n + 1),
      (F.assignedChain hcover p σ).obj i =
        ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
          (blockEndpointFunctor n k)).obj i := by
    intro i
    change F.gluedObj hcover (p (standardTime n i)) =
      F.gluedObj hcover (p (standardTime (n * k) ((blockEndpointFunctor n k).obj i)))
    exact congrArg (fun t => F.gluedObj hcover (p t))
      (standardTime_blockEndpoint hn hk i).symm
  apply ComposableArrows.ext hObj
  intro r hr
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _ (hObj _) (hObj _)).2
  rw [F.assignedChain_map_succ hcover p σ r hr]
  exact (F.assignedSegment_heq_refinedBlock_hom hcover p hn hk σ ⟨r, hr⟩).trans
    (refinedBlock_hom_heq_blockEndpoint_map
      (F.assignedChain hcover p (σ.refine hn hk)) ⟨r, hr⟩)

theorem assignedEvaluation_mul (hcover : U ∪ V = univ)
    {x y : X} (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (σ : CoverAssignment p U V n) :
    F.assignedEvaluation hcover p hn σ =
      F.assignedEvaluation hcover p (Nat.mul_pos hn hk) (σ.refine hn hk) := by
  have hchain := F.assignedChain_eq_refinement hcover p hn hk σ
  have hhom : (F.assignedChain hcover p σ).hom ≍
      ((F.assignedChain hcover p (σ.refine hn hk)).whiskerLeft
        (blockEndpointFunctor n k)).hom := by
    apply Functor.hcongr_hom hchain
  have htotal : (F.assignedChain hcover p σ).hom ≍
      (F.assignedChain hcover p (σ.refine hn hk)).hom :=
    hhom.trans (blockEndpoint_hom_heq
      (F.assignedChain hcover p (σ.refine hn hk)))
  unfold assignedEvaluation
  apply normalizeHom_eq_of_heq _ _ _ _ _ _ htotal

theorem assignedEvaluation_trans (hcover : U ∪ V = univ)
    {x y z : X} (p : _root_.Path x y) (q : _root_.Path y z) {n : ℕ}
    (hn : 0 < n) (σ : CoverAssignment p U V n) (τ : CoverAssignment q U V n) :
    F.assignedEvaluation hcover (p.trans q) (Nat.mul_pos (by omega) hn)
        (CoverAssignment.trans hn σ τ) =
      F.assignedEvaluation hcover p hn σ ≫ F.assignedEvaluation hcover q hn τ := by
  let ξ := CoverAssignment.trans hn σ τ
  let R := F.assignedChain hcover (p.trans q) ξ
  have hpChain := F.assignedChain_eq_trans_first hcover p q hn σ τ
  have hqChain := F.assignedChain_eq_trans_second hcover p q hn σ τ
  have hpHom : (F.assignedChain hcover p σ).hom ≍ R.map' 0 n (hjn := by omega) := by
    have h₁ : (F.assignedChain hcover p σ).hom ≍
        (R.whiskerLeft (firstHalfVertexFunctor hn)).hom := by
      apply Functor.hcongr_hom hpChain
    exact h₁.trans (firstHalf_hom_heq_map_middle hn R)
  have hqHom : (F.assignedChain hcover q τ).hom ≍ R.map' n (2 * n) := by
    have h₁ : (F.assignedChain hcover q τ).hom ≍
        (R.whiskerLeft (secondHalfVertexFunctor n)).hom := by
      apply Functor.hcongr_hom hqChain
    exact h₁.trans (secondHalf_hom_heq_map_middle hn R)
  have h0 : F.gluedObj hcover x = R.obj' 0 := by
    change F.gluedObj hcover x =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) 0))
    rw [standardTime_zero, (p.trans q).source]
  have hmid : F.gluedObj hcover y = R.obj' n (hi := by omega) := by
    change F.gluedObj hcover y =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) ⟨n, by omega⟩))
    apply congrArg (F.gluedObj hcover)
    calc
      y = p (standardTime n (Fin.last n)) := by rw [standardTime_last hn, p.target]
      _ = (p.trans q) (standardTime (2 * n) (firstHalfVertex hn (Fin.last n))) :=
        (trans_standardTime_first p q hn (Fin.last n)).symm
      _ = (p.trans q) (standardTime (2 * n) ⟨n, by omega⟩) := by rfl
  have h2 : F.gluedObj hcover z = R.obj' (2 * n) := by
    change F.gluedObj hcover z =
      F.gluedObj hcover ((p.trans q) (standardTime (2 * n) (Fin.last (2 * n))))
    rw [standardTime_last (Nat.mul_pos (by omega) hn), (p.trans q).target]
  have hpEval : F.assignedEvaluation hcover p hn σ =
      normalizeHom h0 hmid (R.map' 0 n (hjn := by omega)) := by
    unfold assignedEvaluation
    apply normalizeHom_eq_of_heq _ _ _ _ _ _ hpHom
  have hqEval : F.assignedEvaluation hcover q hn τ =
      normalizeHom hmid h2 (R.map' n (2 * n)) := by
    unfold assignedEvaluation
    apply normalizeHom_eq_of_heq _ _ _ _ _ _ hqHom
  rw [hpEval, hqEval, ← normalizeHom_comp]
  unfold assignedEvaluation
  apply normalizeHom_eq_of_heq _ _ _ _ _ _
  exact heq_of_eq (R.map'_comp 0 n (2 * n))

noncomputable def coveredEvaluation (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hp : Path.IsCovered p U V n) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  F.assignedEvaluation hcover p hn (CoverAssignment.ofIsCovered hp)

theorem coveredEvaluation_eq_assigned (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hp : Path.IsCovered p U V n)
    (σ : CoverAssignment p U V n) :
    F.coveredEvaluation hcover p hn hp = F.assignedEvaluation hcover p hn σ :=
  F.assignedEvaluation_eq hcover p hn _ _

theorem coveredEvaluation_mul (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hp : Path.IsCovered p U V n) :
    F.coveredEvaluation hcover p hn hp =
      F.coveredEvaluation hcover p (Nat.mul_pos hn hk) (hp.mul hn hk) := by
  let σ := CoverAssignment.ofIsCovered hp
  calc
    F.coveredEvaluation hcover p hn hp = F.assignedEvaluation hcover p hn σ :=
      F.coveredEvaluation_eq_assigned hcover p hn hp σ
    _ = F.assignedEvaluation hcover p (Nat.mul_pos hn hk) (σ.refine hn hk) :=
      F.assignedEvaluation_mul hcover p hn hk σ
    _ = F.coveredEvaluation hcover p (Nat.mul_pos hn hk) (hp.mul hn hk) :=
      (F.coveredEvaluation_eq_assigned hcover p (Nat.mul_pos hn hk) (hp.mul hn hk)
        (σ.refine hn hk)).symm

theorem coveredEvaluation_eq_of_isCovered (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnCovered : Path.IsCovered p U V n) (hmCovered : Path.IsCovered p U V m) :
    F.coveredEvaluation hcover p hn hnCovered =
      F.coveredEvaluation hcover p hm hmCovered := by
  calc
    F.coveredEvaluation hcover p hn hnCovered =
        F.coveredEvaluation hcover p (Nat.mul_pos hn hm) (hnCovered.mul hn hm) :=
      F.coveredEvaluation_mul hcover p hn hm hnCovered
    _ = F.coveredEvaluation hcover p hm hmCovered := by
      symm
      simpa [Nat.mul_comm] using F.coveredEvaluation_mul hcover p hm hn hmCovered

noncomputable def Path.coveredSubdivision {x y : X} (p : _root_.Path x y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    {n : ℕ // 0 < n ∧ Path.IsCovered p U V n} :=
  ⟨(Path.exists_isCovered p hU hV hcover).choose,
    (Path.exists_isCovered p hU hV hcover).choose_spec⟩

noncomputable def rawEvaluation (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} (p : _root_.Path x y) :
    F.gluedObj hcover x ⟶ F.gluedObj hcover y :=
  let c := Path.coveredSubdivision p hU hV hcover
  F.coveredEvaluation hcover p c.property.1 c.property.2

theorem rawEvaluation_eq_covered (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} (p : _root_.Path x y)
    {n : ℕ} (hn : 0 < n) (hp : Path.IsCovered p U V n) :
    F.rawEvaluation hU hV hcover p = F.coveredEvaluation hcover p hn hp := by
  unfold rawEvaluation
  apply F.coveredEvaluation_eq_of_isCovered

theorem rawEvaluation_eq_leftPathMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} (p : _root_.Path x y)
    (hp : range p ⊆ U) :
    F.rawEvaluation hU hV hcover p = F.leftPathMap hcover p hp := by
  let hcovered : Path.IsCovered p U V 1 := fun i =>
    Or.inl (range_standardSubpath_subset p hp i)
  calc
    F.rawEvaluation hU hV hcover p =
        F.coveredEvaluation hcover p Nat.zero_lt_one hcovered :=
      F.rawEvaluation_eq_covered hU hV hcover p Nat.zero_lt_one hcovered
    _ = F.assignedEvaluation hcover p Nat.zero_lt_one
        (CoverAssignment.constant 1 .left hp) :=
      F.coveredEvaluation_eq_assigned hcover p Nat.zero_lt_one hcovered _
    _ = F.leftPathMap hcover p hp :=
      F.assignedEvaluation_constant_left hcover p hp Nat.zero_lt_one

theorem rawEvaluation_eq_rightPathMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} (p : _root_.Path x y)
    (hp : range p ⊆ V) :
    F.rawEvaluation hU hV hcover p = F.rightPathMap hcover p hp := by
  let hcovered : Path.IsCovered p U V 1 := fun i =>
    Or.inr (range_standardSubpath_subset p hp i)
  calc
    F.rawEvaluation hU hV hcover p =
        F.coveredEvaluation hcover p Nat.zero_lt_one hcovered :=
      F.rawEvaluation_eq_covered hU hV hcover p Nat.zero_lt_one hcovered
    _ = F.assignedEvaluation hcover p Nat.zero_lt_one
        (CoverAssignment.constant 1 .right hp) :=
      F.coveredEvaluation_eq_assigned hcover p Nat.zero_lt_one hcovered _
    _ = F.rightPathMap hcover p hp :=
      F.assignedEvaluation_constant_right hcover p hp Nat.zero_lt_one

theorem rawEvaluation_refl (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (x : X) :
    F.rawEvaluation hU hV hcover (_root_.Path.refl x) = 𝟙 (F.gluedObj hcover x) := by
  have hx : x ∈ U ∨ x ∈ V := by
    have : x ∈ U ∪ V := by rw [hcover]; trivial
    exact this
  rcases hx with hxU | hxV
  · let hp : range (_root_.Path.refl x) ⊆ U := by
      rintro _ ⟨t, rfl⟩
      exact hxU
    rw [F.rawEvaluation_eq_leftPathMap hU hV hcover (_root_.Path.refl x) hp]
    exact F.leftPathMap_refl hcover hp
  · let hp : range (_root_.Path.refl x) ⊆ V := by
      rintro _ ⟨t, rfl⟩
      exact hxV
    rw [F.rawEvaluation_eq_rightPathMap hU hV hcover (_root_.Path.refl x) hp]
    exact F.rightPathMap_refl hcover hp

theorem rawEvaluation_trans (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y z : X}
    (p : _root_.Path x y) (q : _root_.Path y z) :
    F.rawEvaluation hU hV hcover (p.trans q) =
      F.rawEvaluation hU hV hcover p ≫ F.rawEvaluation hU hV hcover q := by
  obtain ⟨np, hnp, hp⟩ := Path.exists_isCovered p hU hV hcover
  obtain ⟨nq, hnq, hq⟩ := Path.exists_isCovered q hU hV hcover
  let n := np * nq
  have hn : 0 < n := Nat.mul_pos hnp hnq
  let hpN : Path.IsCovered p U V n := hp.mul hnp hnq
  let hqN : Path.IsCovered q U V n := by
    simpa [n, Nat.mul_comm] using hq.mul hnq hnp
  let σ := CoverAssignment.ofIsCovered hpN
  let τ := CoverAssignment.ofIsCovered hqN
  let ξ := CoverAssignment.trans hn σ τ
  have hξ : Path.IsCovered (p.trans q) U V (2 * n) := ξ.isCovered
  calc
    F.rawEvaluation hU hV hcover (p.trans q) =
        F.coveredEvaluation hcover (p.trans q) (Nat.mul_pos (by omega) hn) hξ :=
      F.rawEvaluation_eq_covered hU hV hcover (p.trans q)
        (Nat.mul_pos (by omega) hn) hξ
    _ = F.assignedEvaluation hcover (p.trans q) (Nat.mul_pos (by omega) hn) ξ :=
      F.coveredEvaluation_eq_assigned hcover (p.trans q)
        (Nat.mul_pos (by omega) hn) hξ ξ
    _ = F.assignedEvaluation hcover p hn σ ≫ F.assignedEvaluation hcover q hn τ :=
      F.assignedEvaluation_trans hcover p q hn σ τ
    _ = F.coveredEvaluation hcover p hn hpN ≫
        F.coveredEvaluation hcover q hn hqN := by
      rw [F.coveredEvaluation_eq_assigned hcover p hn hpN σ,
        F.coveredEvaluation_eq_assigned hcover q hn hqN τ]
    _ = F.rawEvaluation hU hV hcover p ≫ F.rawEvaluation hU hV hcover q := by
      rw [F.rawEvaluation_eq_covered hU hV hcover p hn hpN,
        F.rawEvaluation_eq_covered hU hV hcover q hn hqN]

theorem coveredEvaluation_eq_leftPathMap (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hcovered : Path.IsCovered p U V n)
    (hp : range p ⊆ U) :
    F.coveredEvaluation hcover p hn hcovered = F.leftPathMap hcover p hp := by
  rw [F.coveredEvaluation_eq_assigned hcover p hn hcovered
    (CoverAssignment.constant n .left hp)]
  exact F.assignedEvaluation_constant_left hcover p hp hn

theorem coveredEvaluation_eq_rightPathMap (hcover : U ∪ V = univ) {x y : X}
    (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) (hcovered : Path.IsCovered p U V n)
    (hp : range p ⊆ V) :
    F.coveredEvaluation hcover p hn hcovered = F.rightPathMap hcover p hp := by
  rw [F.coveredEvaluation_eq_assigned hcover p hn hcovered
    (CoverAssignment.constant n .right hp)]
  exact F.assignedEvaluation_constant_right hcover p hp hn

end LocalFunctorData

end DifferentialGeometry.Topology.VanKampen
end svkBundle_004
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/Evaluation.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/HomotopyGrid.lean
section svkBundle_005
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open Metric Set unitInterval
open scoped unitInterval

universe u

namespace DifferentialGeometry.Topology.VanKampen

def IsCoveredGrid {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    (U V : Set X) (n : ℕ) : Prop :=
  ∀ i j : Fin n,
    H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ U ∨
    H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ V

theorem exists_coveredGrid {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    ∃ n : ℕ, 0 < n ∧ IsCoveredGrid H U V n := by
  let c : Bool → Set (I × I) := fun side ↦ H ⁻¹' if side then U else V
  have hc_open : ∀ side, IsOpen (c side) := by
    intro side
    cases side <;> simp [c, hU, hV, H.continuous.isOpen_preimage]
  have hc_cover : (univ : Set (I × I)) ⊆ ⋃ side, c side := by
    intro z _
    have hz : H z ∈ U ∪ V := by rw [hcover]; trivial
    rcases hz with hzU | hzV
    · exact mem_iUnion.mpr ⟨true, by simpa [c] using hzU⟩
    · exact mem_iUnion.mpr ⟨false, by simpa [c] using hzV⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := (univ : Set (I × I))) isCompact_univ hc_open hc_cover
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hm
  refine ⟨n, hn, ?_⟩
  intro i j
  let z₀ : I × I := (standardTime n i.castSucc, standardTime n j.castSucc)
  obtain ⟨side, hside⟩ := hball z₀ (mem_univ _)
  let cell := Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
    Icc (standardTime n j.castSucc) (standardTime n j.succ)
  have hcell : cell ⊆ c side := by
    intro z hz
    apply hside
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · simpa [z₀, dist_comm] using
        (Path.dist_standardTime_le hn i z.1 hz.1).trans_lt hmesh
    · simpa [z₀, dist_comm] using
        (Path.dist_standardTime_le hn j z.2 hz.2).trans_lt hmesh
  have himage : H '' cell ⊆ if side then U else V := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcell hz
  cases side
  · exact Or.inr himage
  · exact Or.inl himage

end DifferentialGeometry.Topology.VanKampen
end svkBundle_005
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/HomotopyGrid.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/CellIdentity.lean
section svkBundle_006
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory Set unitInterval
open scoped unitInterval

universe u v

namespace DifferentialGeometry.Topology.VanKampen

noncomputable def convexSubtypeSegment {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) (a b : S) : _root_.Path a b where
  toFun t := ⟨AffineMap.lineMap a.1 b.1 (t : ℝ), hS.lineMap_mem a.2 b.2 t.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  source' := by
    apply Subtype.ext
    simp
  target' := by
    apply Subtype.ext
    simp

noncomputable def convexSubtypePathHomotopy {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    {S : Set E} (hS : Convex ℝ S) {a b : S} (p q : _root_.Path a b) :
    p.Homotopy q where
  toFun z := ⟨AffineMap.lineMap (p z.2).1 (q z.2).1 (z.1 : ℝ),
    hS.lineMap_mem (p z.2).2 (q z.2).2 z.1.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  map_zero_left t := by
    apply Subtype.ext
    simp
  map_one_left t := by
    apply Subtype.ext
    simp
  prop' t s hs := by
    rcases hs with hs | hs
    · subst s
      apply Subtype.ext
      simp
    · rw [Set.mem_singleton_iff] at hs
      subst s
      apply Subtype.ext
      simp

def gridCellSet {n : ℕ} (i j : Fin n) : Set (ℝ × ℝ) :=
  Icc (standardTime n i.castSucc : ℝ) (standardTime n i.succ : ℝ) ×ˢ
    Icc (standardTime n j.castSucc : ℝ) (standardTime n j.succ : ℝ)

abbrev GridCell {n : ℕ} (i j : Fin n) := ↥(gridCellSet i j)

theorem convex_gridCellSet {n : ℕ} (i j : Fin n) : Convex ℝ (gridCellSet i j) :=
  (convex_Icc _ _).prod (convex_Icc _ _)

noncomputable def gridCell00 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.castSucc : ℝ), (standardTime n j.castSucc : ℝ)),
    ⟨⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn i⟩,
      ⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn j⟩⟩⟩

noncomputable def gridCell10 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.succ : ℝ), (standardTime n j.castSucc : ℝ)),
    ⟨⟨by exact_mod_cast standardTime_castSucc_le_succ hn i, le_rfl⟩,
      ⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn j⟩⟩⟩

noncomputable def gridCell01 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.castSucc : ℝ), (standardTime n j.succ : ℝ)),
    ⟨⟨le_rfl, by exact_mod_cast standardTime_castSucc_le_succ hn i⟩,
      ⟨by exact_mod_cast standardTime_castSucc_le_succ hn j, le_rfl⟩⟩⟩

noncomputable def gridCell11 {n : ℕ} (hn : 0 < n) (i j : Fin n) : GridCell i j :=
  ⟨((standardTime n i.succ : ℝ), (standardTime n j.succ : ℝ)),
    ⟨⟨by exact_mod_cast standardTime_castSucc_le_succ hn i, le_rfl⟩,
      ⟨by exact_mod_cast standardTime_castSucc_le_succ hn j, le_rfl⟩⟩⟩

def gridCellInclusion {n : ℕ} (i j : Fin n) : C(GridCell i j, I × I) where
  toFun z :=
    (⟨z.1.1, (standardTime n i.castSucc).2.1.trans z.2.1.1,
        z.2.1.2.trans (standardTime n i.succ).2.2⟩,
      ⟨z.1.2, (standardTime n j.castSucc).2.1.trans z.2.2.1,
        z.2.2.2.trans (standardTime n j.succ).2.2⟩)
  continuous_toFun := by fun_prop

def gridCellMap {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (i j : Fin n) : C(GridCell i j, X) :=
  H.comp (gridCellInclusion i j)

noncomputable def cellBottom {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell00 hn i j) (gridCell10 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def cellRight {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell10 hn i j) (gridCell11 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def cellLeft {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell00 hn i j) (gridCell01 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def cellTop {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    _root_.Path (gridCell01 hn i j) (gridCell11 hn i j) :=
  convexSubtypeSegment (convex_gridCellSet i j) _ _

noncomputable def gridBottom {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellBottom hn i j).map (gridCellMap H i j).continuous

noncomputable def gridRight {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellRight hn i j).map (gridCellMap H i j).continuous

noncomputable def gridLeft {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellLeft hn i j).map (gridCellMap H i j).continuous

noncomputable def gridTop {X : Type u} [TopologicalSpace X] (H : C(I × I, X))
    {n : ℕ} (hn : 0 < n) (i j : Fin n) :=
  (cellTop hn i j).map (gridCellMap H i j).continuous

noncomputable def gridCellParameterHomotopy {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    ((cellBottom hn i j).trans (cellRight hn i j)).Homotopy
      ((cellLeft hn i j).trans (cellTop hn i j)) :=
  convexSubtypePathHomotopy (convex_gridCellSet i j)
    ((cellBottom hn i j).trans (cellRight hn i j))
    ((cellLeft hn i j).trans (cellTop hn i j))

noncomputable def gridCellBoundaryHomotopy {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (gridBottom H hn i j).trans (gridRight H hn i j) |>.Homotopy
      ((gridLeft H hn i j).trans (gridTop H hn i j)) where
  toFun z := gridCellMap H i j (gridCellParameterHomotopy hn i j z)
  continuous_toFun := (gridCellMap H i j).continuous.comp
    (gridCellParameterHomotopy hn i j).continuous
  map_zero_left t := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (0, t)) =
      ((cellBottom hn i j).map (gridCellMap H i j).continuous).trans
        ((cellRight hn i j).map (gridCellMap H i j).continuous) t
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).map_zero_left t)
  map_one_left t := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (1, t)) =
      ((cellLeft hn i j).map (gridCellMap H i j).continuous).trans
        ((cellTop hn i j).map (gridCellMap H i j).continuous) t
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).map_one_left t)
  prop' t s hs := by
    change gridCellMap H i j (gridCellParameterHomotopy hn i j (t, s)) =
      ((cellBottom hn i j).map (gridCellMap H i j).continuous).trans
        ((cellRight hn i j).map (gridCellMap H i j).continuous) s
    rw [← Path.map_trans]
    exact congrArg (gridCellMap H i j)
      ((gridCellParameterHomotopy hn i j).prop' t s hs)

theorem gridCellMap_mem_of_image_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A)
    (z : GridCell i j) : gridCellMap H i j z ∈ A := by
  apply hcell
  refine ⟨gridCellInclusion i j z, ?_, rfl⟩
  constructor
  · constructor
    · exact_mod_cast z.2.1.1
    · exact_mod_cast z.2.1.2
  · constructor
    · exact_mod_cast z.2.2.1
    · exact_mod_cast z.2.2.2

def pathHomotopyIn {X : Type u} [TopologicalSpace X] {A : Set X} {x y : X}
    {p q : _root_.Path x y} (hp : range p ⊆ A) (hq : range q ⊆ A)
    (K : p.Homotopy q) (hK : ∀ z, K z ∈ A) :
    (pathIn A p hp).Homotopy (pathIn A q hq) where
  toFun z := ⟨K z, hK z⟩
  continuous_toFun := K.continuous.subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    exact K.map_zero_left t
  map_one_left t := by
    apply Subtype.ext
    exact K.map_one_left t
  prop' t s hs := by
    apply Subtype.ext
    exact K.prop' t s hs

theorem LocalFunctorData.leftPathMap_eq_of_homotopyIn
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hcover : U ∪ V = univ) {x y : X} {p q : _root_.Path x y}
    (hp : range p ⊆ U) (hq : range q ⊆ U) (K : p.Homotopy q)
    (hK : ∀ z, K z ∈ U) :
    F.leftPathMap hcover p hp = F.leftPathMap hcover q hq := by
  unfold LocalFunctorData.leftPathMap
  apply LocalFunctorData.normalizeHom_eq_of_heq
  exact heq_of_eq (congrArg F.left.map
    (Path.Homotopic.Quotient.eq.mpr ⟨pathHomotopyIn hp hq K hK⟩))

theorem LocalFunctorData.rightPathMap_eq_of_homotopyIn
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hcover : U ∪ V = univ) {x y : X} {p q : _root_.Path x y}
    (hp : range p ⊆ V) (hq : range q ⊆ V) (K : p.Homotopy q)
    (hK : ∀ z, K z ∈ V) :
    F.rightPathMap hcover p hp = F.rightPathMap hcover q hq := by
  unfold LocalFunctorData.rightPathMap
  apply LocalFunctorData.normalizeHom_eq_of_heq
  exact heq_of_eq (congrArg F.right.map
    (Path.Homotopic.Quotient.eq.mpr ⟨pathHomotopyIn hp hq K hK⟩))

theorem range_gridBottom_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridBottom H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellBottom hn i j) t)

theorem range_gridRight_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridRight H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellRight hn i j) t)

theorem range_gridLeft_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridLeft H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellLeft hn i j) t)

theorem range_gridTop_subset {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A) :
    range (gridTop H hn i j) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact gridCellMap_mem_of_image_subset H i j hcell ((cellTop hn i j) t)

theorem gridCellBoundaryHomotopy_mem {X : Type u} [TopologicalSpace X]
    (H : C(I × I, X)) {A : Set X} {n : ℕ} (hn : 0 < n) (i j : Fin n)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ A)
    (z : I × I) : gridCellBoundaryHomotopy H hn i j z ∈ A := by
  exact gridCellMap_mem_of_image_subset H i j hcell
    (gridCellParameterHomotopy hn i j z)

theorem LocalFunctorData.cell_boundary_of_side
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (i j : Fin n) (side : CoverSide)
    (hcell : H '' (Icc (standardTime n i.castSucc) (standardTime n i.succ) ×ˢ
      Icc (standardTime n j.castSucc) (standardTime n j.succ)) ⊆ side.set U V) :
    F.rawEvaluation hU hV hcover (gridBottom H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridRight H hn i j) =
      F.rawEvaluation hU hV hcover (gridLeft H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridTop H hn i j) := by
  rw [← F.rawEvaluation_trans hU hV hcover (gridBottom H hn i j) (gridRight H hn i j),
    ← F.rawEvaluation_trans hU hV hcover (gridLeft H hn i j) (gridTop H hn i j)]
  have hbr : range ((gridBottom H hn i j).trans (gridRight H hn i j)) ⊆
      side.set U V := by
    rw [_root_.Path.trans_range]
    exact union_subset (range_gridBottom_subset H hn i j hcell)
      (range_gridRight_subset H hn i j hcell)
  have hlt : range ((gridLeft H hn i j).trans (gridTop H hn i j)) ⊆
      side.set U V := by
    rw [_root_.Path.trans_range]
    exact union_subset (range_gridLeft_subset H hn i j hcell)
      (range_gridTop_subset H hn i j hcell)
  have hK : ∀ z, gridCellBoundaryHomotopy H hn i j z ∈ side.set U V :=
    gridCellBoundaryHomotopy_mem H hn i j hcell
  cases side
  · rw [F.rawEvaluation_eq_leftPathMap hU hV hcover _ hbr,
      F.rawEvaluation_eq_leftPathMap hU hV hcover _ hlt]
    exact F.leftPathMap_eq_of_homotopyIn hcover hbr hlt
      (gridCellBoundaryHomotopy H hn i j) hK
  · rw [F.rawEvaluation_eq_rightPathMap hU hV hcover _ hbr,
      F.rawEvaluation_eq_rightPathMap hU hV hcover _ hlt]
    exact F.rightPathMap_eq_of_homotopyIn hcover hbr hlt
      (gridCellBoundaryHomotopy H hn i j) hK

theorem LocalFunctorData.cell_boundary
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (H : C(I × I, X)) {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid H U V n)
    (i j : Fin n) :
    F.rawEvaluation hU hV hcover (gridBottom H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridRight H hn i j) =
      F.rawEvaluation hU hV hcover (gridLeft H hn i j) ≫
        F.rawEvaluation hU hV hcover (gridTop H hn i j) := by
  rcases hgrid i j with hcell | hcell
  · exact F.cell_boundary_of_side hU hV hcover H hn i j .left hcell
  · exact F.cell_boundary_of_side hU hV hcover H hn i j .right hcell

end DifferentialGeometry.Topology.VanKampen
end svkBundle_006
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/CellIdentity.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/GroupoidTelescope.lean
section svkBundle_007
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory

universe u v

namespace DifferentialGeometry.Topology.VanKampen

theorem groupoid_telescope {C : Type u} [Groupoid.{v} C] {n : ℕ}
    {R S : ComposableArrows C n} (α : R ⟶ S) :
    S.hom = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
      ComposableArrows.app' α n (hi := le_rfl) := by
  calc
    S.hom = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫
        ComposableArrows.app' α 0 (hi := Nat.zero_le n) ≫ S.hom := by
      rw [IsIso.inv_hom_id_assoc]
    _ = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫
        (R.hom ≫ ComposableArrows.app' α n (hi := le_rfl)) := by
      rw [ComposableArrows.naturality' α 0 n]
    _ = inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
        ComposableArrows.app' α n (hi := le_rfl) := by
      rfl

section Regression

example {C : Type u} [Groupoid.{v} C] {R S : ComposableArrows C 0} (α : R ⟶ S) :
    S.hom = inv (ComposableArrows.app' α 0 (hi := le_rfl)) ≫ R.hom ≫
      ComposableArrows.app' α 0 (hi := le_rfl) :=
  groupoid_telescope α

example {C : Type u} [Groupoid.{v} C] {R S : ComposableArrows C 1} (α : R ⟶ S) :
    S.hom = inv (ComposableArrows.app' α 0 (hi := by omega)) ≫ R.hom ≫
      ComposableArrows.app' α 1 (hi := le_rfl) :=
  groupoid_telescope α

end Regression

end DifferentialGeometry.Topology.VanKampen
end svkBundle_007
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/GroupoidTelescope.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/HomotopyInvariance.lean
section svkBundle_008
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory Set unitInterval
open scoped unitInterval

universe u v

namespace DifferentialGeometry.Topology.VanKampen

def homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) : C(I × I, X) where
  toFun z := K (z.2, z.1)
  continuous_toFun := K.continuous.comp (by fun_prop)

noncomputable def homotopyVerticalEdge {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (k : Fin (n + 1)) (j : Fin n) :
    _root_.Path (K.eval (standardTime n j.castSucc) (standardTime n k))
      (K.eval (standardTime n j.succ) (standardTime n k)) where
  toFun t := K (Set.Icc.convexComb (standardTime n j.castSucc)
    (standardTime n j.succ) t, standardTime n k)
  continuous_toFun := K.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

theorem gridBottom_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridBottom (homotopySquare K) hn i j =
      standardSubpath (K.eval (standardTime n j.castSucc)) i := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellBottom hn i j) t).1.2 : ℝ) = standardTime n j.castSucc
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell10 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell00, gridCell10]
    ring
  · apply Subtype.ext
    change (((cellBottom hn i j) t).1.1 : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell10 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    rfl

theorem gridTop_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridTop (homotopySquare K) hn i j =
      standardSubpath (K.eval (standardTime n j.succ)) i := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellTop hn i j) t).1.2 : ℝ) = standardTime n j.succ
    change (AffineMap.lineMap (gridCell01 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell01, gridCell11]
    ring
  · apply Subtype.ext
    change (((cellTop hn i j) t).1.1 : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell01 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    rfl

theorem gridLeft_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridLeft (homotopySquare K) hn i j = homotopyVerticalEdge K i.castSucc j := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellLeft hn i j) t).1.2 : ℝ) =
      (Set.Icc.convexComb (standardTime n j.castSucc) (standardTime n j.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell01 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    rfl
  · apply Subtype.ext
    change (((cellLeft hn i j) t).1.1 : ℝ) = standardTime n i.castSucc
    change (AffineMap.lineMap (gridCell00 hn i j).1 (gridCell01 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell00, gridCell01]
    ring

theorem gridRight_homotopySquare {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    gridRight (homotopySquare K) hn i j = homotopyVerticalEdge K i.succ j := by
  apply _root_.Path.ext
  funext t
  apply congrArg K
  apply Prod.ext
  · apply Subtype.ext
    change (((cellRight hn i j) t).1.2 : ℝ) =
      (Set.Icc.convexComb (standardTime n j.castSucc) (standardTime n j.succ) t : ℝ)
    change (AffineMap.lineMap (gridCell10 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).2 = _
    rw [AffineMap.lineMap_apply_module]
    rfl
  · apply Subtype.ext
    change (((cellRight hn i j) t).1.1 : ℝ) = standardTime n i.succ
    change (AffineMap.lineMap (gridCell10 hn i j).1 (gridCell11 hn i j).1 (t : ℝ)).1 = _
    rw [AffineMap.lineMap_apply_module]
    dsimp [gridCell10, gridCell11]
    ring

theorem LocalFunctorData.rawEvaluation_heq_of_pointwise
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y x' y' : X} (p : _root_.Path x y) (q : _root_.Path x' y')
    (h : ∀ t, p t = q t) :
    F.rawEvaluation hU hV hcover p ≍ F.rawEvaluation hU hV hcover q := by
  have hx : x = x' := p.source.symm.trans ((h 0).trans q.source)
  have hy : y = y' := p.target.symm.trans ((h 1).trans q.target)
  subst x'
  subst y'
  have hpq : p = q := by
    apply _root_.Path.ext
    funext t
    exact h t
  subst q
  exact HEq.rfl

theorem LocalFunctorData.rawEvaluation_eq_sidePathMap
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} (p : _root_.Path x y) (side : CoverSide)
    (hp : range p ⊆ side.set U V) :
    F.rawEvaluation hU hV hcover p = F.sidePathMap hcover p side hp := by
  cases side
  · exact F.rawEvaluation_eq_leftPathMap hU hV hcover p hp
  · exact F.rawEvaluation_eq_rightPathMap hU hV hcover p hp

noncomputable def LocalFunctorData.rawRowChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) : ComposableArrows G n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun k ↦ F.gluedObj hcover (K.eval (standardTime n r) (standardTime n k)))
    (fun i ↦ F.rawEvaluation hU hV hcover
      (standardSubpath (K.eval (standardTime n r)) i))

theorem LocalFunctorData.rawRowChain_map_succ
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) (i : ℕ) (hi : i < n) :
    (F.rawRowChain hU hV hcover K n r).map' i (i + 1) =
      F.rawEvaluation hU hV hcover
        (standardSubpath (K.eval (standardTime n r)) ⟨i, hi⟩) := by
  apply ComposableArrows.mkOfObjOfMapSucc_map_succ

theorem homotopyRow_isCovered_bottom {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) : Path.IsCovered (K.eval (standardTime n j.castSucc)) U V n := by
  intro i
  rcases hgrid i j with hcell | hcell
  · left
    rw [← gridBottom_homotopySquare K hn i j]
    exact range_gridBottom_subset (homotopySquare K) hn i j hcell
  · right
    rw [← gridBottom_homotopySquare K hn i j]
    exact range_gridBottom_subset (homotopySquare K) hn i j hcell

theorem homotopyRow_isCovered_top {X : Type u} [TopologicalSpace X]
    {U V : Set X} {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) : Path.IsCovered (K.eval (standardTime n j.succ)) U V n := by
  intro i
  rcases hgrid i j with hcell | hcell
  · left
    rw [← gridTop_homotopySquare K hn i j]
    exact range_gridTop_subset (homotopySquare K) hn i j hcell
  · right
    rw [← gridTop_homotopySquare K hn i j]
    exact range_gridTop_subset (homotopySquare K) hn i j hcell

set_option backward.isDefEq.respectTransparency false in
theorem LocalFunctorData.rawRowChain_eq_assignedChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    F.rawRowChain hU hV hcover K n r =
      F.assignedChain hcover (K.eval (standardTime n r))
        (CoverAssignment.ofIsCovered hp) := by
  unfold LocalFunctorData.rawRowChain LocalFunctorData.assignedChain
  congr 1
  funext i
  exact F.rawEvaluation_eq_sidePathMap hU hV hcover _ _ _

theorem LocalFunctorData.rawRowChain_hom_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    (F.rawRowChain hU hV hcover K n r).hom ≍
      F.rawEvaluation hU hV hcover (K.eval (standardTime n r)) := by
  rw [F.rawRowChain_eq_assignedChain hU hV hcover K r hp]
  rw [F.rawEvaluation_eq_covered hU hV hcover _ hn hp]
  unfold LocalFunctorData.coveredEvaluation LocalFunctorData.assignedEvaluation
  exact (LocalFunctorData.normalizeHom_heq _ _ _).symm

noncomputable def LocalFunctorData.rawRowTransformation
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    F.rawRowChain hU hV hcover K n j.castSucc ⟶
      F.rawRowChain hU hV hcover K n j.succ :=
  ComposableArrows.homMk
    (fun k ↦ F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k j))
    (by
      intro i hi
      rw [F.rawRowChain_map_succ hU hV hcover K n j.castSucc i hi,
        F.rawRowChain_map_succ hU hV hcover K n j.succ i hi]
      let k : Fin n := ⟨i, hi⟩
      change F.rawEvaluation hU hV hcover
          (standardSubpath (K.eval (standardTime n j.castSucc)) k) ≫
            F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k.succ j) =
        F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k.castSucc j) ≫
          F.rawEvaluation hU hV hcover
            (standardSubpath (K.eval (standardTime n j.succ)) k)
      rw [← gridBottom_homotopySquare K hn k j,
        ← gridRight_homotopySquare K hn k j,
        ← gridLeft_homotopySquare K hn k j,
        ← gridTop_homotopySquare K hn k j]
      exact F.cell_boundary hU hV hcover (homotopySquare K) hn hgrid k j)

theorem LocalFunctorData.rawRowTransformation_app
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) (k : Fin (n + 1)) :
    (F.rawRowTransformation hU hV hcover K hn hgrid j).app k =
      F.rawEvaluation hU hV hcover (homotopyVerticalEdge K k j) :=
  rfl

theorem homotopyVerticalEdge_zero_apply {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ}
    (j : Fin n) (t : I) : homotopyVerticalEdge K (0 : Fin (n + 1)) j t = x := by
  simp [homotopyVerticalEdge]

theorem homotopyVerticalEdge_last_apply {X : Type u} [TopologicalSpace X] {x y : X}
    {p q : _root_.Path x y} (K : p.Homotopy q) {n : ℕ} (hn : 0 < n)
    (j : Fin n) (t : I) : homotopyVerticalEdge K (Fin.last n) j t = y := by
  simp [homotopyVerticalEdge, standardTime_last hn]

theorem LocalFunctorData.rawRowTransformation_app_zero_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    ComposableArrows.app' (F.rawRowTransformation hU hV hcover K hn hgrid j) 0 ≍
      𝟙 (F.gluedObj hcover x) := by
  change F.rawEvaluation hU hV hcover
      (homotopyVerticalEdge K (0 : Fin (n + 1)) j) ≍ 𝟙 (F.gluedObj hcover x)
  exact (F.rawEvaluation_heq_of_pointwise hU hV hcover
    (homotopyVerticalEdge K (0 : Fin (n + 1)) j) (_root_.Path.refl x)
      (homotopyVerticalEdge_zero_apply K j)).trans
        (heq_of_eq (F.rawEvaluation_refl hU hV hcover x))

theorem LocalFunctorData.rawRowTransformation_app_last_heq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    ComposableArrows.app' (F.rawRowTransformation hU hV hcover K hn hgrid j) n ≍
      𝟙 (F.gluedObj hcover y) := by
  change F.rawEvaluation hU hV hcover
      (homotopyVerticalEdge K (Fin.last n) j) ≍ 𝟙 (F.gluedObj hcover y)
  exact (F.rawEvaluation_heq_of_pointwise hU hV hcover
    (homotopyVerticalEdge K (Fin.last n) j) (_root_.Path.refl y)
      (homotopyVerticalEdge_last_apply K hn j)).trans
        (heq_of_eq (F.rawEvaluation_refl hU hV hcover y))

theorem LocalFunctorData.normalizeHom_inv
    {G : Type v} [Groupoid G] {a a' b b' : G}
    (ha : a = a') (hb : b = b') (f : a' ⟶ b') :
    LocalFunctorData.normalizeHom hb ha (inv f) =
      inv (LocalFunctorData.normalizeHom ha hb f) := by
  subst a'
  subst b'
  simp [LocalFunctorData.normalizeHom]

theorem LocalFunctorData.gluedObj_eq_rawRowChain_left
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    (n : ℕ) (r : Fin (n + 1)) :
    F.gluedObj hcover x = (F.rawRowChain hU hV hcover K n r).left := by
  change F.gluedObj hcover x =
    F.gluedObj hcover (K.eval (standardTime n r) (standardTime n 0))
  apply congrArg (F.gluedObj hcover)
  simp

theorem LocalFunctorData.gluedObj_eq_rawRowChain_right
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1)) :
    F.gluedObj hcover y = (F.rawRowChain hU hV hcover K n r).right := by
  change F.gluedObj hcover y =
    F.gluedObj hcover (K.eval (standardTime n r) (standardTime n (Fin.last n)))
  apply congrArg (F.gluedObj hcover)
  simp [standardTime_last hn]

theorem LocalFunctorData.rawEvaluation_eq_normalize_rawRowChain
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (r : Fin (n + 1))
    (hp : Path.IsCovered (K.eval (standardTime n r)) U V n) :
    F.rawEvaluation hU hV hcover (K.eval (standardTime n r)) =
      LocalFunctorData.normalizeHom
        (F.gluedObj_eq_rawRowChain_left hU hV hcover K n r)
        (F.gluedObj_eq_rawRowChain_right hU hV hcover K hn r)
        (F.rawRowChain hU hV hcover K n r).hom := by
  rw [F.rawEvaluation_eq_covered hU hV hcover _ hn hp]
  unfold LocalFunctorData.coveredEvaluation LocalFunctorData.assignedEvaluation
  apply LocalFunctorData.normalizeHom_eq_of_heq
  have hhom :
      (F.assignedChain hcover (K.eval (standardTime n r))
        (CoverAssignment.ofIsCovered hp)).hom ≍
        (F.rawRowChain hU hV hcover K n r).hom := by
    apply Functor.hcongr_hom
    exact (F.rawRowChain_eq_assignedChain hU hV hcover K r hp).symm
  exact hhom

theorem LocalFunctorData.rawEvaluation_eval_succ_eq
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n)
    (j : Fin n) :
    F.rawEvaluation hU hV hcover (K.eval (standardTime n j.succ)) =
      F.rawEvaluation hU hV hcover (K.eval (standardTime n j.castSucc)) := by
  let R := F.rawRowChain hU hV hcover K n j.castSucc
  let S := F.rawRowChain hU hV hcover K n j.succ
  let α : R ⟶ S := F.rawRowTransformation hU hV hcover K hn hgrid j
  have htel : S.hom =
      inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) ≫ R.hom ≫
        ComposableArrows.app' α n (hi := le_rfl) :=
    groupoid_telescope α
  have hα0 : ComposableArrows.app' α 0 (hi := Nat.zero_le n) ≍
      𝟙 (F.gluedObj hcover x) := by
    exact F.rawRowTransformation_app_zero_heq hU hV hcover K hn hgrid j
  have hαn : ComposableArrows.app' α n (hi := le_rfl) ≍
      𝟙 (F.gluedObj hcover y) := by
    exact F.rawRowTransformation_app_last_heq hU hV hcover K hn hgrid j
  let rx : F.gluedObj hcover x = R.left :=
    F.gluedObj_eq_rawRowChain_left hU hV hcover K n j.castSucc
  let sx : F.gluedObj hcover x = S.left :=
    F.gluedObj_eq_rawRowChain_left hU hV hcover K n j.succ
  let ry : F.gluedObj hcover y = R.right :=
    F.gluedObj_eq_rawRowChain_right hU hV hcover K hn j.castSucc
  let sy : F.gluedObj hcover y = S.right :=
    F.gluedObj_eq_rawRowChain_right hU hV hcover K hn j.succ
  have hα0Norm : LocalFunctorData.normalizeHom rx sx
      (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) = 𝟙 (F.gluedObj hcover x) := by
    calc
      LocalFunctorData.normalizeHom rx sx
          (ComposableArrows.app' α 0 (hi := Nat.zero_le n)) =
          LocalFunctorData.normalizeHom rfl rfl (𝟙 (F.gluedObj hcover x)) :=
        LocalFunctorData.normalizeHom_eq_of_heq rx rfl sx rfl _ _ hα0
      _ = 𝟙 (F.gluedObj hcover x) := LocalFunctorData.normalizeHom_id rfl
  have hαnNorm : LocalFunctorData.normalizeHom ry sy
      (ComposableArrows.app' α n (hi := le_rfl)) = 𝟙 (F.gluedObj hcover y) := by
    calc
      LocalFunctorData.normalizeHom ry sy
          (ComposableArrows.app' α n (hi := le_rfl)) =
          LocalFunctorData.normalizeHom rfl rfl (𝟙 (F.gluedObj hcover y)) :=
        LocalFunctorData.normalizeHom_eq_of_heq ry rfl sy rfl _ _ hαn
      _ = 𝟙 (F.gluedObj hcover y) := LocalFunctorData.normalizeHom_id rfl
  have hnorm : LocalFunctorData.normalizeHom sx sy S.hom =
      LocalFunctorData.normalizeHom rx ry R.hom := by
    rw [htel]
    rw [LocalFunctorData.normalizeHom_comp sx rx sy
      (inv (ComposableArrows.app' α 0 (hi := Nat.zero_le n)))
      (R.hom ≫ ComposableArrows.app' α n (hi := le_rfl))]
    rw [LocalFunctorData.normalizeHom_comp rx ry sy R.hom
      (ComposableArrows.app' α n (hi := le_rfl))]
    rw [LocalFunctorData.normalizeHom_inv rx sx,
      hα0Norm, hαnNorm]
    simp
  rw [F.rawEvaluation_eq_normalize_rawRowChain hU hV hcover K hn j.succ
      (homotopyRow_isCovered_top K hn hgrid j),
    F.rawEvaluation_eq_normalize_rawRowChain hU hV hcover K hn j.castSucc
      (homotopyRow_isCovered_bottom K hn hgrid j)]
  exact hnorm

theorem LocalFunctorData.rawEvaluation_eq_of_homotopyGrid
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q)
    {n : ℕ} (hn : 0 < n) (hgrid : IsCoveredGrid (homotopySquare K) U V n) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  have hrows : ∀ (k : ℕ) (hk : k ≤ n),
      F.rawEvaluation hU hV hcover
          (K.eval (standardTime n ⟨k, Nat.lt_succ_of_le hk⟩)) =
        F.rawEvaluation hU hV hcover (K.eval (standardTime n 0)) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
        have hklt : k < n := Nat.lt_of_succ_le hk
        let j : Fin n := ⟨k, hklt⟩
        calc
          F.rawEvaluation hU hV hcover
              (K.eval (standardTime n ⟨k + 1, Nat.lt_succ_of_le hk⟩)) =
              F.rawEvaluation hU hV hcover (K.eval (standardTime n j.succ)) := by
                rfl
          _ = F.rawEvaluation hU hV hcover
              (K.eval (standardTime n j.castSucc)) :=
                F.rawEvaluation_eval_succ_eq hU hV hcover K hn hgrid j
          _ = F.rawEvaluation hU hV hcover (K.eval (standardTime n 0)) :=
                ih (Nat.le_of_succ_le hk)
  have hlast := hrows n le_rfl
  have hfin : (⟨n, Nat.lt_succ_of_le (le_refl n)⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    rfl
  rw [hfin, standardTime_last hn] at hlast
  simpa using hlast.symm

theorem LocalFunctorData.rawEvaluation_eq_of_homotopy
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (K : p.Homotopy q) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  obtain ⟨n, hn, hgrid⟩ := exists_coveredGrid (homotopySquare K) hU hV hcover
  exact F.rawEvaluation_eq_of_homotopyGrid hU hV hcover K hn hgrid

theorem LocalFunctorData.rawEvaluation_eq_of_homotopic
    {X : Type u} [TopologicalSpace X] {U V : Set X}
    {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    {x y : X} {p q : _root_.Path x y} (hpq : p.Homotopic q) :
    F.rawEvaluation hU hV hcover p = F.rawEvaluation hU hV hcover q := by
  rcases hpq with ⟨K⟩
  exact F.rawEvaluation_eq_of_homotopy hU hV hcover K

end DifferentialGeometry.Topology.VanKampen
end svkBundle_008
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/HomotopyInvariance.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/FullGroupoid.lean
section svkBundle_009
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Set

universe u v

namespace DifferentialGeometry.Topology.VanKampen

def subsetToAmbient {X : Type u} [TopologicalSpace X] (A : Set X) : C(A, X) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

theorem fundamentalGroupoid_coverSquare_commutes
    {X : Type u} [TopologicalSpace X] (U V : Set X) :
    FundamentalGroupoid.map (interToLeft U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient U) =
      FundamentalGroupoid.map (interToRight U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient V) := by
  apply CategoryTheory.Functor.hext
  · intro z
    apply FundamentalGroupoid.ext
    rfl
  · intro a b γ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
        apply Path.Homotopic.hpath_hext
        intro t
        rfl

theorem range_path_map_subsetToAmbient {X : Type u} [TopologicalSpace X]
    {A : Set X} {a b : A} (p : _root_.Path a b) :
    range (p.map (subsetToAmbient A).continuous) ⊆ A := by
  rintro _ ⟨t, rfl⟩
  exact (p t).2

theorem pathIn_map_subsetToAmbient {X : Type u} [TopologicalSpace X]
    {A : Set X} {a b : A} (p : _root_.Path a b)
    (hp : range (p.map (subsetToAmbient A).continuous) ⊆ A) :
    pathIn A (p.map (subsetToAmbient A).continuous) hp = p := by
  apply _root_.Path.ext
  rfl

namespace LocalFunctorData

variable {X : Type u} [TopologicalSpace X] {U V : Set X}
  {G : Type v} [Groupoid G] (F : LocalFunctorData U V G)

noncomputable def descendedEvaluation (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} :
    Path.Homotopic.Quotient x y → (F.gluedObj hcover x ⟶ F.gluedObj hcover y) :=
  Quotient.lift (F.rawEvaluation hU hV hcover)
    (fun _ _ hpq ↦ F.rawEvaluation_eq_of_homotopic hU hV hcover hpq)

@[simp]
theorem descendedEvaluation_mk (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) {x y : X} (p : _root_.Path x y) :
    F.descendedEvaluation hU hV hcover (Path.Homotopic.Quotient.mk p) =
      F.rawEvaluation hU hV hcover p :=
  rfl

noncomputable def extension (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) : FundamentalGroupoid X ⥤ G where
  obj x := F.gluedObj hcover x.as
  map γ := F.descendedEvaluation hU hV hcover γ
  map_id x := by
    change F.rawEvaluation hU hV hcover (_root_.Path.refl x.as) =
      𝟙 (F.gluedObj hcover x.as)
    exact F.rawEvaluation_refl hU hV hcover x.as
  map_comp := by
    rintro a b c γ δ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction δ using Path.Homotopic.Quotient.ind with
      | mk q =>
        exact F.rawEvaluation_trans hU hV hcover p q

theorem extension_comp_left (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient U) ⋙ F.extension hU hV hcover = F.left := by
  apply CategoryTheory.Functor.hext
  · intro z
    exact F.gluedObj_eq_left hcover z.as.2
  · intro a b γ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
        let hp := range_path_map_subsetToAmbient p
        change F.rawEvaluation hU hV hcover
            (p.map (subsetToAmbient U).continuous) ≍
          F.left.map (Path.Homotopic.Quotient.mk p)
        rw [F.rawEvaluation_eq_leftPathMap hU hV hcover _ hp]
        unfold leftPathMap
        exact (normalizeHom_heq _ _ _).trans (heq_of_eq (congrArg F.left.map
          (congrArg Path.Homotopic.Quotient.mk (pathIn_map_subsetToAmbient p hp))))

theorem extension_comp_right (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient V) ⋙ F.extension hU hV hcover = F.right := by
  apply CategoryTheory.Functor.hext
  · intro z
    exact F.gluedObj_eq_right hcover z.as.2
  · intro a b γ
    induction γ using Path.Homotopic.Quotient.ind with
    | mk p =>
        let hp := range_path_map_subsetToAmbient p
        change F.rawEvaluation hU hV hcover
            (p.map (subsetToAmbient V).continuous) ≍
          F.right.map (Path.Homotopic.Quotient.mk p)
        rw [F.rawEvaluation_eq_rightPathMap hU hV hcover _ hp]
        unfold rightPathMap
        exact (normalizeHom_heq _ _ _).trans (heq_of_eq (congrArg F.right.map
          (congrArg Path.Homotopic.Quotient.mk (pathIn_map_subsetToAmbient p hp))))

theorem alternate_obj_eq (_hU : IsOpen U) (_hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    (z : FundamentalGroupoid X) : L.obj z = F.gluedObj hcover z.as := by
  classical
  by_cases hzU : z.as ∈ U
  · let zu : FundamentalGroupoid U := ⟨⟨z.as, hzU⟩⟩
    have h := CategoryTheory.Functor.congr_obj hleft zu
    have hzu : (FundamentalGroupoid.map (subsetToAmbient U)).obj zu = z := by
      apply FundamentalGroupoid.ext
      rfl
    calc
      L.obj z = L.obj ((FundamentalGroupoid.map (subsetToAmbient U)).obj zu) :=
        congrArg L.obj hzu.symm
      _ = F.left.obj zu := h
      _ = F.gluedObj hcover z.as := by
        symm
        exact F.gluedObj_eq_left hcover hzU
  · have hzV : z.as ∈ V := by
      have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
      exact hz.resolve_left hzU
    let zv : FundamentalGroupoid V := ⟨⟨z.as, hzV⟩⟩
    have h := CategoryTheory.Functor.congr_obj hright zv
    have hzv : (FundamentalGroupoid.map (subsetToAmbient V)).obj zv = z := by
      apply FundamentalGroupoid.ext
      rfl
    calc
      L.obj z = L.obj ((FundamentalGroupoid.map (subsetToAmbient V)).obj zv) :=
        congrArg L.obj hzv.symm
      _ = F.right.obj zv := h
      _ = F.gluedObj hcover z.as := by
        symm
        exact F.gluedObj_eq_right hcover hzV

theorem alternate_map_mk_heq_sidePathMap (_hU : IsOpen U) (_hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) (side : CoverSide)
    (hp : range p ⊆ side.set U V) :
    L.map (Path.Homotopic.Quotient.mk p) ≍ F.sidePathMap hcover p side hp := by
  cases side with
  | left =>
      let hpU : range p ⊆ U := by simpa [CoverSide.set] using hp
      let pU := pathIn U p hpU
      have hmap := CategoryTheory.Functor.hcongr_hom hleft
        (Path.Homotopic.Quotient.mk pU)
      change L.map ((Path.Homotopic.Quotient.mk pU).map (subsetToAmbient U)) ≍
        F.left.map (Path.Homotopic.Quotient.mk pU) at hmap
      have hq : (Path.Homotopic.Quotient.mk pU).map (subsetToAmbient U) =
          Path.Homotopic.Quotient.mk p := by
        apply congrArg Path.Homotopic.Quotient.mk
        apply _root_.Path.ext
        rfl
      rw [hq] at hmap
      change L.map (Path.Homotopic.Quotient.mk p) ≍ F.leftPathMap hcover p hpU
      unfold leftPathMap
      exact hmap.trans (normalizeHom_heq _ _ _).symm
  | right =>
      let hpV : range p ⊆ V := by simpa [CoverSide.set] using hp
      let pV := pathIn V p hpV
      have hmap := CategoryTheory.Functor.hcongr_hom hright
        (Path.Homotopic.Quotient.mk pV)
      change L.map ((Path.Homotopic.Quotient.mk pV).map (subsetToAmbient V)) ≍
        F.right.map (Path.Homotopic.Quotient.mk pV) at hmap
      have hq : (Path.Homotopic.Quotient.mk pV).map (subsetToAmbient V) =
          Path.Homotopic.Quotient.mk p := by
        apply congrArg Path.Homotopic.Quotient.mk
        apply _root_.Path.ext
        rfl
      rw [hq] at hmap
      change L.map (Path.Homotopic.Quotient.mk p) ≍ F.rightPathMap hcover p hpV
      unfold rightPathMap
      exact hmap.trans (normalizeHom_heq _ _ _).symm

theorem mappedStandardPathChain_hom_heq (L : FundamentalGroupoid X ⥤ G)
    {x y : X} (p : _root_.Path x y) {n : ℕ} (hn : 0 < n) :
    ((L.mapComposableArrows n).obj (standardPathChain p n)).hom ≍
      L.map (Path.Homotopic.Quotient.mk p) := by
  have h0 : (standardPathChain p n).left = FundamentalGroupoid.mk x := by
    apply FundamentalGroupoid.ext
    change p (standardTime n 0) = x
    rw [standardTime_zero, p.source]
  have h1 : (standardPathChain p n).right = FundamentalGroupoid.mk y := by
    apply FundamentalGroupoid.ext
    change p (standardTime n (Fin.last n)) = y
    rw [standardTime_last hn, p.target]
  have hraw : (standardPathChain p n).hom =
      eqToHom h0 ≫ Path.Homotopic.Quotient.mk p ≫ eqToHom h1.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _ h0 h1).2
      (standardPathChain_hom_heq p hn)
  change L.map (standardPathChain p n).hom ≍
    L.map (Path.Homotopic.Quotient.mk p)
  apply (CategoryTheory.conj_eqToHom_iff_heq _ _
    (congrArg L.obj h0) (congrArg L.obj h1)).mp
  rw [hraw, L.map_comp, L.map_comp]
  simp only [CategoryTheory.eqToHom_map]

noncomputable def alternateNormalizedChain (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) (n : ℕ) : ComposableArrows G n :=
  normalizedChainOf
    (fun i ↦ F.gluedObj hcover (p (standardTime n i)))
    ((L.mapComposableArrows n).obj (standardPathChain p n))
    (fun i ↦ (F.alternate_obj_eq hU hV hcover L hleft hright
      ⟨p (standardTime n i)⟩).symm)

set_option backward.isDefEq.respectTransparency false in
theorem alternateNormalizedChain_eq_assignedChain
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) {n : ℕ} (sigma : CoverAssignment p U V n) :
    F.alternateNormalizedChain hU hV hcover L hleft hright p n =
      F.assignedChain hcover p sigma := by
  unfold alternateNormalizedChain normalizedChainOf assignedChain
  congr 1
  funext i
  change normalizeHom
      ((F.alternate_obj_eq hU hV hcover L hleft hright
        ⟨p (standardTime n i.castSucc)⟩).symm)
      ((F.alternate_obj_eq hU hV hcover L hleft hright
        ⟨p (standardTime n i.succ)⟩).symm)
      (L.map (Path.Homotopic.Quotient.mk (standardSubpath p i))) =
        F.sidePathMap hcover (standardSubpath p i) (sigma.side i) (sigma.range_subset i)
  calc
    normalizeHom
        ((F.alternate_obj_eq hU hV hcover L hleft hright
          ⟨p (standardTime n i.castSucc)⟩).symm)
        ((F.alternate_obj_eq hU hV hcover L hleft hright
          ⟨p (standardTime n i.succ)⟩).symm)
        (L.map (Path.Homotopic.Quotient.mk (standardSubpath p i))) =
      normalizeHom rfl rfl
        (F.sidePathMap hcover (standardSubpath p i) (sigma.side i)
          (sigma.range_subset i)) := by
        apply normalizeHom_eq_of_heq
        exact F.alternate_map_mk_heq_sidePathMap hU hV hcover L hleft hright
          (standardSubpath p i) (sigma.side i) (sigma.range_subset i)
    _ = F.sidePathMap hcover (standardSubpath p i) (sigma.side i)
        (sigma.range_subset i) := by simp [normalizeHom]

set_option backward.isDefEq.respectTransparency false in
theorem alternate_map_mk_heq_rawEvaluation
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right)
    {x y : X} (p : _root_.Path x y) :
    L.map (Path.Homotopic.Quotient.mk p) ≍ F.rawEvaluation hU hV hcover p := by
  obtain ⟨n, hn, hp⟩ := Path.exists_isCovered p hU hV hcover
  let sigma := CoverAssignment.ofIsCovered hp
  let mappedChain := (L.mapComposableArrows n).obj (standardPathChain p n)
  let normalizedChain := F.alternateNormalizedChain hU hV hcover L hleft hright p n
  have hmapped : mappedChain.hom ≍ L.map (Path.Homotopic.Quotient.mk p) := by
    exact mappedStandardPathChain_hom_heq L p hn
  have hnormalized : normalizedChain.hom ≍ mappedChain.hom := by
    unfold normalizedChain alternateNormalizedChain
    rw [normalizedChainOf_hom]
    apply normalizeHom_heq
  have hassigned : normalizedChain.hom ≍ (F.assignedChain hcover p sigma).hom := by
    apply Functor.hcongr_hom
    exact F.alternateNormalizedChain_eq_assignedChain hU hV hcover L hleft hright p sigma
  have hcovered : (F.assignedChain hcover p sigma).hom ≍
      F.coveredEvaluation hcover p hn hp := by
    unfold sigma coveredEvaluation assignedEvaluation
    exact (normalizeHom_heq _ _ _).symm
  have hraw : F.coveredEvaluation hcover p hn hp ≍
      F.rawEvaluation hU hV hcover p := by
    exact heq_of_eq (F.rawEvaluation_eq_covered hU hV hcover p hn hp).symm
  exact hmapped.symm.trans
    (hnormalized.symm.trans (hassigned.trans (hcovered.trans hraw)))

theorem extension_unique (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (L : FundamentalGroupoid X ⥤ G)
    (hleft : FundamentalGroupoid.map (subsetToAmbient U) ⋙ L = F.left)
    (hright : FundamentalGroupoid.map (subsetToAmbient V) ⋙ L = F.right) :
    L = F.extension hU hV hcover := by
  apply CategoryTheory.Functor.hext
  · intro z
    exact F.alternate_obj_eq hU hV hcover L hleft hright z
  · intro a b gamma
    induction gamma using Path.Homotopic.Quotient.ind with
    | mk p =>
        exact F.alternate_map_mk_heq_rawEvaluation hU hV hcover L hleft hright p

end LocalFunctorData

def fullGroupoidSquareIsPushoutStatement
    {X : Type u} [TopologicalSpace X] (U V : Set X) : Prop :=
  @IsPushout Grpd.{u, u} _
    (Grpd.of (FundamentalGroupoid (↑(U ∩ V))))
    (Grpd.of (FundamentalGroupoid U))
    (Grpd.of (FundamentalGroupoid V))
    (Grpd.of (FundamentalGroupoid X))
    (FundamentalGroupoid.map (interToLeft U V))
    (FundamentalGroupoid.map (interToRight U V))
    (FundamentalGroupoid.map (subsetToAmbient U))
    (FundamentalGroupoid.map (subsetToAmbient V))

theorem seifertVanKampen {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    fullGroupoidSquareIsPushoutStatement U V := by
  unfold fullGroupoidSquareIsPushoutStatement
  refine { w := by exact fundamentalGroupoid_coverSquare_commutes U V, isColimit' := ?_ }
  constructor
  apply PushoutCocone.isColimitAux'
  intro s
  let F : LocalFunctorData U V s.pt := {
    left := s.inl
    right := s.inr
    compatibility := s.condition }
  refine ⟨F.extension hU hV hcover, ?_, ?_, ?_⟩
  · exact F.extension_comp_left hU hV hcover
  · exact F.extension_comp_right hU hV hcover
  · intro L hleft hright
    exact F.extension_unique hU hV hcover L hleft hright

end DifferentialGeometry.Topology.VanKampen
end svkBundle_009
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/FullGroupoid.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/Representative.lean
section svkBundle_010
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory

universe u v

namespace DifferentialGeometry.Topology.VanKampen

structure RepresentativeChoice (C : Type u) [Groupoid.{v} C] (D : Set C) where
  obj : C → C
  obj_mem : ∀ x, obj x ∈ D
  hom : ∀ x, obj x ⟶ x

namespace RepresentativeChoice

variable {C : Type u} [Groupoid.{v} C] {D : Set C} (d : RepresentativeChoice C D)

noncomputable def normalizedObj (x : C) : C := by
  classical
  exact if x ∈ D then x else d.obj x

@[simp]
theorem normalizedObj_of_mem {x : C} (hx : x ∈ D) : d.normalizedObj x = x := by
  simp [normalizedObj, hx]

theorem normalizedObj_mem (x : C) : d.normalizedObj x ∈ D := by
  classical
  by_cases hx : x ∈ D
  · simp [normalizedObj, hx]
  · simp [normalizedObj, hx, d.obj_mem]

noncomputable def normalizedHom (x : C) : d.normalizedObj x ⟶ x := by
  classical
  by_cases hx : x ∈ D
  · exact eqToHom (d.normalizedObj_of_mem hx)
  · exact eqToHom (by simp [normalizedObj, hx]) ≫ d.hom x

@[simp]
theorem normalizedHom_of_mem {x : C} (hx : x ∈ D) :
    d.normalizedHom x = eqToHom (d.normalizedObj_of_mem hx) := by
  classical
  simp [normalizedHom, normalizedObj, hx]

theorem normalizedHom_conjugation_heq {x y : C} (hx : x ∈ D) (hy : y ∈ D) (f : x ⟶ y) :
    d.normalizedHom x ≫ f ≫ inv (d.normalizedHom y) ≍ f := by
  apply (CategoryTheory.conj_eqToHom_iff_heq _ f
    (d.normalizedObj_of_mem hx) (d.normalizedObj_of_mem hy)).mp
  rw [d.normalizedHom_of_mem hx, d.normalizedHom_of_mem hy]
  simp

theorem normalizedHom_heq_id_of_mem {x : C} (hx : x ∈ D) :
    d.normalizedHom x ≍ 𝟙 x := by
  rw [d.normalizedHom_of_mem hx]
  exact CategoryTheory.eqToHom_heq_id_cod _ _ _

theorem normalizedHom_heq_hom_of_not_mem {x : C} (hx : x ∉ D) :
    d.normalizedHom x ≍ d.hom x := by
  classical
  unfold normalizedHom
  simp only [hx, ↓reduceDIte]
  exact CategoryTheory.eqToHom_comp_heq _ _

end RepresentativeChoice

theorem Functor.map_heq {C : Type u} [Category.{v} C] {E : Type*} [Category E]
    (F : C ⥤ E) {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'}
    (hx : x = x') (hy : y = y') (h : f ≍ g) :
    F.map f ≍ F.map g := by
  subst x'
  subst y'
  exact heq_of_eq (congrArg F.map (eq_of_heq h))

theorem Groupoid.inv_heq {C : Type u} [Groupoid.{v} C]
    {x y x' y' : C} {f : x ⟶ y} {g : x' ⟶ y'}
    (hx : x = x') (hy : y = y') (h : f ≍ g) :
    Groupoid.inv f ≍ Groupoid.inv g := by
  subst x'
  subst y'
  exact heq_of_eq (congrArg Groupoid.inv (eq_of_heq h))

noncomputable def representativeRetraction {C : Type u} [Groupoid.{v} C] {D : Set C}
    (d : RepresentativeChoice C D) : C ⥤ (CategoryTheory.Subgroupoid.full D).objs where
  obj x := ⟨d.normalizedObj x, by simpa using d.normalizedObj_mem x⟩
  map {x y} g :=
    ⟨d.normalizedHom x ≫ g ≫ inv (d.normalizedHom y),
      by exact ⟨d.normalizedObj_mem x, d.normalizedObj_mem y⟩⟩
  map_id x := by
    apply Subtype.ext
    change d.normalizedHom x ≫ 𝟙 x ≫ inv (d.normalizedHom x) = 𝟙 (d.normalizedObj x)
    simp
  map_comp f g := by
    apply Subtype.ext
    change d.normalizedHom _ ≫ (f ≫ g) ≫ inv (d.normalizedHom _) =
      (d.normalizedHom _ ≫ f ≫ inv (d.normalizedHom _)) ≫
        (d.normalizedHom _ ≫ g ≫ inv (d.normalizedHom _))
    simp [Category.assoc]

theorem inclusion_comp_representativeRetraction {C : Type u} [Groupoid.{v} C] {D : Set C}
    (d : RepresentativeChoice C D) :
    CategoryTheory.Subgroupoid.hom (CategoryTheory.Subgroupoid.full D) ⋙
      representativeRetraction d = 𝟭 (CategoryTheory.Subgroupoid.full D).objs := by
  apply Functor.hext
  · rintro ⟨x, hx⟩
    have hxD : x ∈ D := (CategoryTheory.Subgroupoid.mem_full_objs_iff D).mp hx
    apply Subtype.ext
    simp [CategoryTheory.Subgroupoid.hom, representativeRetraction,
      RepresentativeChoice.normalizedObj, hxD]
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨f, hf⟩
    have hxD : x ∈ D := (CategoryTheory.Subgroupoid.mem_full_objs_iff D).mp hx
    have hyD : y ∈ D := (CategoryTheory.Subgroupoid.mem_full_objs_iff D).mp hy
    dsimp only [Functor.comp_map, CategoryTheory.Subgroupoid.hom, representativeRetraction,
      Functor.id_map]
    congr 1
    · rw [d.normalizedObj_of_mem hxD, d.normalizedObj_of_mem hyD]
    · apply Function.hfunext
      · rw [d.normalizedObj_of_mem hxD, d.normalizedObj_of_mem hyD]
      · intro g g' hgg
        apply heq_of_eq
        apply propext
        simp [hxD, hyD]
    · exact d.normalizedHom_conjugation_heq hxD hyD f
    · exact proof_irrel_heq _ _

noncomputable def representativeRetractionCompInclusionIso
    {C : Type u} [Groupoid.{v} C] {D : Set C} (d : RepresentativeChoice C D) :
    representativeRetraction d ⋙ CategoryTheory.Subgroupoid.hom
        (CategoryTheory.Subgroupoid.full D) ≅ 𝟭 C :=
  NatIso.ofComponents (fun x =>
    { hom := d.normalizedHom x
      inv := Groupoid.inv (d.normalizedHom x)
      hom_inv_id := Groupoid.comp_inv _
      inv_hom_id := Groupoid.inv_comp _ }) (by
    intro x y f
    change (d.normalizedHom x ≫ f ≫ inv (d.normalizedHom y)) ≫
      d.normalizedHom y = d.normalizedHom x ≫ f
    simp)

noncomputable def representativeInclusionEquivalence
    {C : Type u} [Groupoid.{v} C] {D : Set C} (d : RepresentativeChoice C D) :
    (CategoryTheory.Subgroupoid.full D).objs ≌ C :=
  CategoryTheory.Equivalence.mk
    (CategoryTheory.Subgroupoid.hom (CategoryTheory.Subgroupoid.full D))
    (representativeRetraction d)
    (eqToIso (inclusion_comp_representativeRetraction d).symm)
    (representativeRetractionCompInclusionIso d)

def IsRepresentative {Y : Type u} [TopologicalSpace Y] (A : Set Y) : Prop :=
  ∀ y : Y, ∃ a ∈ A, Joined a y

noncomputable def representativeChoiceOfIsRepresentative {Y : Type u} [TopologicalSpace Y]
    {A : Set Y} (hA : IsRepresentative A) :
    RepresentativeChoice (FundamentalGroupoid Y) {x : FundamentalGroupoid Y | x.as ∈ A} where
  obj x := ⟨(hA x.as).choose⟩
  obj_mem x := (hA x.as).choose_spec.1
  hom x := Path.Homotopic.Quotient.mk (hA x.as).choose_spec.2.somePath

noncomputable def fundamentalGroupoidRepresentativeRetraction {Y : Type u} [TopologicalSpace Y]
    {A : Set Y} (hA : IsRepresentative A) :
    FundamentalGroupoid Y ⥤
      (CategoryTheory.Subgroupoid.full {x : FundamentalGroupoid Y | x.as ∈ A}).objs :=
  representativeRetraction (representativeChoiceOfIsRepresentative hA)

theorem fundamentalGroupoid_inclusion_comp_retraction {Y : Type u} [TopologicalSpace Y]
    {A : Set Y} (hA : IsRepresentative A) :
    CategoryTheory.Subgroupoid.hom
        (CategoryTheory.Subgroupoid.full {x : FundamentalGroupoid Y | x.as ∈ A}) ⋙
      fundamentalGroupoidRepresentativeRetraction hA =
        𝟭 (CategoryTheory.Subgroupoid.full {x : FundamentalGroupoid Y | x.as ∈ A}).objs :=
  inclusion_comp_representativeRetraction (representativeChoiceOfIsRepresentative hA)

end DifferentialGeometry.Topology.VanKampen
end svkBundle_010
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/Representative.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/RetractPushout.lean
section svkBundle_011
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory

universe u v

namespace DifferentialGeometry.Topology.VanKampen

structure CommSqRetract {C : Type u} [Category.{v} C]
    {Z' X' Y' P' Z X Y P : C}
    (f' : Z' ⟶ X') (g' : Z' ⟶ Y') (inl' : X' ⟶ P') (inr' : Y' ⟶ P')
    (f : Z ⟶ X) (g : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P) where
  small : CommSq f' g' inl' inr'
  iZ : Z' ⟶ Z
  iX : X' ⟶ X
  iY : Y' ⟶ Y
  iP : P' ⟶ P
  rZ : Z ⟶ Z'
  rX : X ⟶ X'
  rY : Y ⟶ Y'
  rP : P ⟶ P'
  retract_z : iZ ≫ rZ = 𝟙 Z'
  retract_x : iX ≫ rX = 𝟙 X'
  retract_y : iY ≫ rY = 𝟙 Y'
  retract_p : iP ≫ rP = 𝟙 P'
  i_top : iZ ≫ f = f' ≫ iX
  i_left : iZ ≫ g = g' ≫ iY
  i_right : iX ≫ inl = inl' ≫ iP
  i_bottom : iY ≫ inr = inr' ≫ iP
  r_top : f ≫ rX = rZ ≫ f'
  r_left : g ≫ rY = rZ ≫ g'
  r_right : inl ≫ rP = rX ≫ inl'
  r_bottom : inr ≫ rP = rY ≫ inr'

theorem CommSqRetract.isPushout {C : Type u} [Category.{v} C]
    {Z' X' Y' P' Z X Y P : C}
    {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}
    (R : CommSqRetract f' g' inl' inr' f g inl inr)
    (h : IsPushout f g inl inr) : IsPushout f' g' inl' inr' := by
  apply IsPushout.mk' R.small.w
  · intro T d e hd he
    rw [← Category.id_comp d, ← R.retract_p, Category.assoc]
    rw [← Category.id_comp e, ← R.retract_p, Category.assoc]
    congr 1
    apply h.hom_ext
    · calc
        inl ≫ (R.rP ≫ d) = (inl ≫ R.rP) ≫ d := by simp
        _ = (R.rX ≫ inl') ≫ d := by rw [R.r_right]
        _ = R.rX ≫ (inl' ≫ d) := by simp
        _ = R.rX ≫ (inl' ≫ e) := by rw [hd]
        _ = (R.rX ≫ inl') ≫ e := by simp
        _ = (inl ≫ R.rP) ≫ e := by rw [R.r_right]
        _ = inl ≫ (R.rP ≫ e) := by simp
    · calc
        inr ≫ (R.rP ≫ d) = (inr ≫ R.rP) ≫ d := by simp
        _ = (R.rY ≫ inr') ≫ d := by rw [R.r_bottom]
        _ = R.rY ≫ (inr' ≫ d) := by simp
        _ = R.rY ≫ (inr' ≫ e) := by rw [he]
        _ = (R.rY ≫ inr') ≫ e := by simp
        _ = (inr ≫ R.rP) ≫ e := by rw [R.r_bottom]
        _ = inr ≫ (R.rP ≫ e) := by simp
  · intro T a b hab
    have hcompat : f ≫ (R.rX ≫ a) = g ≫ (R.rY ≫ b) := by
      calc
        f ≫ (R.rX ≫ a) = (f ≫ R.rX) ≫ a := by simp
        _ = (R.rZ ≫ f') ≫ a := by rw [R.r_top]
        _ = R.rZ ≫ (f' ≫ a) := by simp
        _ = R.rZ ≫ (g' ≫ b) := by rw [hab]
        _ = (R.rZ ≫ g') ≫ b := by simp
        _ = (g ≫ R.rY) ≫ b := by rw [R.r_left]
        _ = g ≫ (R.rY ≫ b) := by simp
    let d : P ⟶ T := h.desc (R.rX ≫ a) (R.rY ≫ b) hcompat
    refine ⟨R.iP ≫ d, ?_, ?_⟩
    · calc
        inl' ≫ (R.iP ≫ d) = (inl' ≫ R.iP) ≫ d := by simp
        _ = (R.iX ≫ inl) ≫ d := by rw [R.i_right]
        _ = R.iX ≫ (inl ≫ d) := by simp
        _ = R.iX ≫ (R.rX ≫ a) := by rw [h.inl_desc]
        _ = (R.iX ≫ R.rX) ≫ a := by simp
        _ = a := by rw [R.retract_x]; simp
    · calc
        inr' ≫ (R.iP ≫ d) = (inr' ≫ R.iP) ≫ d := by simp
        _ = (R.iY ≫ inr) ≫ d := by rw [R.i_bottom]
        _ = R.iY ≫ (inr ≫ d) := by simp
        _ = R.iY ≫ (R.rY ≫ b) := by rw [h.inr_desc]
        _ = (R.iY ≫ R.rY) ≫ b := by simp
        _ = b := by rw [R.retract_y]; simp

end DifferentialGeometry.Topology.VanKampen
end svkBundle_011
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/RetractPushout.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/SelectedObjects.lean
section svkBundle_012
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory Set

universe u v

namespace DifferentialGeometry.Topology.VanKampen

abbrev FundamentalGroupoidOn (Y : Type u) [TopologicalSpace Y] (A : Set Y) :=
  (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A}).objs

def selectedIn {X : Type u} (A B : Set X) : Set B := {x | x.1 ∈ A}

def fundamentalGroupoidMapOn {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {A : Set Y} {B : Set Z} (f : C(Y, Z)) (hf : MapsTo f A B) :
    FundamentalGroupoidOn Y A ⥤ FundamentalGroupoidOn Z B where
  obj x := ⟨(FundamentalGroupoid.map f).obj x.1, by
    apply (CategoryTheory.Subgroupoid.mem_full_objs_iff _).2
    exact hf ((CategoryTheory.Subgroupoid.mem_full_objs_iff
      {z : FundamentalGroupoid Y | z.as ∈ A}).1 x.2)⟩
  map {x y} g := ⟨(FundamentalGroupoid.map f).map g.1, by
    apply (CategoryTheory.Subgroupoid.mem_full_iff _).2
    constructor
    · exact hf ((CategoryTheory.Subgroupoid.mem_full_objs_iff
        {z : FundamentalGroupoid Y | z.as ∈ A}).1 x.2)
    · exact hf ((CategoryTheory.Subgroupoid.mem_full_objs_iff
        {z : FundamentalGroupoid Y | z.as ∈ A}).1 y.2)⟩
  map_id x := by apply Subtype.ext; exact (FundamentalGroupoid.map f).map_id x.1
  map_comp g h := by apply Subtype.ext; exact (FundamentalGroupoid.map f).map_comp g.1 h.1

theorem fundamentalGroupoidMapOn_comp_inclusion
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {A : Set Y} {B : Set Z} (f : C(Y, Z)) (hf : MapsTo f A B) :
    fundamentalGroupoidMapOn f hf ⋙
        CategoryTheory.Subgroupoid.hom
          (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Z | z.as ∈ B}) =
      CategoryTheory.Subgroupoid.hom
          (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A}) ⋙
        FundamentalGroupoid.map f := by
  apply Functor.hext
  · intro x
    rfl
  · intro x y g
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupoidMap_comp_representativeRetraction
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    {A : Set Y} {B : Set Z} (f : C(Y, Z)) (hf : MapsTo f A B)
    (dY : RepresentativeChoice (FundamentalGroupoid Y) {z | z.as ∈ A})
    (dZ : RepresentativeChoice (FundamentalGroupoid Z) {z | z.as ∈ B})
    (hobj : ∀ z, (FundamentalGroupoid.map f).obj (dY.normalizedObj z) =
      dZ.normalizedObj ((FundamentalGroupoid.map f).obj z))
    (hhom : ∀ z, (FundamentalGroupoid.map f).map (dY.normalizedHom z) ≍
      dZ.normalizedHom ((FundamentalGroupoid.map f).obj z)) :
    FundamentalGroupoid.map f ⋙ representativeRetraction dZ =
      representativeRetraction dY ⋙ fundamentalGroupoidMapOn f hf := by
  let J := FundamentalGroupoid.map f
  apply Functor.hext
  · intro z
    apply Subtype.ext
    exact (hobj z).symm
  · intro x y g
    have hxObj := hobj x
    have hyObj := hobj y
    have hxHom := hhom x
    have hyHom := hhom y
    have hyInv : J.map (inv (dY.normalizedHom y)) ≍
        inv (dZ.normalizedHom (J.obj y)) := by
      have hmapInv : J.map (inv (dY.normalizedHom y)) =
          inv (J.map (dY.normalizedHom y)) := by simp
      exact (heq_of_eq hmapInv).trans
        (by simpa only [Groupoid.inv_eq_inv] using
          Groupoid.inv_heq hyObj rfl hyHom)
    have hfirst : J.map (dY.normalizedHom x) ≫ J.map g ≍
        dZ.normalizedHom (J.obj x) ≫ J.map g :=
      CategoryTheory.heq_comp hxObj rfl rfl hxHom HEq.rfl
    have htotal : J.map (dY.normalizedHom x ≫ g ≫ inv (dY.normalizedHom y)) ≍
        dZ.normalizedHom (J.obj x) ≫ J.map g ≫
          inv (dZ.normalizedHom (J.obj y)) := by
      have hcomp := CategoryTheory.heq_comp hxObj rfl hyObj hfirst hyInv
      exact (heq_of_eq (by simp :
        J.map (dY.normalizedHom x ≫ g ≫ inv (dY.normalizedHom y)) =
          (J.map (dY.normalizedHom x) ≫ J.map g) ≫
            J.map (inv (dY.normalizedHom y)))).trans
        (hcomp.trans (heq_of_eq (Category.assoc _ _ _)))
    dsimp only [Functor.comp_map, representativeRetraction, fundamentalGroupoidMapOn]
    congr 1
    · exact congrArg₂ (fun a b : FundamentalGroupoid Z => a ⟶ b)
        hxObj.symm hyObj.symm
    · apply Function.hfunext
      · exact congrArg₂ (fun a b : FundamentalGroupoid Z => a ⟶ b)
          hxObj.symm hyObj.symm
      · intro q q' hq
        apply heq_of_eq
        apply propext
        simp only [CategoryTheory.Subgroupoid.mem_full_iff]
        exact iff_of_true
          ⟨dZ.normalizedObj_mem (J.obj x), dZ.normalizedObj_mem (J.obj y)⟩
          ⟨hf (dY.normalizedObj_mem x), hf (dY.normalizedObj_mem y)⟩
    · exact htotal.symm
    · exact proof_irrel_heq _ _

noncomputable def fundamentalGroupoidOnInclusionEquivalence
    {Y : Type u} [TopologicalSpace Y] {A : Set Y} (hA : IsRepresentative A) :
    FundamentalGroupoidOn Y A ≌ FundamentalGroupoid Y :=
  representativeInclusionEquivalence (representativeChoiceOfIsRepresentative hA)

def selectedInterToLeft {X : Type u} [TopologicalSpace X]
    (A U V : Set X) :
    FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V)) ⥤
      FundamentalGroupoidOn U (selectedIn A U) :=
  fundamentalGroupoidMapOn (interToLeft U V) (fun _ hx => hx)

def selectedInterToRight {X : Type u} [TopologicalSpace X]
    (A U V : Set X) :
    FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V)) ⥤
      FundamentalGroupoidOn V (selectedIn A V) :=
  fundamentalGroupoidMapOn (interToRight U V) (fun _ hx => hx)

def selectedLeftToAmbient {X : Type u} [TopologicalSpace X]
    (A U : Set X) : FundamentalGroupoidOn U (selectedIn A U) ⥤
      FundamentalGroupoidOn X A :=
  fundamentalGroupoidMapOn (subsetToAmbient U) (fun _ hx => hx)

def selectedRightToAmbient {X : Type u} [TopologicalSpace X]
    (A V : Set X) : FundamentalGroupoidOn V (selectedIn A V) ⥤
      FundamentalGroupoidOn X A :=
  fundamentalGroupoidMapOn (subsetToAmbient V) (fun _ hx => hx)

theorem selectedGroupoid_coverSquare_commutes
    {X : Type u} [TopologicalSpace X] (A U V : Set X) :
    selectedInterToLeft A U V ⋙ selectedLeftToAmbient A U =
      selectedInterToRight A U V ⋙ selectedRightToAmbient A V := by
  apply Functor.hext
  · intro z
    rfl
  · intro x y g
    apply heq_of_eq
    apply Subtype.ext
    change ((FundamentalGroupoid.map (interToLeft U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient U)).map g.1) =
      ((FundamentalGroupoid.map (interToRight U V) ⋙
        FundamentalGroupoid.map (subsetToAmbient V)).map g.1)
    exact eq_of_heq
      (Functor.hcongr_hom (fundamentalGroupoid_coverSquare_commutes U V) g.1)

def selectedGroupoidSquareIsPushoutStatement
    {X : Type u} [TopologicalSpace X] (A U V : Set X) : Prop :=
  @IsPushout Grpd.{u, u} _
    (Grpd.of (FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V))))
    (Grpd.of (FundamentalGroupoidOn U (selectedIn A U)))
    (Grpd.of (FundamentalGroupoidOn V (selectedIn A V)))
    (Grpd.of (FundamentalGroupoidOn X A))
    (selectedInterToLeft A U V)
    (selectedInterToRight A U V)
    (selectedLeftToAmbient A U)
    (selectedRightToAmbient A V)

theorem isRepresentative_of_cover {X : Type u} [TopologicalSpace X]
    {A U V : Set X} (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V)) : IsRepresentative A := by
  intro x
  have hx : x ∈ U ∪ V := by rw [hcover]; trivial
  rcases hx with hxU | hxV
  · obtain ⟨a, haA, hax⟩ := hAU ⟨x, hxU⟩
    exact ⟨a.1, haA, hax.map continuous_subtype_val⟩
  · obtain ⟨a, haA, hax⟩ := hAV ⟨x, hxV⟩
    exact ⟨a.1, haA, hax.map continuous_subtype_val⟩

noncomputable def leftRepresentativeChoice {X : Type u} [TopologicalSpace X]
    (A U V : Set X) (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U} := by
  classical
  exact {
  obj z := if hzV : z.as.1 ∈ V then
      (FundamentalGroupoid.map (interToLeft U V)).obj
        (dW.obj ⟨⟨z.as.1, z.as.2, hzV⟩⟩)
    else
      (representativeChoiceOfIsRepresentative hAU).obj z
  obj_mem z := by
    classical
    by_cases hzV : z.as.1 ∈ V
    · simp only [hzV]
      change (dW.obj ⟨⟨z.as.1, z.as.2, hzV⟩⟩).as.1 ∈ A
      exact dW.obj_mem ⟨⟨z.as.1, z.as.2, hzV⟩⟩
    · simpa [hzV] using (representativeChoiceOfIsRepresentative hAU).obj_mem z
  hom z := by
    by_cases hzV : z.as.1 ∈ V
    · exact eqToHom (by simp [hzV]) ≫
        (FundamentalGroupoid.map (interToLeft U V)).map
          (dW.hom ⟨⟨z.as.1, z.as.2, hzV⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl)
    · exact eqToHom (by simp [hzV]) ≫
        (representativeChoiceOfIsRepresentative hAU).hom z }

noncomputable def rightRepresentativeChoice {X : Type u} [TopologicalSpace X]
    (A U V : Set X) (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V} := by
  classical
  exact {
  obj z := if hzU : z.as.1 ∈ U then
      (FundamentalGroupoid.map (interToRight U V)).obj
        (dW.obj ⟨⟨z.as.1, hzU, z.as.2⟩⟩)
    else
      (representativeChoiceOfIsRepresentative hAV).obj z
  obj_mem z := by
    classical
    by_cases hzU : z.as.1 ∈ U
    · simp only [hzU]
      change (dW.obj ⟨⟨z.as.1, hzU, z.as.2⟩⟩).as.1 ∈ A
      exact dW.obj_mem ⟨⟨z.as.1, hzU, z.as.2⟩⟩
    · simpa [hzU] using (representativeChoiceOfIsRepresentative hAV).obj_mem z
  hom z := by
    by_cases hzU : z.as.1 ∈ U
    · exact eqToHom (by simp [hzU]) ≫
        (FundamentalGroupoid.map (interToRight U V)).map
          (dW.hom ⟨⟨z.as.1, hzU, z.as.2⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl)
    · exact eqToHom (by simp [hzU]) ≫
        (representativeChoiceOfIsRepresentative hAV).hom z }

noncomputable def ambientRepresentativeChoice {X : Type u} [TopologicalSpace X]
    (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V}) :
    RepresentativeChoice (FundamentalGroupoid X) {z | z.as ∈ A} := by
  classical
  exact {
  obj z := if hzU : z.as ∈ U then
      (FundamentalGroupoid.map (subsetToAmbient U)).obj (dU.obj ⟨⟨z.as, hzU⟩⟩)
    else
      (FundamentalGroupoid.map (subsetToAmbient V)).obj
        (dV.obj ⟨⟨z.as, by
          have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
          exact hz.resolve_left hzU⟩⟩)
  obj_mem z := by
    classical
    by_cases hzU : z.as ∈ U
    · simp only [hzU]
      change (dU.obj ⟨⟨z.as, hzU⟩⟩).as.1 ∈ A
      exact dU.obj_mem ⟨⟨z.as, hzU⟩⟩
    · simp only [hzU]
      change (dV.obj ⟨⟨z.as, by
        have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
        exact hz.resolve_left hzU⟩⟩).as.1 ∈ A
      exact dV.obj_mem ⟨⟨z.as, by
        have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
        exact hz.resolve_left hzU⟩⟩
  hom z := by
    by_cases hzU : z.as ∈ U
    · exact eqToHom (by simp [hzU]) ≫
        (FundamentalGroupoid.map (subsetToAmbient U)).map (dU.hom ⟨⟨z.as, hzU⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl)
    · exact eqToHom (by simp [hzU]) ≫
        (FundamentalGroupoid.map (subsetToAmbient V)).map (dV.hom ⟨⟨z.as, by
          have hz : z.as ∈ U ∪ V := by rw [hcover]; trivial
          exact hz.resolve_left hzU⟩⟩) ≫
        eqToHom (by apply FundamentalGroupoid.ext; rfl) }

set_option backward.isDefEq.respectTransparency false in
theorem interToLeft_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToLeft U V)).obj (dW.normalizedObj z) =
      (leftRepresentativeChoice A U V hAU dW).normalizedObj
        ((FundamentalGroupoid.map (interToLeft U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToLeft U V)
  let dU := leftRepresentativeChoice A U V hAU dW
  have hzV : (J.obj z).as.1 ∈ V := z.as.2.2
  have hzV' : ((interToLeft U V) z.as).1 ∈ V := z.as.2.2
  have hzw : (⟨⟨(J.obj z).as.1, (J.obj z).as.2, hzV⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  have hzw' : (⟨⟨((interToLeft U V) z.as).1,
      ((interToLeft U V) z.as).2, hzV'⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∈ {q | q.as ∈ selectedIn A U} := hzA
    rw [dW.normalizedObj_of_mem hzW, dU.normalizedObj_of_mem hzU]
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∉ {q | q.as ∈ selectedIn A U} := hzA
    unfold RepresentativeChoice.normalizedObj
    rw [ite_eq_right hzW, ite_eq_right hzU]
    change J.obj (dW.obj z) = dU.obj (J.obj z)
    simp [dU, leftRepresentativeChoice, J, hzV', hzw']

set_option backward.isDefEq.respectTransparency false in
theorem interToLeft_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToLeft U V)).map (dW.normalizedHom z) ≍
      (leftRepresentativeChoice A U V hAU dW).normalizedHom
        ((FundamentalGroupoid.map (interToLeft U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToLeft U V)
  let dU := leftRepresentativeChoice A U V hAU dW
  have hzV : (J.obj z).as.1 ∈ V := z.as.2.2
  have hzV' : ((interToLeft U V) z.as).1 ∈ V := z.as.2.2
  have hzw : (⟨⟨(J.obj z).as.1, (J.obj z).as.2, hzV⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∈ {q | q.as ∈ selectedIn A U} := hzA
    have hmap := Functor.map_heq J (dW.normalizedObj_of_mem hzW) rfl
      (dW.normalizedHom_heq_id_of_mem hzW)
    exact hmap.trans ((heq_of_eq (J.map_id z)).trans
      (dU.normalizedHom_heq_id_of_mem hzU).symm)
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzU : J.obj z ∉ {q | q.as ∈ selectedIn A U} := hzA
    have hmap := Functor.map_heq J
      (by simp [RepresentativeChoice.normalizedObj, hzW]) rfl
      (dW.normalizedHom_heq_hom_of_not_mem hzW)
    have hraw : dU.hom (J.obj z) ≍ J.map (dW.hom z) := by
      have hhom : dW.hom
          (⟨⟨(J.obj z).as.1, (J.obj z).as.2, hzV⟩⟩ :
            FundamentalGroupoid (↑(U ∩ V))) ≍ dW.hom z := by
        cases hzw
        rfl
      have hmapraw := Functor.map_heq J (congrArg dW.obj hzw) hzw hhom
      simpa [dU, leftRepresentativeChoice, J, hzV'] using hmapraw
    exact hmap.trans (hraw.symm.trans
      (dU.normalizedHom_heq_hom_of_not_mem hzU).symm)

set_option backward.isDefEq.respectTransparency false in
theorem interToLeft_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAU : IsRepresentative (selectedIn A U))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    FundamentalGroupoid.map (interToLeft U V) ⋙
        representativeRetraction (leftRepresentativeChoice A U V hAU dW) =
      representativeRetraction dW ⋙ selectedInterToLeft A U V := by
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact interToLeft_map_normalizedObj_eq A U V hAU dW
  · exact interToLeft_map_normalizedHom_heq A U V hAU dW

set_option backward.isDefEq.respectTransparency false in
theorem interToRight_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToRight U V)).obj (dW.normalizedObj z) =
      (rightRepresentativeChoice A U V hAV dW).normalizedObj
        ((FundamentalGroupoid.map (interToRight U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToRight U V)
  let dV := rightRepresentativeChoice A U V hAV dW
  have hzU : (J.obj z).as.1 ∈ U := z.as.2.1
  have hzU' : ((interToRight U V) z.as).1 ∈ U := z.as.2.1
  have hzw : (⟨⟨(J.obj z).as.1, hzU, (J.obj z).as.2⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  have hzw' : (⟨⟨((interToRight U V) z.as).1, hzU',
      ((interToRight U V) z.as).2⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∈ {q | q.as ∈ selectedIn A V} := hzA
    rw [dW.normalizedObj_of_mem hzW, dV.normalizedObj_of_mem hzV]
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∉ {q | q.as ∈ selectedIn A V} := hzA
    unfold RepresentativeChoice.normalizedObj
    rw [ite_eq_right hzW, ite_eq_right hzV]
    change J.obj (dW.obj z) = dV.obj (J.obj z)
    simp [dV, rightRepresentativeChoice, J, hzU', hzw']

set_option backward.isDefEq.respectTransparency false in
theorem interToRight_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid (↑(U ∩ V))) :
    (FundamentalGroupoid.map (interToRight U V)).map (dW.normalizedHom z) ≍
      (rightRepresentativeChoice A U V hAV dW).normalizedHom
        ((FundamentalGroupoid.map (interToRight U V)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (interToRight U V)
  let dV := rightRepresentativeChoice A U V hAV dW
  have hzU : (J.obj z).as.1 ∈ U := z.as.2.1
  have hzU' : ((interToRight U V) z.as).1 ∈ U := z.as.2.1
  have hzw : (⟨⟨(J.obj z).as.1, hzU, (J.obj z).as.2⟩⟩ :
      FundamentalGroupoid (↑(U ∩ V))) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzW : z ∈ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∈ {q | q.as ∈ selectedIn A V} := hzA
    have hmap := Functor.map_heq J (dW.normalizedObj_of_mem hzW) rfl
      (dW.normalizedHom_heq_id_of_mem hzW)
    exact hmap.trans ((heq_of_eq (J.map_id z)).trans
      (dV.normalizedHom_heq_id_of_mem hzV).symm)
  · have hzW : z ∉ {q | q.as ∈ selectedIn A (U ∩ V)} := hzA
    have hzV : J.obj z ∉ {q | q.as ∈ selectedIn A V} := hzA
    have hmap := Functor.map_heq J
      (by simp [RepresentativeChoice.normalizedObj, hzW]) rfl
      (dW.normalizedHom_heq_hom_of_not_mem hzW)
    have hraw : dV.hom (J.obj z) ≍ J.map (dW.hom z) := by
      have hhom : dW.hom
          (⟨⟨(J.obj z).as.1, hzU, (J.obj z).as.2⟩⟩ :
            FundamentalGroupoid (↑(U ∩ V))) ≍ dW.hom z := by
        cases hzw
        rfl
      have hmapraw := Functor.map_heq J (congrArg dW.obj hzw) hzw hhom
      simpa [dV, rightRepresentativeChoice, J, hzU'] using hmapraw
    exact hmap.trans (hraw.symm.trans
      (dV.normalizedHom_heq_hom_of_not_mem hzV).symm)

theorem interToRight_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    FundamentalGroupoid.map (interToRight U V) ⋙
        representativeRetraction (rightRepresentativeChoice A U V hAV dW) =
      representativeRetraction dW ⋙ selectedInterToRight A U V := by
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact interToRight_map_normalizedObj_eq A U V hAV dW
  · exact interToRight_map_normalizedHom_heq A U V hAV dW

set_option backward.isDefEq.respectTransparency false in
theorem leftToAmbient_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V})
    (z : FundamentalGroupoid U) :
    (FundamentalGroupoid.map (subsetToAmbient U)).obj (dU.normalizedObj z) =
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedObj
        ((FundamentalGroupoid.map (subsetToAmbient U)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (subsetToAmbient U)
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  have hzU : (J.obj z).as ∈ U := z.as.2
  have hzU' : (subsetToAmbient U z.as) ∈ U := z.as.2
  have hzu : (⟨⟨(J.obj z).as, hzU⟩⟩ : FundamentalGroupoid U) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  have hzu' : (⟨⟨subsetToAmbient U z.as, hzU'⟩⟩ : FundamentalGroupoid U) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzSelU : z ∈ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∈ {q | q.as ∈ A} := hzA
    rw [dU.normalizedObj_of_mem hzSelU, dX.normalizedObj_of_mem hzSelX]
  · have hzSelU : z ∉ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∉ {q | q.as ∈ A} := hzA
    unfold RepresentativeChoice.normalizedObj
    rw [ite_eq_right hzSelU, ite_eq_right hzSelX]
    change J.obj (dU.obj z) = dX.obj (J.obj z)
    simp [dX, ambientRepresentativeChoice, J, hzU', hzu']

set_option backward.isDefEq.respectTransparency false in
theorem leftToAmbient_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V})
    (z : FundamentalGroupoid U) :
    (FundamentalGroupoid.map (subsetToAmbient U)).map (dU.normalizedHom z) ≍
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedHom
        ((FundamentalGroupoid.map (subsetToAmbient U)).obj z) := by
  classical
  let J := FundamentalGroupoid.map (subsetToAmbient U)
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  have hzU : (J.obj z).as ∈ U := z.as.2
  have hzU' : (subsetToAmbient U z.as) ∈ U := z.as.2
  have hzu : (⟨⟨(J.obj z).as, hzU⟩⟩ : FundamentalGroupoid U) = z := by
    apply FundamentalGroupoid.ext
    apply Subtype.ext
    rfl
  by_cases hzA : z.as.1 ∈ A
  · have hzSelU : z ∈ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∈ {q | q.as ∈ A} := hzA
    have hmap := Functor.map_heq J (dU.normalizedObj_of_mem hzSelU) rfl
      (dU.normalizedHom_heq_id_of_mem hzSelU)
    exact hmap.trans ((heq_of_eq (J.map_id z)).trans
      (dX.normalizedHom_heq_id_of_mem hzSelX).symm)
  · have hzSelU : z ∉ {q | q.as ∈ selectedIn A U} := hzA
    have hzSelX : J.obj z ∉ {q | q.as ∈ A} := hzA
    have hmap := Functor.map_heq J
      (by simp [RepresentativeChoice.normalizedObj, hzSelU]) rfl
      (dU.normalizedHom_heq_hom_of_not_mem hzSelU)
    have hraw : dX.hom (J.obj z) ≍ J.map (dU.hom z) := by
      have hhom : dU.hom (⟨⟨(J.obj z).as, hzU⟩⟩ : FundamentalGroupoid U) ≍
          dU.hom z := by
        cases hzu
        rfl
      have hmapraw := Functor.map_heq J (congrArg dU.obj hzu) hzu hhom
      simpa [dX, ambientRepresentativeChoice, J, hzU'] using hmapraw
    exact hmap.trans (hraw.symm.trans
      (dX.normalizedHom_heq_hom_of_not_mem hzSelX).symm)

theorem leftToAmbient_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (dU : RepresentativeChoice (FundamentalGroupoid U) {z | z.as ∈ selectedIn A U})
    (dV : RepresentativeChoice (FundamentalGroupoid V) {z | z.as ∈ selectedIn A V}) :
    FundamentalGroupoid.map (subsetToAmbient U) ⋙
        representativeRetraction (ambientRepresentativeChoice A U V hcover dU dV) =
      representativeRetraction dU ⋙ selectedLeftToAmbient A U := by
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact leftToAmbient_map_normalizedObj_eq A U V hcover dU dV
  · exact leftToAmbient_map_normalizedHom_heq A U V hcover dU dV

set_option backward.isDefEq.respectTransparency false in
theorem rightToAmbient_map_normalizedObj_eq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid V) :
    let dU := leftRepresentativeChoice A U V hAU dW
    let dV := rightRepresentativeChoice A U V hAV dW
    (FundamentalGroupoid.map (subsetToAmbient V)).obj (dV.normalizedObj z) =
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedObj
        ((FundamentalGroupoid.map (subsetToAmbient V)).obj z) := by
  classical
  dsimp only
  let KWU := FundamentalGroupoid.map (interToLeft U V)
  let KWV := FundamentalGroupoid.map (interToRight U V)
  let JU := FundamentalGroupoid.map (subsetToAmbient U)
  let JV := FundamentalGroupoid.map (subsetToAmbient V)
  let dU := leftRepresentativeChoice A U V hAU dW
  let dV := rightRepresentativeChoice A U V hAV dW
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  by_cases hzU : z.as.1 ∈ U
  · let w : FundamentalGroupoid (↑(U ∩ V)) := ⟨⟨z.as.1, hzU, z.as.2⟩⟩
    have hVz : KWV.obj w = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    have hSquare (q : FundamentalGroupoid (↑(U ∩ V))) :
        JU.obj (KWU.obj q) = JV.obj (KWV.obj q) :=
      Functor.congr_obj (fundamentalGroupoid_coverSquare_commutes U V) q
    calc
      JV.obj (dV.normalizedObj z) = JV.obj (dV.normalizedObj (KWV.obj w)) :=
        congrArg (fun q => JV.obj (dV.normalizedObj q)) hVz.symm
      _ = JV.obj (KWV.obj (dW.normalizedObj w)) :=
        congrArg JV.obj (interToRight_map_normalizedObj_eq A U V hAV dW w).symm
      _ = JU.obj (KWU.obj (dW.normalizedObj w)) := (hSquare _).symm
      _ = JU.obj (dU.normalizedObj (KWU.obj w)) :=
        congrArg JU.obj (interToLeft_map_normalizedObj_eq A U V hAU dW w)
      _ = dX.normalizedObj (JU.obj (KWU.obj w)) :=
        leftToAmbient_map_normalizedObj_eq A U V hcover dU dV (KWU.obj w)
      _ = dX.normalizedObj (JV.obj z) :=
        congrArg dX.normalizedObj ((hSquare w).trans (congrArg JV.obj hVz))
  · have hzU' : (JV.obj z).as ∉ U := hzU
    have hzU'' : subsetToAmbient V z.as ∉ U := hzU
    have hzV : (JV.obj z).as ∈ V := z.as.2
    have hzV' : subsetToAmbient V z.as ∈ V := z.as.2
    have hzv : (⟨⟨(JV.obj z).as, hzV⟩⟩ : FundamentalGroupoid V) = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    have hzv' : (⟨⟨subsetToAmbient V z.as, hzV'⟩⟩ : FundamentalGroupoid V) = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    by_cases hzA : z.as.1 ∈ A
    · have hzSelV : z ∈ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∈ {q | q.as ∈ A} := hzA
      rw [dV.normalizedObj_of_mem hzSelV, dX.normalizedObj_of_mem hzSelX]
    · have hzSelV : z ∉ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∉ {q | q.as ∈ A} := hzA
      unfold RepresentativeChoice.normalizedObj
      rw [ite_eq_right hzSelV, ite_eq_right hzSelX]
      change JV.obj (dV.obj z) = dX.obj (JV.obj z)
      simp [dX, ambientRepresentativeChoice, JV, hzU'', hzv']

set_option backward.isDefEq.respectTransparency false in
theorem rightToAmbient_map_normalizedHom_heq
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)})
    (z : FundamentalGroupoid V) :
    let dU := leftRepresentativeChoice A U V hAU dW
    let dV := rightRepresentativeChoice A U V hAV dW
    (FundamentalGroupoid.map (subsetToAmbient V)).map (dV.normalizedHom z) ≍
      (ambientRepresentativeChoice A U V hcover dU dV).normalizedHom
        ((FundamentalGroupoid.map (subsetToAmbient V)).obj z) := by
  classical
  dsimp only
  let KWU := FundamentalGroupoid.map (interToLeft U V)
  let KWV := FundamentalGroupoid.map (interToRight U V)
  let JU := FundamentalGroupoid.map (subsetToAmbient U)
  let JV := FundamentalGroupoid.map (subsetToAmbient V)
  let dU := leftRepresentativeChoice A U V hAU dW
  let dV := rightRepresentativeChoice A U V hAV dW
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  by_cases hzU : z.as.1 ∈ U
  · let w : FundamentalGroupoid (↑(U ∩ V)) := ⟨⟨z.as.1, hzU, z.as.2⟩⟩
    have hVz : KWV.obj w = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    have hSquareObj (q : FundamentalGroupoid (↑(U ∩ V))) :
        JU.obj (KWU.obj q) = JV.obj (KWV.obj q) :=
      Functor.congr_obj (fundamentalGroupoid_coverSquare_commutes U V) q
    have hStart : JV.map (dV.normalizedHom z) ≍
        JV.map (dV.normalizedHom (KWV.obj w)) := by
      have htransport : dV.normalizedHom z ≍ dV.normalizedHom (KWV.obj w) := by
        cases hVz
        rfl
      exact Functor.map_heq JV
        (congrArg dV.normalizedObj hVz.symm) hVz.symm htransport
    have hRight := interToRight_map_normalizedHom_heq A U V hAV dW w
    have hThroughRight : JV.map (dV.normalizedHom (KWV.obj w)) ≍
        JV.map (KWV.map (dW.normalizedHom w)) := by
      exact Functor.map_heq JV
        (interToRight_map_normalizedObj_eq A U V hAV dW w).symm rfl hRight.symm
    have hSquare := Functor.hcongr_hom
      (fundamentalGroupoid_coverSquare_commutes U V) (dW.normalizedHom w)
    have hThroughLeft : JU.map (KWU.map (dW.normalizedHom w)) ≍
        JU.map (dU.normalizedHom (KWU.obj w)) := by
      exact Functor.map_heq JU
        (interToLeft_map_normalizedObj_eq A U V hAU dW w) rfl
        (interToLeft_map_normalizedHom_heq A U V hAU dW w)
    have hAmbient := leftToAmbient_map_normalizedHom_heq
      A U V hcover dU dV (KWU.obj w)
    have hEndpoint : JU.obj (KWU.obj w) = JV.obj z :=
      (hSquareObj w).trans (congrArg JV.obj hVz)
    have hFinish : dX.normalizedHom (JU.obj (KWU.obj w)) ≍
        dX.normalizedHom (JV.obj z) := by
      cases hEndpoint
      rfl
    exact hStart.trans (hThroughRight.trans
      (hSquare.symm.trans (hThroughLeft.trans (hAmbient.trans hFinish))))
  · have hzU' : (JV.obj z).as ∉ U := hzU
    have hzU'' : subsetToAmbient V z.as ∉ U := hzU
    have hzV : (JV.obj z).as ∈ V := z.as.2
    have hzV' : subsetToAmbient V z.as ∈ V := z.as.2
    have hzv : (⟨⟨(JV.obj z).as, hzV⟩⟩ : FundamentalGroupoid V) = z := by
      apply FundamentalGroupoid.ext
      apply Subtype.ext
      rfl
    by_cases hzA : z.as.1 ∈ A
    · have hzSelV : z ∈ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∈ {q | q.as ∈ A} := hzA
      have hmap := Functor.map_heq JV (dV.normalizedObj_of_mem hzSelV) rfl
        (dV.normalizedHom_heq_id_of_mem hzSelV)
      exact hmap.trans ((heq_of_eq (JV.map_id z)).trans
        (dX.normalizedHom_heq_id_of_mem hzSelX).symm)
    · have hzSelV : z ∉ {q | q.as ∈ selectedIn A V} := hzA
      have hzSelX : JV.obj z ∉ {q | q.as ∈ A} := hzA
      have hmap := Functor.map_heq JV
        (by simp [RepresentativeChoice.normalizedObj, hzSelV]) rfl
        (dV.normalizedHom_heq_hom_of_not_mem hzSelV)
      have hraw : dX.hom (JV.obj z) ≍ JV.map (dV.hom z) := by
        have hhom : dV.hom (⟨⟨(JV.obj z).as, hzV⟩⟩ : FundamentalGroupoid V) ≍
            dV.hom z := by
          cases hzv
          rfl
        have hmapraw := Functor.map_heq JV (congrArg dV.obj hzv) hzv hhom
        simpa [dX, ambientRepresentativeChoice, JV, hzU'', hzV'] using hmapraw
      exact hmap.trans (hraw.symm.trans
        (dX.normalizedHom_heq_hom_of_not_mem hzSelX).symm)

theorem rightToAmbient_comp_representativeRetraction
    {X : Type u} [TopologicalSpace X] (A U V : Set X) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (dW : RepresentativeChoice (FundamentalGroupoid (↑(U ∩ V)))
      {z | z.as ∈ selectedIn A (U ∩ V)}) :
    let dU := leftRepresentativeChoice A U V hAU dW
    let dV := rightRepresentativeChoice A U V hAV dW
    FundamentalGroupoid.map (subsetToAmbient V) ⋙
        representativeRetraction (ambientRepresentativeChoice A U V hcover dU dV) =
      representativeRetraction dV ⋙ selectedRightToAmbient A V := by
  dsimp only
  apply fundamentalGroupoidMap_comp_representativeRetraction
  · exact rightToAmbient_map_normalizedObj_eq A U V hcover hAU hAV dW
  · exact rightToAmbient_map_normalizedHom_heq A U V hcover hAU hAV dW

theorem seifertVanKampenOn {X : Type u} [TopologicalSpace X] (A U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hAU : IsRepresentative (selectedIn A U))
    (hAV : IsRepresentative (selectedIn A V))
    (hAW : IsRepresentative (selectedIn A (U ∩ V))) :
    selectedGroupoidSquareIsPushoutStatement A U V := by
  let dW := representativeChoiceOfIsRepresentative hAW
  let dU := leftRepresentativeChoice A U V hAU dW
  let dV := rightRepresentativeChoice A U V hAV dW
  let dX := ambientRepresentativeChoice A U V hcover dU dV
  let iW := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full
      {z : FundamentalGroupoid (↑(U ∩ V)) | z.as ∈ selectedIn A (U ∩ V)})
  let iU := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid U | z.as ∈ selectedIn A U})
  let iV := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid V | z.as ∈ selectedIn A V})
  let iX := CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid X | z.as ∈ A})
  let R : @CommSqRetract Grpd.{u, u} _
      (Grpd.of (FundamentalGroupoidOn (↑(U ∩ V)) (selectedIn A (U ∩ V))))
      (Grpd.of (FundamentalGroupoidOn U (selectedIn A U)))
      (Grpd.of (FundamentalGroupoidOn V (selectedIn A V)))
      (Grpd.of (FundamentalGroupoidOn X A))
      (Grpd.of (FundamentalGroupoid (↑(U ∩ V))))
      (Grpd.of (FundamentalGroupoid U))
      (Grpd.of (FundamentalGroupoid V))
      (Grpd.of (FundamentalGroupoid X))
      (selectedInterToLeft A U V) (selectedInterToRight A U V)
      (selectedLeftToAmbient A U) (selectedRightToAmbient A V)
      (FundamentalGroupoid.map (interToLeft U V))
      (FundamentalGroupoid.map (interToRight U V))
      (FundamentalGroupoid.map (subsetToAmbient U))
      (FundamentalGroupoid.map (subsetToAmbient V)) := {
    small := { w := by exact selectedGroupoid_coverSquare_commutes A U V }
    iZ := iW
    iX := iU
    iY := iV
    iP := iX
    rZ := representativeRetraction dW
    rX := representativeRetraction dU
    rY := representativeRetraction dV
    rP := representativeRetraction dX
    retract_z := inclusion_comp_representativeRetraction dW
    retract_x := inclusion_comp_representativeRetraction dU
    retract_y := inclusion_comp_representativeRetraction dV
    retract_p := inclusion_comp_representativeRetraction dX
    i_top := (fundamentalGroupoidMapOn_comp_inclusion (interToLeft U V) _).symm
    i_left := (fundamentalGroupoidMapOn_comp_inclusion (interToRight U V) _).symm
    i_right := (fundamentalGroupoidMapOn_comp_inclusion (subsetToAmbient U) _).symm
    i_bottom := (fundamentalGroupoidMapOn_comp_inclusion (subsetToAmbient V) _).symm
    r_top := interToLeft_comp_representativeRetraction A U V hAU dW
    r_left := interToRight_comp_representativeRetraction A U V hAV dW
    r_right := leftToAmbient_comp_representativeRetraction A U V hcover dU dV
    r_bottom := rightToAmbient_comp_representativeRetraction A U V hcover hAU hAV dW }
  unfold selectedGroupoidSquareIsPushoutStatement
  exact R.isPushout (seifertVanKampen U V hU hV hcover)

end DifferentialGeometry.Topology.VanKampen
end svkBundle_012
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/SelectedObjects.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/Based.lean
section svkBundle_013
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory Set

universe u v w t

namespace DifferentialGeometry.Topology.VanKampen

@[simp] theorem fullSubgroupoid_coe_id {C : Type u} [Groupoid C]
    (D : Set C) (x : (CategoryTheory.Subgroupoid.full D).objs) :
    (𝟙 x : x ⟶ x).1 = 𝟙 x.1 := rfl

@[simp] theorem fullSubgroupoid_coe_comp {C : Type u} [Groupoid C]
    (D : Set C) {x y z : (CategoryTheory.Subgroupoid.full D).objs}
    (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g : x ⟶ z).1 = f.1 ≫ g.1 := rfl

theorem fullSubgroupoid_coe_eqToHom {C : Type u} [Groupoid C]
    (D : Set C) {x y : (CategoryTheory.Subgroupoid.full D).objs} (h : x = y) :
    (eqToHom h : x ⟶ y).1 = eqToHom (congrArg Subtype.val h) := by
  exact eqToHom_map (CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full D)) h

@[instance_reducible] def uliftGroupoid (C : Type t) [Groupoid.{v} C] :
    Groupoid.{v} (ULift.{w} C) where
  toCategory := CategoryTheory.uliftCategory C
  inv f := Groupoid.inv f
  inv_comp f := Groupoid.inv_comp f
  comp_inv f := Groupoid.comp_inv f

def pointedSelectedObject {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) : FundamentalGroupoidOn Y A :=
  ⟨FundamentalGroupoid.mk y₀, by
    rw [CategoryTheory.Subgroupoid.mem_full_objs_iff]
    exact hy₀⟩

theorem selectedObject_eq_pointed {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀)
    (z : FundamentalGroupoidOn Y A) : z = pointedSelectedObject A y₀ hy₀ := by
  apply Subtype.ext
  apply FundamentalGroupoid.ext
  change z.1.as = y₀
  exact huniq z.1.as ((CategoryTheory.Subgroupoid.mem_full_objs_iff
    {z : FundamentalGroupoid Y | z.as ∈ A}).1 z.2)

noncomputable def pointedDeloopingFunctor {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀) :
    FundamentalGroupoidOn Y A ⥤ SingleObj (FundamentalGroup Y y₀) where
  obj _ := SingleObj.star _
  map {x y} f :=
    (eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq x).symm ≫ f ≫
      eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq y)).1
  map_id x := by
    have hx := selectedObject_eq_pointed A y₀ hy₀ huniq x
    subst x
    simp
    rfl
  map_comp {x y z} f g := by
    have hx := selectedObject_eq_pointed A y₀ hy₀ huniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ huniq y
    have hz := selectedObject_eq_pointed A y₀ hy₀ huniq z
    subst x
    subst y
    subst z
    simp
    rfl

noncomputable def pointedDeloopingInverse {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) :
    SingleObj (FundamentalGroup Y y₀) ⥤ FundamentalGroupoidOn Y A where
  obj _ := pointedSelectedObject A y₀ hy₀
  map f := ⟨f, by
    apply (CategoryTheory.Subgroupoid.mem_full_iff _).2
    constructor <;> exact hy₀⟩
  map_id _ := by
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply Subtype.ext
    rfl

theorem pointedDelooping_inv_hom_id {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀) :
    pointedDeloopingInverse A y₀ hy₀ ⋙ pointedDeloopingFunctor A y₀ hy₀ huniq =
      𝟭 (SingleObj (FundamentalGroup Y y₀)) := by
  apply Functor.hext
  · intro z
    exact Subsingleton.elim _ _
  · intro x y f
    have hx : x = SingleObj.star _ := Subsingleton.elim _ _
    have hy : y = SingleObj.star _ := Subsingleton.elim _ _
    subst x
    subst y
    apply heq_of_eq
    change
      (eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq
          (pointedSelectedObject A y₀ hy₀)).symm ≫
        (⟨f, by
          apply (CategoryTheory.Subgroupoid.mem_full_iff _).2
          constructor <;> exact hy₀⟩ :
            pointedSelectedObject A y₀ hy₀ ⟶ pointedSelectedObject A y₀ hy₀) ≫
        eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq
          (pointedSelectedObject A y₀ hy₀))).1 = f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

theorem pointedDelooping_hom_inv_id {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀) :
    pointedDeloopingFunctor A y₀ hy₀ huniq ⋙ pointedDeloopingInverse A y₀ hy₀ =
      𝟭 (FundamentalGroupoidOn Y A) := by
  apply Functor.hext
  · intro z
    exact (selectedObject_eq_pointed A y₀ hy₀ huniq z).symm
  · intro x y f
    have hx := selectedObject_eq_pointed A y₀ hy₀ huniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ huniq y
    subst x
    subst y
    apply heq_of_eq
    apply Subtype.ext
    simp [pointedDeloopingFunctor, pointedDeloopingInverse]

theorem fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (f : C(Y, Z)) (hf : MapsTo f A B)
    (hBuniq : ∀ z ∈ B, z = f y₀) :
    fundamentalGroupoidMapOn f hf ⋙
        pointedDeloopingFunctor B (f y₀) (hf hy₀) hBuniq =
      pointedDeloopingFunctor A y₀ hy₀ hAuniq ⋙
        (FundamentalGroup.map f y₀).toFunctor := by
  apply Functor.hext
  · intro z
    exact Subsingleton.elim _ _
  · intro x y g
    have hx := selectedObject_eq_pointed A y₀ hy₀ hAuniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ hAuniq y
    subst x
    subst y
    let pA := pointedSelectedObject A y₀ hy₀
    let pB := pointedSelectedObject B (f y₀) (hf hy₀)
    let J := fundamentalGroupoidMapOn f hf
    let iA := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A})
    let iB := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Z | z.as ∈ B})
    have q : J.obj pA = pB :=
      selectedObject_eq_pointed B (f y₀) (hf hy₀) hBuniq _
    have r : pA = pA := selectedObject_eq_pointed A y₀ hy₀ hAuniq pA
    have hBconj :
        (eqToHom q.symm ≫ J.map g ≫ eqToHom q) ≍ J.map g :=
      (conj_eqToHom_iff_heq' _ _ q.symm q).1 rfl
    have hBunder :
        iB.map (eqToHom q.symm ≫ J.map g ≫ eqToHom q) ≍ iB.map (J.map g) :=
      Functor.map_heq iB q.symm q.symm hBconj
    have hAconj :
        (eqToHom r.symm ≫ g ≫ eqToHom r) ≍ g :=
      (conj_eqToHom_iff_heq' _ _ r.symm r).1 rfl
    have hAunder :
        iA.map (eqToHom r.symm ≫ g ≫ eqToHom r) ≍ iA.map g :=
      Functor.map_heq iA r.symm r.symm hAconj
    have hAmap := Functor.map_heq (FundamentalGroupoid.map f)
      (congrArg iA.obj r.symm) (congrArg iA.obj r.symm) hAunder
    exact hBunder.trans hAmap.symm

theorem fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (z₀ : Z) (hz₀ : z₀ ∈ B)
    (hBuniq : ∀ z ∈ B, z = z₀) (f : C(Y, Z)) (hf : MapsTo f A B)
    (hbase : f y₀ = z₀) :
    fundamentalGroupoidMapOn f hf ⋙ pointedDeloopingFunctor B z₀ hz₀ hBuniq =
      pointedDeloopingFunctor A y₀ hy₀ hAuniq ⋙
        (FundamentalGroup.mapOfEq f hbase).toFunctor := by
  apply Functor.hext
  · intro z
    exact Subsingleton.elim _ _
  · intro x y g
    have hx := selectedObject_eq_pointed A y₀ hy₀ hAuniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ hAuniq y
    subst x
    subst y
    let pA := pointedSelectedObject A y₀ hy₀
    let pB := pointedSelectedObject B z₀ hz₀
    let J := fundamentalGroupoidMapOn f hf
    let iA := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A})
    let iB := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Z | z.as ∈ B})
    have q : J.obj pA = pB := selectedObject_eq_pointed B z₀ hz₀ hBuniq _
    have r : pA = pA := selectedObject_eq_pointed A y₀ hy₀ hAuniq pA
    have hBconj : (eqToHom q.symm ≫ J.map g ≫ eqToHom q) ≍ J.map g :=
      (conj_eqToHom_iff_heq' _ _ q.symm q).1 rfl
    have hBunder :
        iB.map (eqToHom q.symm ≫ J.map g ≫ eqToHom q) ≍ iB.map (J.map g) :=
      Functor.map_heq iB q.symm q.symm hBconj
    have hAconj : (eqToHom r.symm ≫ g ≫ eqToHom r) ≍ g :=
      (conj_eqToHom_iff_heq' _ _ r.symm r).1 rfl
    have hAunder : iA.map (eqToHom r.symm ≫ g ≫ eqToHom r) ≍ iA.map g :=
      Functor.map_heq iA r.symm r.symm hAconj
    have hAmap := Functor.map_heq (FundamentalGroupoid.map f)
      (congrArg iA.obj r.symm) (congrArg iA.obj r.symm) hAunder
    have hcast (p : FundamentalGroup Y y₀) :
        FundamentalGroup.mapOfEq f hbase p ≍ FundamentalGroup.map f y₀ p := by
      rw [FundamentalGroup.mapOfEq_apply]
      exact Path.Homotopic.Quotient.cast_heq hbase.symm hbase.symm
    exact hBunder.trans
      ((hcast ((pointedDeloopingFunctor A y₀ hy₀ hAuniq).map g)).trans hAmap).symm

theorem fundamentalGroup_to_pointedDeloopingInverse_comp
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (f : C(Y, Z)) (hf : MapsTo f A B)
    (hBuniq : ∀ z ∈ B, z = f y₀) :
    (FundamentalGroup.map f y₀).toFunctor ⋙
        pointedDeloopingInverse B (f y₀) (hf hy₀) =
      pointedDeloopingInverse A y₀ hy₀ ⋙ fundamentalGroupoidMapOn f hf := by
  let DA := pointedDeloopingFunctor A y₀ hy₀ hAuniq
  let DB := pointedDeloopingFunctor B (f y₀) (hf hy₀) hBuniq
  let EA := pointedDeloopingInverse A y₀ hy₀
  let EB := pointedDeloopingInverse B (f y₀) (hf hy₀)
  let J := fundamentalGroupoidMapOn f hf
  let m := (FundamentalGroup.map f y₀).toFunctor
  change m ⋙ EB = EA ⋙ J
  calc
    m ⋙ EB = (𝟭 _) ⋙ m ⋙ EB := rfl
    _ = (EA ⋙ DA) ⋙ m ⋙ EB := by
      rw [pointedDelooping_inv_hom_id A y₀ hy₀ hAuniq]
    _ = EA ⋙ (DA ⋙ m) ⋙ EB := rfl
    _ = EA ⋙ (J ⋙ DB) ⋙ EB := by
      rw [fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor
        A B y₀ hy₀ hAuniq f hf hBuniq]
    _ = EA ⋙ J ⋙ (DB ⋙ EB) := rfl
    _ = EA ⋙ J ⋙ 𝟭 _ := by
      rw [pointedDelooping_hom_inv_id B (f y₀) (hf hy₀) hBuniq]
    _ = EA ⋙ J := rfl

theorem fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (z₀ : Z) (hz₀ : z₀ ∈ B)
    (hBuniq : ∀ z ∈ B, z = z₀) (f : C(Y, Z)) (hf : MapsTo f A B)
    (hbase : f y₀ = z₀) :
    (FundamentalGroup.mapOfEq f hbase).toFunctor ⋙
        pointedDeloopingInverse B z₀ hz₀ =
      pointedDeloopingInverse A y₀ hy₀ ⋙ fundamentalGroupoidMapOn f hf := by
  let DA := pointedDeloopingFunctor A y₀ hy₀ hAuniq
  let DB := pointedDeloopingFunctor B z₀ hz₀ hBuniq
  let EA := pointedDeloopingInverse A y₀ hy₀
  let EB := pointedDeloopingInverse B z₀ hz₀
  let J := fundamentalGroupoidMapOn f hf
  let m := (FundamentalGroup.mapOfEq f hbase).toFunctor
  change m ⋙ EB = EA ⋙ J
  calc
    m ⋙ EB = (𝟭 _) ⋙ m ⋙ EB := rfl
    _ = (EA ⋙ DA) ⋙ m ⋙ EB := by
      rw [pointedDelooping_inv_hom_id A y₀ hy₀ hAuniq]
    _ = EA ⋙ (DA ⋙ m) ⋙ EB := rfl
    _ = EA ⋙ (J ⋙ DB) ⋙ EB := by
      rw [fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
        A B y₀ hy₀ hAuniq z₀ hz₀ hBuniq f hf hbase]
    _ = EA ⋙ J ⋙ (DB ⋙ EB) := rfl
    _ = EA ⋙ J ⋙ 𝟭 _ := by
      rw [pointedDelooping_hom_inv_id B z₀ hz₀ hBuniq]
    _ = EA ⋙ J := rfl

abbrev overlapBasepoint {X : Type u} (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) : ↑(U ∩ V) :=
  ⟨x₀, hx₀⟩

abbrev leftBasepoint {X : Type u} (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) : U := ⟨x₀, hx₀⟩

abbrev rightBasepoint {X : Type u} (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) : V := ⟨x₀, hx₀⟩

theorem interToLeft_overlapBasepoint {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    (interToLeft U V) (overlapBasepoint U V x₀ hx₀) = leftBasepoint U x₀ hx₀.1 := rfl

theorem interToRight_overlapBasepoint {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    (interToRight U V) (overlapBasepoint U V x₀ hx₀) = rightBasepoint V x₀ hx₀.2 := rfl

theorem leftBasepoint_toAmbient {X : Type u} [TopologicalSpace X]
    (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    (subsetToAmbient U) (leftBasepoint U x₀ hx₀) = x₀ := rfl

theorem rightBasepoint_toAmbient {X : Type u} [TopologicalSpace X]
    (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    (subsetToAmbient V) (rightBasepoint V x₀ hx₀) = x₀ := rfl

theorem fundamentalGroup_mapOfEq_heq_map
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y₀ : Y) (z₀ : Z) (hbase : f y₀ = z₀)
    (p : FundamentalGroup Y y₀) :
    FundamentalGroup.mapOfEq f hbase p ≍ FundamentalGroup.map f y₀ p := by
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_heq hbase.symm hbase.symm

noncomputable def fundamentalGroupInterToLeft {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (interToLeft U V)
    (interToLeft_overlapBasepoint U V x₀ hx₀))

noncomputable def fundamentalGroupInterToRight {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (interToRight U V)
    (interToRight_overlapBasepoint U V x₀ hx₀))

noncomputable def fundamentalGroupLeftToAmbient {X : Type u} [TopologicalSpace X]
    (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (subsetToAmbient U)
    (leftBasepoint_toAmbient U x₀ hx₀))

noncomputable def fundamentalGroupRightToAmbient {X : Type u} [TopologicalSpace X]
    (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (subsetToAmbient V)
    (rightBasepoint_toAmbient V x₀ hx₀))

theorem fundamentalGroup_coverSquare_commutes {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupInterToLeft U V x₀ hx₀ ≫
        fundamentalGroupLeftToAmbient U x₀ hx₀.1 =
      fundamentalGroupInterToRight U V x₀ hx₀ ≫
        fundamentalGroupRightToAmbient V x₀ hx₀.2 := by
  apply GrpCat.ext
  intro p
  let hLU := interToLeft_overlapBasepoint U V x₀ hx₀
  let hRV := interToRight_overlapBasepoint U V x₀ hx₀
  let hUX := leftBasepoint_toAmbient U x₀ hx₀.1
  let hVX := rightBasepoint_toAmbient V x₀ hx₀.2
  have hInterL := fundamentalGroup_mapOfEq_heq_map
    (interToLeft U V) (overlapBasepoint U V x₀ hx₀)
      (leftBasepoint U x₀ hx₀.1) hLU p
  have hLeft := fundamentalGroup_mapOfEq_heq_map
    (subsetToAmbient U) (leftBasepoint U x₀ hx₀.1) x₀ hUX
      (FundamentalGroup.mapOfEq (interToLeft U V) hLU p)
  have hLeftMap := Functor.map_heq (FundamentalGroupoid.map (subsetToAmbient U))
    (congrArg FundamentalGroupoid.mk hLU.symm)
    (congrArg FundamentalGroupoid.mk hLU.symm) hInterL
  have hInterR := fundamentalGroup_mapOfEq_heq_map
    (interToRight U V) (overlapBasepoint U V x₀ hx₀)
      (rightBasepoint V x₀ hx₀.2) hRV p
  have hRight := fundamentalGroup_mapOfEq_heq_map
    (subsetToAmbient V) (rightBasepoint V x₀ hx₀.2) x₀ hVX
      (FundamentalGroup.mapOfEq (interToRight U V) hRV p)
  have hRightMap := Functor.map_heq (FundamentalGroupoid.map (subsetToAmbient V))
    (congrArg FundamentalGroupoid.mk hRV.symm)
    (congrArg FundamentalGroupoid.mk hRV.symm) hInterR
  have hSquare := Functor.hcongr_hom (fundamentalGroupoid_coverSquare_commutes U V) p
  exact eq_of_heq ((hLeft.trans hLeftMap).trans (hSquare.trans (hRight.trans hRightMap).symm))

def basedGroupSquareIsPushoutStatement {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) : Prop :=
  IsPushout
    (fundamentalGroupInterToLeft U V x₀ hx₀)
    (fundamentalGroupInterToRight U V x₀ hx₀)
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1)
    (fundamentalGroupRightToAmbient V x₀ hx₀.2)

theorem selectedIn_singleton_mem {X : Type u} (B : Set X) (x₀ : X) (hx₀ : x₀ ∈ B) :
    leftBasepoint B x₀ hx₀ ∈ selectedIn ({x₀} : Set X) B := by
  rfl

theorem eq_basepoint_of_mem_selectedIn_singleton {X : Type u}
    (B : Set X) (x₀ : X) (hx₀ : x₀ ∈ B) (y : B)
    (hy : y ∈ selectedIn ({x₀} : Set X) B) : y = leftBasepoint B x₀ hx₀ := by
  apply Subtype.ext
  exact hy

theorem selectedIn_singleton_isRepresentative {X : Type u} [TopologicalSpace X]
    (B : Set X) [PathConnectedSpace B] (x₀ : X) (hx₀ : x₀ ∈ B) :
    IsRepresentative (selectedIn ({x₀} : Set X) B) := by
  intro y
  exact ⟨leftBasepoint B x₀ hx₀, selectedIn_singleton_mem B x₀ hx₀,
    PathConnectedSpace.joined _ _⟩

theorem selectedInterToLeft_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    selectedInterToLeft ({x₀} : Set X) U V ⋙
        pointedDeloopingFunctor (selectedIn ({x₀} : Set X) U)
          (leftBasepoint U x₀ hx₀.1) (selectedIn_singleton_mem U x₀ hx₀.1)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀.1 y hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) (U ∩ V))
          (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton
            (U ∩ V) x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (interToLeft U V)
          (interToLeft_overlapBasepoint U V x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) (U ∩ V)) (selectedIn ({x₀} : Set X) U)
    (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton (U ∩ V) x₀ hx₀ y hy)
    (leftBasepoint U x₀ hx₀.1) (selectedIn_singleton_mem U x₀ hx₀.1)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀.1 y hy)
    (interToLeft U V) (fun _ h => h) (interToLeft_overlapBasepoint U V x₀ hx₀)

theorem selectedInterToRight_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    selectedInterToRight ({x₀} : Set X) U V ⋙
        pointedDeloopingFunctor (selectedIn ({x₀} : Set X) V)
          (rightBasepoint V x₀ hx₀.2) (selectedIn_singleton_mem V x₀ hx₀.2)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀.2 y hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) (U ∩ V))
          (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton
            (U ∩ V) x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (interToRight U V)
          (interToRight_overlapBasepoint U V x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) (U ∩ V)) (selectedIn ({x₀} : Set X) V)
    (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton (U ∩ V) x₀ hx₀ y hy)
    (rightBasepoint V x₀ hx₀.2) (selectedIn_singleton_mem V x₀ hx₀.2)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀.2 y hy)
    (interToRight U V) (fun _ h => h) (interToRight_overlapBasepoint U V x₀ hx₀)

theorem selectedLeftToAmbient_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    selectedLeftToAmbient ({x₀} : Set X) U ⋙
        pointedDeloopingFunctor ({x₀} : Set X) x₀ (Set.mem_singleton x₀)
          (fun _ hy => hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) U)
          (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (subsetToAmbient U)
          (leftBasepoint_toAmbient U x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) U) ({x₀} : Set X)
    (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient U) (fun _ h => h) (leftBasepoint_toAmbient U x₀ hx₀)

theorem selectedRightToAmbient_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    selectedRightToAmbient ({x₀} : Set X) V ⋙
        pointedDeloopingFunctor ({x₀} : Set X) x₀ (Set.mem_singleton x₀)
          (fun _ hy => hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) V)
          (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (subsetToAmbient V)
          (rightBasepoint_toAmbient V x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) V) ({x₀} : Set X)
    (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient V) (fun _ h => h) (rightBasepoint_toAmbient V x₀ hx₀)

theorem fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse
    {X : Type u} [TopologicalSpace X] (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    (FundamentalGroup.mapOfEq (subsetToAmbient U)
        (leftBasepoint_toAmbient U x₀ hx₀)).toFunctor ⋙
        pointedDeloopingInverse ({x₀} : Set X) x₀ (Set.mem_singleton x₀) =
      pointedDeloopingInverse (selectedIn ({x₀} : Set X) U)
          (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀) ⋙
        selectedLeftToAmbient ({x₀} : Set X) U := by
  exact fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp
    (selectedIn ({x₀} : Set X) U) ({x₀} : Set X)
    (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient U) (fun _ h => h) (leftBasepoint_toAmbient U x₀ hx₀)

theorem fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse
    {X : Type u} [TopologicalSpace X] (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    (FundamentalGroup.mapOfEq (subsetToAmbient V)
        (rightBasepoint_toAmbient V x₀ hx₀)).toFunctor ⋙
        pointedDeloopingInverse ({x₀} : Set X) x₀ (Set.mem_singleton x₀) =
      pointedDeloopingInverse (selectedIn ({x₀} : Set X) V)
          (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀) ⋙
        selectedRightToAmbient ({x₀} : Set X) V := by
  exact fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp
    (selectedIn ({x₀} : Set X) V) ({x₀} : Set X)
    (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient V) (fun _ h => h) (rightBasepoint_toAmbient V x₀ hx₀)

theorem fundamentalGroup_isPushout {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    basedGroupSquareIsPushoutStatement U V x₀ hx₀ := by
  let AW := selectedIn ({x₀} : Set X) (U ∩ V)
  let AU := selectedIn ({x₀} : Set X) U
  let AV := selectedIn ({x₀} : Set X) V
  let AX : Set X := {x₀}
  let w₀ := overlapBasepoint U V x₀ hx₀
  let u₀ := leftBasepoint U x₀ hx₀.1
  let v₀ := rightBasepoint V x₀ hx₀.2
  have hw₀ : w₀ ∈ AW := selectedIn_singleton_mem (U ∩ V) x₀ hx₀
  have hu₀ : u₀ ∈ AU := selectedIn_singleton_mem U x₀ hx₀.1
  have hv₀ : v₀ ∈ AV := selectedIn_singleton_mem V x₀ hx₀.2
  have hx₀A : x₀ ∈ AX := Set.mem_singleton x₀
  have hWuniq : ∀ y ∈ AW, y = w₀ := fun y hy =>
    eq_basepoint_of_mem_selectedIn_singleton (U ∩ V) x₀ hx₀ y hy
  have hUuniq : ∀ y ∈ AU, y = u₀ := fun y hy =>
    eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀.1 y hy
  have hVuniq : ∀ y ∈ AV, y = v₀ := fun y hy =>
    eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀.2 y hy
  have hXuniq : ∀ y ∈ AX, y = x₀ := fun _ hy => hy
  let DW := pointedDeloopingFunctor AW w₀ hw₀ hWuniq
  let DU := pointedDeloopingFunctor AU u₀ hu₀ hUuniq
  let DV := pointedDeloopingFunctor AV v₀ hv₀ hVuniq
  let DX := pointedDeloopingFunctor AX x₀ hx₀A hXuniq
  let EU := pointedDeloopingInverse AU u₀ hu₀
  let EV := pointedDeloopingInverse AV v₀ hv₀
  let EX := pointedDeloopingInverse AX x₀ hx₀A
  let mWU := (FundamentalGroup.mapOfEq (interToLeft U V)
    (interToLeft_overlapBasepoint U V x₀ hx₀)).toFunctor
  let mWV := (FundamentalGroup.mapOfEq (interToRight U V)
    (interToRight_overlapBasepoint U V x₀ hx₀)).toFunctor
  let mUX := (FundamentalGroup.mapOfEq (subsetToAmbient U)
    (leftBasepoint_toAmbient U x₀ hx₀.1)).toFunctor
  let mVX := (FundamentalGroup.mapOfEq (subsetToAmbient V)
    (rightBasepoint_toAmbient V x₀ hx₀.2)).toFunctor
  have hselected := seifertVanKampenOn ({x₀} : Set X) U V hU hV hcover
    (selectedIn_singleton_isRepresentative U x₀ hx₀.1)
    (selectedIn_singleton_isRepresentative V x₀ hx₀.2)
    (selectedIn_singleton_isRepresentative (U ∩ V) x₀ hx₀)
  unfold basedGroupSquareIsPushoutStatement
  apply IsPushout.mk' (fundamentalGroup_coverSquare_commutes U V x₀ hx₀)
  · intro T φ φ' hφU hφV
    let _ : Groupoid (ULift.{u} (SingleObj T)) := uliftGroupoid (SingleObj T)
    let upT : SingleObj T ⥤ ULift.{u} (SingleObj T) := ULift.upFunctor
    let Pφ := DX ⋙ φ.hom.toFunctor ⋙ upT
    let Pφ' := DX ⋙ φ'.hom.toFunctor ⋙ upT
    have hUfun : mUX ⋙ φ.hom.toFunctor = mUX ⋙ φ'.hom.toFunctor := by
      simpa only [mUX, fundamentalGroupLeftToAmbient, GrpCat.hom_ofHom,
        GrpCat.hom_comp, MonoidHom.comp_toFunctor] using
        congrArg (fun k => k.hom.toFunctor) hφU
    have hVfun : mVX ⋙ φ.hom.toFunctor = mVX ⋙ φ'.hom.toFunctor := by
      simpa only [mVX, fundamentalGroupRightToAmbient, GrpCat.hom_ofHom,
        GrpCat.hom_comp, MonoidHom.comp_toFunctor] using
        congrArg (fun k => k.hom.toFunctor) hφV
    have hleft :
        selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ =
          selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ' := by
      calc
        selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ =
            (selectedLeftToAmbient ({x₀} : Set X) U ⋙ DX) ⋙
              φ.hom.toFunctor ⋙ upT := rfl
        _ = (DU ⋙ mUX) ⋙ φ.hom.toFunctor ⋙ upT := by
          rw [selectedLeftToAmbient_comp_pointedDelooping U x₀ hx₀.1]
        _ = DU ⋙ (mUX ⋙ φ.hom.toFunctor) ⋙ upT := rfl
        _ = DU ⋙ (mUX ⋙ φ'.hom.toFunctor) ⋙ upT := by rw [hUfun]
        _ = (DU ⋙ mUX) ⋙ φ'.hom.toFunctor ⋙ upT := rfl
        _ = (selectedLeftToAmbient ({x₀} : Set X) U ⋙ DX) ⋙
              φ'.hom.toFunctor ⋙ upT := by
          rw [selectedLeftToAmbient_comp_pointedDelooping U x₀ hx₀.1]
        _ = selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ' := rfl
    have hright :
        selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ =
          selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ' := by
      calc
        selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ =
            (selectedRightToAmbient ({x₀} : Set X) V ⋙ DX) ⋙
              φ.hom.toFunctor ⋙ upT := rfl
        _ = (DV ⋙ mVX) ⋙ φ.hom.toFunctor ⋙ upT := by
          rw [selectedRightToAmbient_comp_pointedDelooping V x₀ hx₀.2]
        _ = DV ⋙ (mVX ⋙ φ.hom.toFunctor) ⋙ upT := rfl
        _ = DV ⋙ (mVX ⋙ φ'.hom.toFunctor) ⋙ upT := by rw [hVfun]
        _ = (DV ⋙ mVX) ⋙ φ'.hom.toFunctor ⋙ upT := rfl
        _ = (selectedRightToAmbient ({x₀} : Set X) V ⋙ DX) ⋙
              φ'.hom.toFunctor ⋙ upT := by
          rw [selectedRightToAmbient_comp_pointedDelooping V x₀ hx₀.2]
        _ = selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ' := rfl
    have hP : Pφ = Pφ' := hselected.hom_ext
      (W := Grpd.of (ULift.{u} (SingleObj T))) hleft hright
    have hup : φ.hom.toFunctor ⋙ upT = φ'.hom.toFunctor ⋙ upT := by
      calc
        φ.hom.toFunctor ⋙ upT = (𝟭 _) ⋙ φ.hom.toFunctor ⋙ upT := rfl
        _ = (EX ⋙ DX) ⋙ φ.hom.toFunctor ⋙ upT := by
          rw [pointedDelooping_inv_hom_id AX x₀ hx₀A hXuniq]
        _ = EX ⋙ Pφ := rfl
        _ = EX ⋙ Pφ' := by rw [hP]
        _ = (EX ⋙ DX) ⋙ φ'.hom.toFunctor ⋙ upT := rfl
        _ = (𝟭 _) ⋙ φ'.hom.toFunctor ⋙ upT := by
          rw [pointedDelooping_inv_hom_id AX x₀ hx₀A hXuniq]
        _ = φ'.hom.toFunctor ⋙ upT := rfl
    have hdown := congrArg (fun F => F ⋙ ULift.downFunctor) hup
    have hsingle : φ.hom.toFunctor = φ'.hom.toFunctor := by
      change φ.hom.toFunctor = φ'.hom.toFunctor at hdown
      exact hdown
    apply GrpCat.hom_ext
    exact (SingleObj.mapHom _ _).injective hsingle
  · intro T a b hab
    let _ : Groupoid (ULift.{u} (SingleObj T)) := uliftGroupoid (SingleObj T)
    let upT : SingleObj T ⥤ ULift.{u} (SingleObj T) := ULift.upFunctor
    let FU := DU ⋙ a.hom.toFunctor ⋙ upT
    let FV := DV ⋙ b.hom.toFunctor ⋙ upT
    have habfun : mWU ⋙ a.hom.toFunctor = mWV ⋙ b.hom.toFunctor := by
      simpa only [mWU, mWV, fundamentalGroupInterToLeft,
        fundamentalGroupInterToRight, GrpCat.hom_ofHom,
        GrpCat.hom_comp, MonoidHom.comp_toFunctor] using
        congrArg (fun k => k.hom.toFunctor) hab
    have hcompat :
        selectedInterToLeft ({x₀} : Set X) U V ⋙ FU =
          selectedInterToRight ({x₀} : Set X) U V ⋙ FV := by
      calc
        selectedInterToLeft ({x₀} : Set X) U V ⋙ FU =
            (selectedInterToLeft ({x₀} : Set X) U V ⋙ DU) ⋙
              a.hom.toFunctor ⋙ upT := rfl
        _ = (DW ⋙ mWU) ⋙ a.hom.toFunctor ⋙ upT := by
          rw [selectedInterToLeft_comp_pointedDelooping U V x₀ hx₀]
        _ = DW ⋙ (mWU ⋙ a.hom.toFunctor) ⋙ upT := rfl
        _ = DW ⋙ (mWV ⋙ b.hom.toFunctor) ⋙ upT := by rw [habfun]
        _ = (DW ⋙ mWV) ⋙ b.hom.toFunctor ⋙ upT := rfl
        _ = (selectedInterToRight ({x₀} : Set X) U V ⋙ DV) ⋙
              b.hom.toFunctor ⋙ upT := by
          rw [selectedInterToRight_comp_pointedDelooping U V x₀ hx₀]
        _ = selectedInterToRight ({x₀} : Set X) U V ⋙ FV := rfl
    obtain ⟨L, hUL, hVL⟩ := hselected.exists_desc
      (W := Grpd.of (ULift.{u} (SingleObj T))) FU FV hcompat
    change selectedLeftToAmbient ({x₀} : Set X) U ⋙ L = FU at hUL
    change selectedRightToAmbient ({x₀} : Set X) V ⋙ L = FV at hVL
    let L₀ := EX ⋙ L ⋙ ULift.downFunctor
    let lhom := (SingleObj.mapHom _ _).symm L₀
    let l : GrpCat.of (FundamentalGroup X x₀) ⟶ T := GrpCat.ofHom lhom
    have hupdown : upT ⋙ ULift.downFunctor = 𝟭 (SingleObj T) := rfl
    have hUfactorFun : mUX ⋙ L₀ = a.hom.toFunctor := by
      calc
        mUX ⋙ L₀ = (mUX ⋙ EX) ⋙ L ⋙ ULift.downFunctor := rfl
        _ = (EU ⋙ selectedLeftToAmbient ({x₀} : Set X) U) ⋙ L ⋙
              ULift.downFunctor := by
          rw [fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse U x₀ hx₀.1]
        _ = EU ⋙ (selectedLeftToAmbient ({x₀} : Set X) U ⋙ L) ⋙
              ULift.downFunctor := rfl
        _ = EU ⋙ FU ⋙ ULift.downFunctor :=
          congrArg (fun F => EU ⋙ F ⋙ ULift.downFunctor) hUL
        _ = (EU ⋙ DU) ⋙ a.hom.toFunctor ⋙ (upT ⋙ ULift.downFunctor) := rfl
        _ = (𝟭 _) ⋙ a.hom.toFunctor ⋙ 𝟭 _ := by
          rw [pointedDelooping_inv_hom_id AU u₀ hu₀ hUuniq, hupdown]
        _ = a.hom.toFunctor := rfl
    have hVfactorFun : mVX ⋙ L₀ = b.hom.toFunctor := by
      calc
        mVX ⋙ L₀ = (mVX ⋙ EX) ⋙ L ⋙ ULift.downFunctor := rfl
        _ = (EV ⋙ selectedRightToAmbient ({x₀} : Set X) V) ⋙ L ⋙
              ULift.downFunctor := by
          rw [fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse V x₀ hx₀.2]
        _ = EV ⋙ (selectedRightToAmbient ({x₀} : Set X) V ⋙ L) ⋙
              ULift.downFunctor := rfl
        _ = EV ⋙ FV ⋙ ULift.downFunctor :=
          congrArg (fun F => EV ⋙ F ⋙ ULift.downFunctor) hVL
        _ = (EV ⋙ DV) ⋙ b.hom.toFunctor ⋙ (upT ⋙ ULift.downFunctor) := rfl
        _ = (𝟭 _) ⋙ b.hom.toFunctor ⋙ 𝟭 _ := by
          rw [pointedDelooping_inv_hom_id AV v₀ hv₀ hVuniq, hupdown]
        _ = b.hom.toFunctor := rfl
    refine ⟨l, ?_, ?_⟩
    · apply GrpCat.hom_ext
      apply (SingleObj.mapHom _ _).injective
      simpa only [mUX, fundamentalGroupLeftToAmbient, l, lhom,
        GrpCat.hom_comp, GrpCat.hom_ofHom,
        MonoidHom.comp_toFunctor, Equiv.apply_symm_apply] using hUfactorFun
    · apply GrpCat.hom_ext
      apply (SingleObj.mapHom _ _).injective
      simpa only [mVX, fundamentalGroupRightToAmbient, l, lhom,
        GrpCat.hom_comp, GrpCat.hom_ofHom,
        MonoidHom.comp_toFunctor, Equiv.apply_symm_apply] using hVfactorFun

end DifferentialGeometry.Topology.VanKampen
end svkBundle_013
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/Based.lean

-- BEGIN SOURCE: DifferentialGeometry/Topology/VanKampen/AmalgamatedProduct.lean
section svkBundle_014
/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/

set_option autoImplicit false

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology.VanKampen

abbrev fundamentalGroupFactor {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) : Bool → Type u
  | false => FundamentalGroup U (leftBasepoint U x₀ hx₀.1)
  | true => FundamentalGroup V (rightBasepoint V x₀ hx₀.2)

noncomputable instance fundamentalGroupFactorGroup {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) (i : Bool) :
    Group (fundamentalGroupFactor U V x₀ hx₀ i) := by
  cases i <;> simp only [fundamentalGroupFactor] <;> infer_instance

noncomputable def fundamentalGroupAmalgamation {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    ∀ i, FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀) →*
      fundamentalGroupFactor U V x₀ hx₀ i
  | false => (fundamentalGroupInterToLeft U V x₀ hx₀).hom
  | true => (fundamentalGroupInterToRight U V x₀ hx₀).hom

abbrev fundamentalGroupAmalgamatedProduct {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :=
  Monoid.PushoutI (fundamentalGroupAmalgamation U V x₀ hx₀)

noncomputable def fundamentalGroupAmalgamatedProductLeft {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) ⟶
      GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.PushoutI.of
    (φ := fundamentalGroupAmalgamation U V x₀ hx₀) false)

noncomputable def fundamentalGroupAmalgamatedProductRight {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) ⟶
      GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) :=
  GrpCat.ofHom (Monoid.PushoutI.of
    (φ := fundamentalGroupAmalgamation U V x₀ hx₀) true)

theorem fundamentalGroupAmalgamatedProduct_coverSquare_commutes
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupInterToLeft U V x₀ hx₀ ≫
        fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ =
      fundamentalGroupInterToRight U V x₀ hx₀ ≫
        fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ := by
  apply GrpCat.ext
  intro w
  change Monoid.PushoutI.of false (fundamentalGroupAmalgamation U V x₀ hx₀ false w) =
    Monoid.PushoutI.of true (fundamentalGroupAmalgamation U V x₀ hx₀ true w)
  rw [Monoid.PushoutI.of_apply_eq_base, Monoid.PushoutI.of_apply_eq_base]

noncomputable def fundamentalGroupFactorToAmbient {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    ∀ i, fundamentalGroupFactor U V x₀ hx₀ i →* FundamentalGroup X x₀
  | false => (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom
  | true => (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom

theorem fundamentalGroupFactorToAmbient_compatible {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (i : Bool) :
    (fundamentalGroupFactorToAmbient U V x₀ hx₀ i).comp
        (fundamentalGroupAmalgamation U V x₀ hx₀ i) =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (fundamentalGroupInterToLeft U V x₀ hx₀).hom := by
  cases i with
  | false => rfl
  | true =>
      have h := congrArg GrpCat.Hom.hom
        (fundamentalGroup_coverSquare_commutes U V x₀ hx₀)
      simpa only [fundamentalGroupFactorToAmbient, fundamentalGroupAmalgamation,
        GrpCat.hom_comp] using h.symm

noncomputable def amalgamatedProductToFundamentalGroup {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom <| Monoid.PushoutI.lift
    (fundamentalGroupFactorToAmbient U V x₀ hx₀)
    ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
      (fundamentalGroupInterToLeft U V x₀ hx₀).hom)
    (fundamentalGroupFactorToAmbient_compatible U V x₀ hx₀)

theorem fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ ≫
        amalgamatedProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupLeftToAmbient U x₀ hx₀.1 := by
  apply GrpCat.ext
  intro g
  change (Monoid.PushoutI.lift
      (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (fundamentalGroupInterToLeft U V x₀ hx₀).hom)
      (fundamentalGroupFactorToAmbient_compatible U V x₀ hx₀))
      (Monoid.PushoutI.of
        (φ := fundamentalGroupAmalgamation U V x₀ hx₀) false g) =
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom g
  rw [Monoid.PushoutI.lift_of]
  rfl

theorem fundamentalGroupAmalgamatedProductRight_toFundamentalGroup
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ ≫
        amalgamatedProductToFundamentalGroup U V x₀ hx₀ =
      fundamentalGroupRightToAmbient V x₀ hx₀.2 := by
  apply GrpCat.ext
  intro g
  change (Monoid.PushoutI.lift
      (fundamentalGroupFactorToAmbient U V x₀ hx₀)
      ((fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom.comp
        (fundamentalGroupInterToLeft U V x₀ hx₀).hom)
      (fundamentalGroupFactorToAmbient_compatible U V x₀ hx₀))
      (Monoid.PushoutI.of
        (φ := fundamentalGroupAmalgamation U V x₀ hx₀) true g) =
    (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom g
  rw [Monoid.PushoutI.lift_of]
  rfl

noncomputable def fundamentalGroupToAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    GrpCat.of (FundamentalGroup X x₀) ⟶
      GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀) :=
  (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).desc
    (fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀)
    (fundamentalGroupAmalgamatedProductRight U V x₀ hx₀)
    (fundamentalGroupAmalgamatedProduct_coverSquare_commutes U V x₀ hx₀)

theorem fundamentalGroupLeftToAmbient_toAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupLeftToAmbient U x₀ hx₀.1 ≫
        fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inl_desc

theorem fundamentalGroupRightToAmbient_toAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupRightToAmbient V x₀ hx₀.2 ≫
        fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ =
      fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).inr_desc

theorem canonicalMaps_forward_inverse
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ ≫
        amalgamatedProductToFundamentalGroup U V x₀ hx₀ =
      𝟙 (GrpCat.of (FundamentalGroup X x₀)) := by
  apply (fundamentalGroup_isPushout U V hU hV hcover x₀ hx₀).hom_ext
  · rw [← Category.assoc, fundamentalGroupLeftToAmbient_toAmalgamatedProduct,
      fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup, Category.comp_id]
  · rw [← Category.assoc, fundamentalGroupRightToAmbient_toAmalgamatedProduct,
      fundamentalGroupAmalgamatedProductRight_toFundamentalGroup, Category.comp_id]

theorem canonicalMaps_inverse_forward
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    amalgamatedProductToFundamentalGroup U V x₀ hx₀ ≫
        fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀ =
      𝟙 (GrpCat.of (fundamentalGroupAmalgamatedProduct U V x₀ hx₀)) := by
  apply GrpCat.hom_ext
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i with
  | false =>
      have hleft : fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ ≫
            (amalgamatedProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup,
          fundamentalGroupLeftToAmbient_toAmalgamatedProduct, Category.comp_id]
      simpa only [fundamentalGroupAmalgamatedProductLeft, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hleft
  | true =>
      have hright : fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ ≫
            (amalgamatedProductToFundamentalGroup U V x₀ hx₀ ≫
              fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀) =
          fundamentalGroupAmalgamatedProductRight U V x₀ hx₀ ≫ 𝟙 _ := by
        rw [← Category.assoc, fundamentalGroupAmalgamatedProductRight_toFundamentalGroup,
          fundamentalGroupRightToAmbient_toAmalgamatedProduct, Category.comp_id]
      simpa only [fundamentalGroupAmalgamatedProductRight, GrpCat.hom_comp,
        GrpCat.hom_id, GrpCat.hom_ofHom] using congrArg GrpCat.Hom.hom hright

noncomputable def fundamentalGroupEquivAmalgamatedProduct
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    fundamentalGroupAmalgamatedProduct U V x₀ hx₀ ≃* FundamentalGroup X x₀ :=
  MonoidHom.toMulEquiv
    (amalgamatedProductToFundamentalGroup U V x₀ hx₀).hom
    (fundamentalGroupToAmalgamatedProduct U V hU hV hcover x₀ hx₀).hom
    (congrArg GrpCat.Hom.hom <|
      canonicalMaps_inverse_forward U V hU hV hcover x₀ hx₀)
    (congrArg GrpCat.Hom.hom <|
      canonicalMaps_forward_inverse U V hU hV hcover x₀ hx₀)

theorem fundamentalGroupEquivAmalgamatedProduct_comp_left
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupAmalgamatedProductLeft U V x₀ hx₀).hom =
      (fundamentalGroupLeftToAmbient U x₀ hx₀.1).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupAmalgamatedProductLeft_toFundamentalGroup U V x₀ hx₀)

theorem fundamentalGroupEquivAmalgamatedProduct_comp_right
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀).toMonoidHom.comp
        (fundamentalGroupAmalgamatedProductRight U V x₀ hx₀).hom =
      (fundamentalGroupRightToAmbient V x₀ hx₀.2).hom := by
  exact congrArg GrpCat.Hom.hom
    (fundamentalGroupAmalgamatedProductRight_toFundamentalGroup U V x₀ hx₀)

end DifferentialGeometry.Topology.VanKampen
end svkBundle_014
-- END SOURCE: DifferentialGeometry/Topology/VanKampen/AmalgamatedProduct.lean
