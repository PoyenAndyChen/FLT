/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
import FLT.QuaternionAlgebra.NumberField -- rigidifications of quat algs
import Mathlib.Data.Matrix.Reflection
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.FinitePlaces
import FLT.Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

open NumberField IsQuaternionAlgebra.NumberField IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
open scoped Pointwise

namespace TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator

-- let F be a (totally real) number field
variable {F : Type*} [Field F] [NumberField F]

namespace Local

variable {v : HeightOneSpectrum (𝓞 F)}

variable (α : v.adicCompletionIntegers F)

variable (hα : α ≠ 0)

variable (v) {α hα} in
/-- The subgroup `U1 v = GL2.localTameLevel v`. -/
noncomputable abbrev U1 : Subgroup (GL (Fin 2) (adicCompletion F v)) := GL2.localTameLevel v

open Matrix.GeneralLinearGroup.GL2

/- Some lemmas in this section could be placed somewhere else in greater generality. -/
namespace GL2

/-- The matrix element `diag[α, 1]`. -/
noncomputable abbrev diag : (GL (Fin 2) (adicCompletion F v)) :=
  Matrix.GeneralLinearGroup.diagonal (![⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩, 1])

lemma diag_def :
    (diag α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
    = !![↑α, 0; 0, 1] := by
  rw[diag, Matrix.GeneralLinearGroup.diagonal]
  ext i j; fin_cases i; all_goals fin_cases j
  all_goals simp

lemma conjBy_diag {a b c d : adicCompletion F v} :
    (diag α hα)⁻¹ * !![a, b; c, d] * diag α hα
    = !![a, (α : v.adicCompletion F)⁻¹ * b; c * α, d] := by
  simp only [Matrix.coe_units_inv, diag_def, Matrix.inv_def, Matrix.det_fin_two_of, mul_one,
    mul_zero, sub_zero, Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, neg_zero, Matrix.smul_of,
    Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.cons_mul, Nat.succ_eq_add_one,
    Nat.reduceAdd, Matrix.vecMul_cons, Matrix.head_cons, Matrix.tail_cons, zero_smul,
    Matrix.empty_vecMul, add_zero, zero_add, Matrix.empty_mul, Equiv.symm_apply_apply,
    Matrix.add_cons, Matrix.empty_add_empty, EmbeddingLike.apply_eq_iff_eq]
  rw[inv_mul_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]
  ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]

-- Show that `unipotent t` is in `U1 v` for `t ∈ O_v`.
lemma unipotent_mem_U1 (t : v.adicCompletionIntegers F) :
    unipotent ↑t ∈ (U1 v) := by
  unfold unipotent
  constructor
  · apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
    constructor
    · intro i j
      fin_cases i; all_goals fin_cases j
      all_goals simp only [Matrix.unitOfDetInvertible, Fin.mk_one, Fin.isValue, Fin.zero_eta,
        val_unitOfInvertible, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, Matrix.cons_val_one, map_zero, zero_le', map_one, le_refl]
      apply (mem_adicCompletionIntegers _ _ _).mp
      simp
    simp [Matrix.unitOfDetInvertible]
  simp [Matrix.unitOfDetInvertible]

/-- The matrix element `(unipotent t) * (diag α hα) = !![α, t; 0, 1]`. -/
noncomputable def unipotent_mul_diag (t : v.adicCompletionIntegers F) :
    (GL (Fin 2) (adicCompletion F v)) :=
  (unipotent (t : adicCompletion F v)) * (diag α hα)

/-- `!![α s; 0 1] * !![β t; 0 1] = !![αβ, αt+s; 0 1]`. -/
lemma unipotent_mul_diag_mul_unipotent_mul_diag
    {β : v.adicCompletionIntegers F} (hβ : β ≠ 0)
    (s t : v.adicCompletionIntegers F) :
    unipotent_mul_diag α hα s * unipotent_mul_diag β hβ t =
      unipotent_mul_diag (α * β) (mul_ne_zero hα hβ) (α * t + s) := by
  ext i j
  push_cast [unipotent_mul_diag, unipotent_def, diag_def]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `!![α t₁; 0 1]⁻¹ * [α t₂; 0 1] = [1 (t₂ - t₁) / α; 0 1]`. -/
lemma unipotent_mul_diag_inv_mul_unipotent_mul_diag (t₁ t₂ : v.adicCompletionIntegers F) :
    (unipotent_mul_diag α hα t₁)⁻¹ * unipotent_mul_diag α hα t₂
    = unipotent ((α : v.adicCompletion F)⁻¹ * ((t₂ + -t₁) : adicCompletion F v )) := by
  ext i j
  push_cast [unipotent_mul_diag, mul_inv_rev, unipotent_inv]
  rw [← mul_assoc]; nth_rw 2 [mul_assoc]
  rw_mod_cast [unipotent_mul]; push_cast [unipotent_def]
  rw_mod_cast [conjBy_diag]
  simp


end GL2

open GL2

/- We could use `TameLevel` instead of `U1` in the naming,
but not sure if we might want to generalise to more general `U_Δ` at some point. -/
namespace U1

variable {α hα}

variable {x : GL (Fin 2) (adicCompletion F v)}

variable (hx : x ∈ (U1 v))
include hx

lemma apply_mem_integer (i j : Fin 2) :
    (x i j) ∈ (adicCompletionIntegers F v) :=
  GL2.v_le_one_of_mem_localFullLevel _ hx.left _ _

lemma apply_zero_zero_sub_apply_one_one_mem_maximalIdeal :
    (⟨(x 0 0), apply_mem_integer hx _ _⟩ - ⟨(x 1 1), apply_mem_integer hx _ _⟩)
    ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
  (mem_completionIdeal_iff _ v _).mpr hx.right.left

lemma apply_one_zero_mem_maximalIdeal :
    ⟨(x 1 0), apply_mem_integer hx _ _⟩
    ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
  (mem_completionIdeal_iff _ v _).mpr hx.right.right

lemma apply_one_one_notMem_maximalIdeal :
    ⟨(x 1 1), apply_mem_integer hx _ _⟩
    ∉ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) := by
  by_contra mem_maximalIdeal
  have det_mem_maximalIdeal :
      ⟨(x 0 0), apply_mem_integer hx _ _⟩ * ⟨(x 1 1), apply_mem_integer hx _ _⟩
      - ⟨(x 0 1), apply_mem_integer hx _ _⟩ * ⟨(x 1 0), apply_mem_integer hx _ _⟩
      ∈ IsLocalRing.maximalIdeal (adicCompletionIntegers F v) :=
    Ideal.sub_mem _
      (Ideal.mul_mem_left _ _ mem_maximalIdeal)
      (Ideal.mul_mem_left _ _ (apply_one_zero_mem_maximalIdeal hx))
  have v_det_lt_one :=
    ((mem_completionIdeal_iff _ v _).mp det_mem_maximalIdeal)
  push_cast at v_det_lt_one; rw[← Matrix.det_fin_two] at v_det_lt_one
  exact (ne_of_lt v_det_lt_one) (GL2.v_det_val_mem_localFullLevel_eq_one hx.left)

lemma isUnit_apply_one_one :
    IsUnit (⟨(x 1 1), apply_mem_integer hx _ _⟩ : adicCompletionIntegers F v) :=
  (IsLocalRing.notMem_maximalIdeal.mp (apply_one_one_notMem_maximalIdeal hx))

lemma conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal :
    (diag α hα)⁻¹ * x * diag α hα ∈ U1 v
    ↔ ⟨(x 0 1), apply_mem_integer hx _ _⟩ ∈ (Ideal.span {α}) := by
  let a : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 0⟩
  let b : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 1⟩
  let c : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 0 ⟩
  let d : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  constructor
  · /- If `(diag α hα)⁻¹ * x * diag α hα ∈ U1 v`,
    then we have `((diag α hα)⁻¹ * x * diag α hα) 0 1 ∈ adicCompletionIntegers F v`,
    which after computing `(diag α hα)⁻¹ * x * diag α hα` gives the desired. -/
    intro h; have h₁ := apply_mem_integer h 0 1
    push_cast [hx₁] at h₁; rw_mod_cast [conjBy_diag] at h₁
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero] at h₁
    apply Ideal.mem_span_singleton'.mpr
    use ⟨_, h₁⟩
    apply (Subtype.coe_inj).mp; push_cast
    ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
  /- Conversely, we show that `(diag α hα)⁻¹ * x * diag α hα ∈ U1 v`. -/
  intro h; obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
  constructor
  /- We first show that `(diag α hα)⁻¹ * x * diag α hα` is in `GL_2(O_v)`. -/
  · apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
    push_cast [hx₁]; rw_mod_cast [conjBy_diag]
    constructor
    · intro i j; fin_cases i; all_goals fin_cases j
      all_goals simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one,
        Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      · exact apply_mem_integer hx 0 0
      · unfold b; rw[← hq]; push_cast; ring_nf
        rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
        apply (mem_adicCompletionIntegers _ _ _).mp
        simp
      · exact_mod_cast le_of_lt
          ((mem_completionIdeal_iff _ v _).mp
          (Ideal.mul_mem_right _ _ (apply_one_zero_mem_maximalIdeal hx)))
      exact apply_mem_integer hx 1 1
    rw[Matrix.det_fin_two_of]; ring_nf
    rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
    rw[← Matrix.det_fin_two]
    exact GL2.v_det_val_mem_localFullLevel_eq_one hx.left
  /- Finally we show that `(diag α hα)⁻¹ * x * diag α hα`
  is in `GL2.localTameLevel`. -/
  push_cast [hx₁]; rw_mod_cast [conjBy_diag]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  norm_cast
  exact ⟨hx.right.left,
    (mem_completionIdeal_iff _ v _).mp
    (Ideal.mul_mem_right _ _ (apply_one_zero_mem_maximalIdeal hx))⟩

end U1

open U1

section CosetDecomposition

variable (v) in
/-- The double coset space `U1 diag U1` as a set of left cosets. -/
noncomputable def U1diagU1 :
    Set ((GL (Fin 2) (adicCompletion F v)) ⧸ (U1 v)) :=
  (QuotientGroup.mk '' ((U1 v) * {diag α hα}))

variable (v) in
/-- For each `t ∈ O_v / αO_v`, the left coset `unipotent_mul_diag U1`
for a lift of t to `O_v`. -/
noncomputable def unipotent_mul_diagU1
    (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α})) :
    ((GL (Fin 2) (adicCompletion F v)) ⧸ ↑(U1 v)) :=
  QuotientGroup.mk (unipotent_mul_diag α hα (Quotient.out t : adicCompletionIntegers F v))

/-- `unipotent_mul_diagU1` is contained in `U1diagU1` for all t. -/
lemma mapsTo_unipotent_mul_diagU1_U1diagU1 :
    Set.MapsTo (unipotent_mul_diagU1 v α hα) ⊤ (U1diagU1 v α hα) :=
  (fun t _ => Set.mem_image_of_mem QuotientGroup.mk
    (Set.mul_mem_mul (unipotent_mem_U1 (Quotient.out t)) rfl))

/-- Distinct t give distinct `unipotent_mul_diagU1`, i.e. we have a disjoint union. -/
lemma injOn_unipotent_mul_diagU1 :
    Set.InjOn (unipotent_mul_diagU1 v α hα) ⊤ := by
  intro t₁ h₁ t₂ h₂ h
  /- If `unipotent_mul_diagU1 t₁ = unipotent_mul_diagU1 t₂`,
  then `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)` is in `U1 v`.
  Note `unipotent_mul_diag_inv_mul_unipotent_mul_diag` tells us that
  `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)` is `unipotent`. -/
  have unipotent_mem_U1 :=
    (unipotent_mul_diag_inv_mul_unipotent_mul_diag α hα (Quotient.out t₁) (Quotient.out t₂)) ▸
      (QuotientGroup.eq.mp h)
  /- Then inspecting the top-right entry of `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)`
  gives us `t₁ = t₂`. -/
  have unipotent_apply_zero_one_mem_integer := apply_mem_integer unipotent_mem_U1 0 1
  simp only [unipotent, Matrix.unitOfDetInvertible, Fin.isValue, val_unitOfInvertible,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.cons_val_zero] at unipotent_apply_zero_one_mem_integer
  rw [← (QuotientAddGroup.out_eq' t₁), ← (QuotientAddGroup.out_eq' t₂)]
  apply QuotientAddGroup.eq.mpr; apply Ideal.mem_span_singleton'.mpr
  use ⟨_, unipotent_apply_zero_one_mem_integer⟩
  apply (Subtype.coe_inj).mp; push_cast
  ring_nf; rw[mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]

/-- Each coset in `U1diagU1` is of the form `unipotent_mul_diagU1` for some `t ∈ O_v`. -/
lemma surjOn_unipotent_mul_diagU1_U1diagU1 :
    Set.SurjOn (unipotent_mul_diagU1 v α hα) ⊤ (U1diagU1 v α hα) := by
  rintro _ ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩
  /- Each element of `U1diagU1` can be written as `x * diag`,
  where `x = !![a,b;c,d]` is viewed as a matrix over `O_v`. -/
  let a : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 0⟩
  let b : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 0 1⟩
  let c : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 0⟩
  let d : (adicCompletionIntegers F v) := ⟨_, apply_mem_integer hx 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  -- The desired t is `⅟d * b`.
  letI invertible_d := (isUnit_apply_one_one hx).invertible
  let t : ↥(adicCompletionIntegers F v) ⧸ (Ideal.span {α}) := (⅟d * b)
  use t
  have ht : (b + -Quotient.out t * d) ∈ Ideal.span {α} := by
    apply Ideal.mem_span_singleton'.mpr
    have t_def : (Ideal.Quotient.mk (Ideal.span {α})) (Quotient.out t) = (⅟d * b) := by
      simp only [Ideal.Quotient.mk_out]; rfl
    obtain ⟨q, hq⟩ :=
      Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp t_def)
    use - d * q
    rw[mul_assoc, hq]; ring_nf; simp
  /- The rest of the proof is devoted to showing that this t works.
  This means showing that `unipotent_mul_diag⁻¹ * x * diag` is in U. -/
  simp only [unipotent_mul_diagU1, Set.top_eq_univ, Set.mem_univ, true_and]
  apply QuotientGroup.eq.mpr
  unfold unipotent_mul_diag; rw[mul_inv_rev, ← mul_assoc, mul_assoc _ _ x]
  /- But `unipotent_mul_diag⁻¹ * x * diag = diag⁻¹ * (unipotent⁻¹ * x) * diag`,
  so we can apply `conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal`,
  and it suffices to show `(unipotent⁻¹ * x) 0 1 ∈ (Ideal.span {α})`.
  The choice of t guarantees this. -/
  apply (conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (unipotent_mem_U1 _)) hx)).mpr
  simp only [Fin.isValue, Units.val_mul, Matrix.coe_units_inv, unipotent_def, Matrix.inv_def,
    Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_one,
    Matrix.adjugate_fin_two_of, neg_zero, one_smul, hx₁, Matrix.mul_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.sum_univ_two, one_mul]
  exact_mod_cast ht

variable (v) in
/-- The double coset space `U1diagU1` is the disjoint union of
`unipotent_mul_diagU1` as t ranges over `O_v / αO_v`. -/
theorem bijOn_unipotent_mul_diagU1_U1diagU1 :
    Set.BijOn (unipotent_mul_diagU1 v α hα) ⊤ (U1diagU1 v α hα) :=
  ⟨mapsTo_unipotent_mul_diagU1_U1diagU1 α hα,
    injOn_unipotent_mul_diagU1 α hα,
    surjOn_unipotent_mul_diagU1_U1diagU1 α hα⟩

end CosetDecomposition

section TCosetGoodPrime

/-- The full local level subgroup for "good primes": GL2(O_v). -/
noncomputable def U0 (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (adicCompletion F v)) :=
  GL2.localFullLevel v

/-- The secondary diagonal matrix element `!![1, 0; 0, α]`. Dual to `GL2.diag` which is
`!![α, 0; 0, 1]`. The name `diag'` mirrors `diag` with the unit placed on the other
diagonal entry. This represents the "extra" coset in the T_v double coset decomposition
at good primes (beyond the q_v unipotent_mul_diag cosets). -/
noncomputable def diag' (α : v.adicCompletionIntegers F) (hα : α ≠ 0) :
    (GL (Fin 2) (adicCompletion F v)) :=
  Matrix.GeneralLinearGroup.diagonal (![1, ⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]
      exact_mod_cast hα, by
      rw [inv_mul_cancel₀]
      exact_mod_cast hα⟩])

lemma diag'_def :
    (diag' α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
    = !![1, 0; 0, ↑α] := by
  rw [diag', Matrix.GeneralLinearGroup.diagonal]
  ext i j; fin_cases i; all_goals fin_cases j
  all_goals simp

/-- The unipotent matrix `!![1, t; 0, 1]` is in `U0 v = GL₂(O_v)` for `t ∈ O_v`. -/
lemma unipotent_mem_U0 (t : v.adicCompletionIntegers F) :
    unipotent ↑t ∈ (U0 v) :=
  (unipotent_mem_U1 t).left

variable (v) in
/-- The double coset space `U0 diag U0` as a set of left cosets. Since right-multiplying
by `U0` does not change the coset class, `mk '' (U0 * {diag} * U0) = mk '' (U0 * {diag})`. -/
noncomputable def U0diagU0 :
    Set ((GL (Fin 2) (adicCompletion F v)) ⧸ (U0 v)) :=
  QuotientGroup.mk '' ((U0 v : Set _) * {diag α hα})

variable (v) in
/-- The family of `q+1` coset representatives for the `U0 diag U0` double coset:
- `none` maps to `[diag']` (the "extra" coset)
- `some t` maps to `[unipotent_mul_diag t]` for `t ∈ O_v / αO_v` (the `q` unipotent cosets). -/
noncomputable def T_cosets :
    Option (adicCompletionIntegers F v ⧸ Ideal.span {α}) →
    (GL (Fin 2) (adicCompletion F v)) ⧸ (U0 v)
  | none => QuotientGroup.mk (diag' α hα)
  | some t => QuotientGroup.mk (unipotent_mul_diag α hα (Quotient.out t))

/-- Each `T_cosets` value is in `U0diagU0`. -/
lemma mapsTo_T_cosets :
    Set.MapsTo (T_cosets v α hα) ⊤ (U0diagU0 v α hα) := by
  intro x _
  cases x with
  | some t =>
    -- `unipotent_mul_diag t = unipotent t * diag`, and `unipotent t ∈ U0`.
    exact Set.mem_image_of_mem QuotientGroup.mk
      (Set.mul_mem_mul (unipotent_mem_U0 (Quotient.out t)) rfl)
  | none =>
    -- `diag' = W * diag * W` where `W = !![0,1;1,0] ∈ U0`.
    -- So `mk(diag') = mk(W * diag)` (since `W ∈ U0` on the right cancels in the quotient).
    -- And `W * diag ∈ U0 * {diag}`, so `mk(W * diag) ∈ mk '' (U0 * {diag})`.
    -- Concretely: `mk(diag') = mk(W * diag)` iff `(W * diag)⁻¹ * diag' ∈ U0`,
    -- and `(W * diag)⁻¹ * diag' = W ∈ U0`.
    -- Define the swap matrix W
    let W : GL (Fin 2) (adicCompletion F v) :=
      letI detInv : Invertible !![0, 1; 1, (0 : adicCompletion F v)].det :=
      { invOf := -1,
        invOf_mul_self := by simp [Matrix.det_fin_two_of],
        mul_invOf_self := by simp [Matrix.det_fin_two_of] }
      Matrix.unitOfDetInvertible !![0, 1; 1, (0 : adicCompletion F v)]
    -- W * diag is in U0 * {diag}
    suffices h : QuotientGroup.mk (W * diag α hα) ∈ U0diagU0 v α hα from by
      -- mk(diag') = mk(W * diag) since (W * diag)⁻¹ * diag' ∈ U0
      convert h using 1
      apply QuotientGroup.eq.mpr
      -- Need: (diag')⁻¹ * (W * diag) ∈ U0
      -- Show (diag')⁻¹ * (W * diag) = W, then W ∈ U0.
      have hW_eq : (diag' α hα)⁻¹ * (W * diag α hα) = W := by
        ext i j
        push_cast [diag_def, diag'_def, W, Matrix.unitOfDetInvertible,
          Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm,
            mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα)]
      rw [hW_eq]
      change W ∈ GL2.localFullLevel v
      apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
      constructor
      · intro i j; fin_cases i <;> fin_cases j <;>
          simp [W, Matrix.unitOfDetInvertible]
      · simp [W, Matrix.unitOfDetInvertible, Matrix.det_fin_two_of]
    -- Show W * diag ∈ U0 * {diag}
    exact Set.mem_image_of_mem QuotientGroup.mk
      (Set.mul_mem_mul (by
        -- W ∈ U0 = GL₂(O_v)
        change W ∈ GL2.localFullLevel v
        apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
        constructor
        · intro i j; fin_cases i <;> fin_cases j <;>
            simp [W, Matrix.unitOfDetInvertible]
        · simp [W, Matrix.unitOfDetInvertible, Matrix.det_fin_two_of]
      ) rfl)

/-- Distinct indices give distinct `T_cosets`, i.e., the cosets are disjoint. -/
lemma injOn_T_cosets (hα_not_unit : ¬IsUnit α) :
    Set.InjOn (T_cosets v α hα) ⊤ := by
  intro x _ y _ h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some t₂ =>
      -- `(diag')⁻¹ * (unipotent_mul_diag t₂)` has (1,1)-entry `α⁻¹`,
      -- which is NOT in `O_v` (since `α` is not a unit).
      exfalso
      simp only [T_cosets] at h
      have hmem := QuotientGroup.eq.mp h
      -- Extract (1,1) entry and show it equals α⁻¹
      have hentry : ((diag' α hα)⁻¹ * unipotent_mul_diag α hα
          (Quotient.out t₂) : GL (Fin 2) _).val 1 1 =
          (α : adicCompletion F v)⁻¹ := by
        push_cast [diag'_def, unipotent_mul_diag, unipotent_def, diag_def,
          Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      have hv := GL2.v_le_one_of_mem_localFullLevel _ hmem 1 1
      rw [hentry] at hv; rw [map_inv₀] at hv
      exact hα_not_unit (Valued.isUnit_valuationSubring_iff.mpr
        (le_antisymm (α.property) ((inv_le_one₀ (zero_lt_iff.mpr (Valuation.ne_zero_iff _ |>.mpr
        (by exact_mod_cast hα)))).mp hv)))
  | some t₁ =>
    cases y with
    | none =>
      -- `(unipotent_mul_diag t₁)⁻¹ * diag'` has (0,0)-entry `α⁻¹`,
      -- which is NOT in `O_v` (since `α` is not a unit).
      exfalso
      simp only [T_cosets] at h
      have hmem := QuotientGroup.eq.mp h
      -- Extract (0,0) entry and show it equals α⁻¹
      have hentry : ((unipotent_mul_diag α hα (Quotient.out t₁))⁻¹ *
          diag' α hα : GL (Fin 2) _).val 0 0 =
          (α : adicCompletion F v)⁻¹ := by
        push_cast [diag'_def, unipotent_mul_diag, unipotent_def, diag_def,
          Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      have hv := GL2.v_le_one_of_mem_localFullLevel _ hmem 0 0
      rw [hentry] at hv; rw [map_inv₀] at hv
      exact hα_not_unit (Valued.isUnit_valuationSubring_iff.mpr
        (le_antisymm (α.property) ((inv_le_one₀ (zero_lt_iff.mpr (Valuation.ne_zero_iff _ |>.mpr
        (by exact_mod_cast hα)))).mp hv)))
    | some t₂ =>
      -- Same argument as the U1 version: the (0,1)-entry of
      -- `(unipotent_mul_diag t₁)⁻¹ * (unipotent_mul_diag t₂)` determines `t₁ = t₂`.
      congr 1
      simp only [T_cosets] at h
      have unipotent_mem_U0 :=
        (unipotent_mul_diag_inv_mul_unipotent_mul_diag α hα (Quotient.out t₁)
          (Quotient.out t₂)) ▸ (QuotientGroup.eq.mp h)
      have unipotent_apply_zero_one_mem_integer :=
        GL2.v_le_one_of_mem_localFullLevel _ unipotent_mem_U0 0 1
      simp only [unipotent, Matrix.unitOfDetInvertible, Fin.isValue, val_unitOfInvertible,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero] at unipotent_apply_zero_one_mem_integer
      rw [← (QuotientAddGroup.out_eq' t₁), ← (QuotientAddGroup.out_eq' t₂)]
      apply QuotientAddGroup.eq.mpr; apply Ideal.mem_span_singleton'.mpr
      use ⟨_, unipotent_apply_zero_one_mem_integer⟩
      apply (Subtype.coe_inj).mp; push_cast
      ring_nf; rw [mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]

/-- Conjugation by `diag` preserves `U0 = GL₂(O_v)` iff the (0,1) entry is divisible by `α`.
This is the U0 analog of `conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal`. -/
private lemma conjBy_diag_mem_U0_iff_apply_zero_one_mem_ideal
    {y : GL (Fin 2) (adicCompletion F v)} (hy : y ∈ GL2.localFullLevel v) :
    (diag α hα)⁻¹ * y * diag α hα ∈ GL2.localFullLevel v
    ↔ ⟨(y 0 1), GL2.v_le_one_of_mem_localFullLevel _ hy 0 1⟩ ∈ (Ideal.span {α}) := by
  let ya : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hy 0 0⟩
  let yb : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hy 0 1⟩
  let yc : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hy 1 0⟩
  let yd : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hy 1 1⟩
  have hy₁ : y = !![(ya : adicCompletion F v), yb; yc, yd] :=
    (Matrix.etaExpand_eq (y : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  constructor
  · intro h
    have h₁ := GL2.v_le_one_of_mem_localFullLevel _ h 0 1
    push_cast [hy₁] at h₁; rw_mod_cast [conjBy_diag] at h₁
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero] at h₁
    apply Ideal.mem_span_singleton'.mpr
    use ⟨_, h₁⟩
    apply (Subtype.coe_inj).mp; push_cast
    ring_nf; rw [mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
  · intro h; obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h
    apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
    refine ⟨?_, ?_⟩
    · -- All entries have valuation ≤ 1
      intro i j
      push_cast [hy₁]; rw_mod_cast [conjBy_diag]
      fin_cases i <;> fin_cases j
      · -- (0,0)
        simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_fin_one]
        exact GL2.v_le_one_of_mem_localFullLevel _ hy 0 0
      · -- (0,1)
        simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_fin_one]
        unfold yb; rw [← hq]; push_cast; ring_nf
        rw [mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
        apply (mem_adicCompletionIntegers _ _ _).mp; simp
      · -- (1,0): v(yc * α) ≤ 1 since v(yc) ≤ 1 and v(α) ≤ 1
        simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, map_mul]
        exact mul_le_one' (GL2.v_le_one_of_mem_localFullLevel _ hy 1 0) α.property
      · -- (1,1)
        simp only [Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact GL2.v_le_one_of_mem_localFullLevel _ hy 1 1
    · -- det(diag⁻¹ * y * diag) = det(y) since det(diag⁻¹) * det(diag) = 1
      have : ((diag α hα)⁻¹ * y * diag α hα).val.det = y.val.det := by
        simp only [Units.val_mul, Matrix.det_mul]
        have hinv : ((diag α hα)⁻¹ : GL (Fin 2) _).val.det * (diag α hα).val.det = 1 := by
          rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]; simp
        linear_combination y.val.det * hinv
      rw [this]; exact GL2.v_det_val_mem_localFullLevel_eq_one hy

/-- Each coset in `U0diagU0` is of the form `T_cosets` for some index.
This requires a case analysis on the valuation of the (1,1) entry of the coset
representative. The hypothesis `Irreducible α` (equivalently, `α` is a uniformizer)
ensures that every non-unit in `O_v` is divisible by `α`. -/
lemma surjOn_T_cosets (hα_irr : Irreducible α) :
    Set.SurjOn (T_cosets v α hα) ⊤ (U0diagU0 v α hα) := by
  rintro _ ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩
  /- Each element of `U0diagU0` can be written as `mk(x * diag)` with `x ∈ U0 = GL₂(O_v)`.
  Extract the entries of `x` as elements of `O_v`. -/
  have hx' : x ∈ GL2.localFullLevel v := hx
  let a : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx' 0 0⟩
  let b : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx' 0 1⟩
  let c : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx' 1 0⟩
  let d : (adicCompletionIntegers F v) := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx' 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  /- Case split on whether d (the (1,1) entry of x) is a unit in O_v. -/
  by_cases hd : IsUnit d
  · /- **Case 1: d is a unit.** The coset equals `T_cosets (some t)` for `t = d⁻¹b mod α`.
    This is the same argument as the U1 surjection proof. -/
    letI invertible_d := hd.invertible
    let t : ↥(adicCompletionIntegers F v) ⧸ (Ideal.span {α}) := (⅟d * b)
    use (some t)
    /- Show that `b - (Quotient.out t) * d ∈ (α)`. -/
    have ht : (b + -Quotient.out t * d) ∈ Ideal.span {α} := by
      apply Ideal.mem_span_singleton'.mpr
      have t_def : (Ideal.Quotient.mk (Ideal.span {α})) (Quotient.out t) = (⅟d * b) := by
        simp only [Ideal.Quotient.mk_out]; rfl
      obtain ⟨q, hq⟩ :=
        Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp t_def)
      use - d * q
      rw [mul_assoc, hq]; ring_nf; simp
    /- Now show `T_cosets (some t) = mk(x * diag)`, i.e.,
    `(unipotent_mul_diag (out t))⁻¹ * (x * diag) ∈ U0 = GL₂(O_v)`.
    Factor as `diag⁻¹ * (unipotent(-out t) * x) * diag` and check the (0,1) entry. -/
    simp only [T_cosets, Set.top_eq_univ, Set.mem_univ, true_and]
    apply QuotientGroup.eq.mpr
    unfold unipotent_mul_diag; rw [mul_inv_rev, ← mul_assoc, mul_assoc _ _ x]
    have hunip_x_mem : (unipotent (↑(Quotient.out t : adicCompletionIntegers F v) :
        adicCompletion F v))⁻¹ * x ∈ GL2.localFullLevel v :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (unipotent_mem_U0 (Quotient.out t))) hx
    change (diag α hα)⁻¹ * ((unipotent (↑(Quotient.out t : adicCompletionIntegers F v) :
      adicCompletion F v))⁻¹ * x) * diag α hα ∈ GL2.localFullLevel v
    apply (conjBy_diag_mem_U0_iff_apply_zero_one_mem_ideal α hα hunip_x_mem).mpr
    simp only [Fin.isValue, Units.val_mul, Matrix.coe_units_inv, unipotent_def, Matrix.inv_def,
      Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_one,
      Matrix.adjugate_fin_two_of, neg_zero, one_smul, hx₁, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.sum_univ_two, one_mul]
    exact_mod_cast ht
  · /- **Case 2: d is not a unit.** Since `Irreducible α`, `maximalIdeal = (α)`, and
    `¬IsUnit d` implies `d ∈ maximalIdeal = (α)`, i.e., `α | d`.
    The coset equals `T_cosets none = mk(diag')`. -/
    use none
    -- First, show α ∣ d using the DVR structure
    have hα_dvd_d : d ∈ Ideal.span {α} := by
      rw [← hα_irr.maximalIdeal_eq]
      exact (IsLocalRing.mem_maximalIdeal d).mpr (mem_nonunits_iff.mpr hd)
    -- Strategy: use that mk(diag') = mk(W * diag) where W = !![0,1;1,0].
    -- Then mk(x * diag) = mk(diag') iff (W * diag)⁻¹ * (x * diag) = diag⁻¹ * W * x * diag ∈ U0.
    -- This is diag⁻¹ * (W * x) * diag, and W * x ∈ U0, so by the helper lemma
    -- it suffices that (W * x)₀₁ = d ∈ (α), which is hα_dvd_d.
    -- Define W as in the mapsTo_T_cosets proof
    let W : GL (Fin 2) (adicCompletion F v) :=
      letI detInv : Invertible !![0, 1; 1, (0 : adicCompletion F v)].det :=
      { invOf := -1,
        invOf_mul_self := by simp [Matrix.det_fin_two_of],
        mul_invOf_self := by simp [Matrix.det_fin_two_of] }
      Matrix.unitOfDetInvertible !![0, 1; 1, (0 : adicCompletion F v)]
    have hW_mem : W ∈ GL2.localFullLevel v := by
      apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
      constructor
      · intro i j; fin_cases i <;> fin_cases j <;> simp [W, Matrix.unitOfDetInvertible]
      · simp [W, Matrix.unitOfDetInvertible, Matrix.det_fin_two_of]
    simp only [T_cosets, Set.top_eq_univ, Set.mem_univ, true_and]
    -- First establish that mk(diag') = mk(W * diag)
    have hdiag'_eq : (QuotientGroup.mk (diag' α hα) : (GL (Fin 2) _) ⧸ U0 v) =
        QuotientGroup.mk (W * diag α hα) := by
      apply QuotientGroup.eq.mpr
      have hW_eq : (diag' α hα)⁻¹ * (W * diag α hα) = W := by
        ext i j
        push_cast [diag_def, diag'_def, W, Matrix.unitOfDetInvertible,
          Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm,
            mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα)]
      rw [hW_eq]; exact hW_mem
    rw [hdiag'_eq]
    -- Now show mk(x * diag) = mk(W * diag), i.e., (W * diag)⁻¹ * (x * diag) ∈ U0
    apply QuotientGroup.eq.mpr
    -- (W * diag)⁻¹ * (x * diag) = diag⁻¹ * W⁻¹ * x * diag = diag⁻¹ * (W⁻¹ * x) * diag
    rw [mul_inv_rev, ← mul_assoc, mul_assoc _ _ x]
    -- W⁻¹ * x ∈ U0
    have hWinv_x_mem : W⁻¹ * x ∈ GL2.localFullLevel v :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hW_mem) hx'
    change (diag α hα)⁻¹ * (W⁻¹ * x) * diag α hα ∈ GL2.localFullLevel v
    apply (conjBy_diag_mem_U0_iff_apply_zero_one_mem_ideal α hα hWinv_x_mem).mpr
    -- (W⁻¹ * x)₀₁ = d, and d ∈ (α)
    simp only [Fin.isValue, Units.val_mul, Matrix.coe_units_inv, hx₁,
      W, Matrix.unitOfDetInvertible, Matrix.inv_def, Matrix.det_fin_two_of,
      Matrix.adjugate_fin_two_of, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, val_unitOfInvertible]
    simp only [mul_zero, mul_one, zero_sub, Ring.inverse_eq_inv', inv_neg, inv_one, Fin.isValue,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, smul_eq_mul, zero_mul, Matrix.cons_val_one, mul_neg, neg_neg,
      one_mul, zero_add, Subtype.coe_eta]
    exact_mod_cast hα_dvd_d

/-- The double coset space `U0diagU0` is the disjoint union of `T_cosets` as the index
ranges over `Option (O_v / αO_v)`, giving `q + 1` cosets. -/
theorem bijOn_T_cosets_U0diagU0 (hα_irr : Irreducible α) :
    Set.BijOn (T_cosets v α hα) ⊤ (U0diagU0 v α hα) :=
  ⟨mapsTo_T_cosets α hα,
    injOn_T_cosets α hα hα_irr.not_isUnit,
    surjOn_T_cosets α hα hα_irr⟩

end TCosetGoodPrime

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
