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

/-- Conjugation by `diag` preserves `U0 = localFullLevel` when the (0,1) entry is in `span{α}`.
This is the U0 analog of `conjBy_diag_mem_U1_iff_apply_zero_one_mem_ideal` (which requires U1). -/
lemma conjBy_diag_mem_U0_of_apply_zero_one_mem_ideal
    {x : GL (Fin 2) (adicCompletion F v)}
    (hx : x ∈ GL2.localFullLevel v)
    (h01 : ⟨(x 0 1), GL2.v_le_one_of_mem_localFullLevel _ hx 0 1⟩ ∈ Ideal.span {α}) :
    (diag α hα)⁻¹ * x * diag α hα ∈ GL2.localFullLevel v := by
  let a' : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 0⟩
  let b' : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 1⟩
  let c' : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 0⟩
  let d' : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 1⟩
  have hx₁' : x = !![(a' : adicCompletion F v), b'; c', d'] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h01
  apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
  push_cast [hx₁']; rw_mod_cast [conjBy_diag]
  constructor
  · intro i j; fin_cases i; all_goals fin_cases j
    all_goals simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    · exact GL2.v_le_one_of_mem_localFullLevel _ hx 0 0
    · -- (0,1): v(α⁻¹ * b') ≤ 1 since b' = α*q gives α⁻¹*b' = q ∈ O_v.
      have : (↑α : adicCompletion F v)⁻¹ * ↑b' = ↑q := by
        have hbq : (b' : adicCompletion F v) = (α : adicCompletion F v) * (q : adicCompletion F v) := by
          have := congrArg (Subtype.val (p := fun x => x ∈ adicCompletionIntegers F v)) hq
          push_cast at this; rw [show (b' : adicCompletion F v) = x.val 0 1 from rfl, ← this]; ring
        rw [hbq]
        rw [← mul_assoc, inv_mul_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
      rw_mod_cast [this]
      exact q.2
    · -- (1,0): v(c' * α) ≤ 1 since both c', α ∈ O_v.
      exact_mod_cast (c' * α).2
    exact GL2.v_le_one_of_mem_localFullLevel _ hx 1 1
  rw [Matrix.det_fin_two_of]; ring_nf
  rw [mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul]
  rw [← Matrix.det_fin_two]
  exact GL2.v_det_val_mem_localFullLevel_eq_one hx

section TCosetFullLevel

/-! ### Double coset decomposition for `GL₂(O_v) · diag(α,1) · GL₂(O_v)`

At a good prime `v` (where the local subgroup is the full level `GL₂(O_v)` rather than
the tame level), the double coset `GL₂(O_v) · diag(α,1) · GL₂(O_v)` decomposes into
`|O_v/α| + 1` left cosets modulo `GL₂(O_v)`, represented by:
- `unipotent_mul_diag α hα t` for `t ∈ O_v / α` (`|O_v/α|` cosets)
- `diag' α hα = diag[1, α]` (one additional coset)

The surjection uses the fact that `α` generates the maximal ideal (i.e., `α` is a
uniformizer), so every non-unit in `O_v` is divisible by `α`.
-/

variable (v) {α hα} in
/-- The full local level subgroup `GL₂(O_v)`. -/
noncomputable abbrev U0 : Subgroup (GL (Fin 2) (adicCompletion F v)) := GL2.localFullLevel v

/-- The diagonal matrix element `diag[1, α]`. -/
noncomputable def diag' : GL (Fin 2) (adicCompletion F v) :=
  Matrix.GeneralLinearGroup.diagonal (![1, ⟨(α : v.adicCompletion F),
    (α : v.adicCompletion F)⁻¹, by
      rw [mul_inv_cancel₀]; exact_mod_cast hα, by
      rw [inv_mul_cancel₀]; exact_mod_cast hα⟩])

set_option maxHeartbeats 400000 in
lemma diag'_def :
    (diag' α hα : Matrix (Fin 2) (Fin 2) (adicCompletion F v))
    = !![1, 0; 0, ↑α] := by
  rw [diag', Matrix.GeneralLinearGroup.diagonal]
  ext i j; fin_cases i; all_goals fin_cases j
  all_goals simp

set_option maxHeartbeats 400000 in
lemma diag'_inv_val :
    ((diag' α hα)⁻¹ : GL (Fin 2) (adicCompletion F v)).val
    = !![1, 0; 0, (↑α : adicCompletion F v)⁻¹] := by
  -- diag' is constructed as GeneralLinearGroup.diagonal, so its inverse is
  -- GeneralLinearGroup.diagonal applied to the componentwise inverse.
  -- We extract it via Units.val_inv_eq_inv_val and nonsing_inv computation.
  rw [Matrix.coe_units_inv, diag'_def]
  simp only [Matrix.inv_def, Matrix.det_fin_two_of, one_mul, mul_zero, sub_zero,
    Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, neg_zero, Matrix.smul_of,
    Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, mul_one, one_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [inv_mul_cancel₀ ((Subtype.coe_ne_coe).mpr hα)]

-- Computes `(diag')⁻¹ * M * diag` as a raw matrix.
-- diag' = !![1,0;0,α], diag = !![α,0;0,1], so
-- (diag')⁻¹ * !![a,b;c,d] * diag = !![aα, b; c, d*α⁻¹]
set_option maxHeartbeats 800000 in
lemma conjBy_diag'_diag {a b c d : adicCompletion F v} :
    (diag' α hα)⁻¹ * !![a, b; c, d] * diag α hα
    = !![a * (α : v.adicCompletion F), b; c, d * (α : v.adicCompletion F)⁻¹] := by
  simp only [Matrix.coe_units_inv, diag'_def, diag_def, Matrix.inv_def, Matrix.det_fin_two_of,
    one_mul, mul_zero, sub_zero, Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, neg_zero,
    Matrix.smul_of, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.cons_mul,
    Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.vecMul_cons, Matrix.head_cons, Matrix.tail_cons,
    zero_smul, Matrix.empty_vecMul, add_zero, zero_add, Matrix.empty_mul,
    Equiv.symm_apply_apply, Matrix.add_cons, Matrix.empty_add_empty,
    EmbeddingLike.apply_eq_iff_eq, mul_one, zero_mul]
  have hα' : (α : v.adicCompletion F) ≠ 0 := (Subtype.coe_ne_coe).mpr hα
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] <;>
    field_simp

variable (v) in
/-- The double coset space `U0 · diag(α,1) · U0` as a set of left cosets modulo `U0`. -/
noncomputable def U0diagU0 :
    Set (GL (Fin 2) (adicCompletion F v) ⧸ (U0 v)) :=
  QuotientGroup.mk '' ((U0 v : Set _) * {diag α hα})

variable (v) in
/-- The `|O_v/α| + 1` coset representatives for `U0 · diag · U0 / U0`, indexed by
`Option (O_v / αO_v)`. `some t` maps to `unipotent_mul_diag t`, `none` maps to `diag'`. -/
noncomputable def T_cosets
    (t : Option (↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α}))) :
    GL (Fin 2) (adicCompletion F v) ⧸ ↑(U0 v) :=
  match t with
  | none => QuotientGroup.mk (diag' α hα)
  | some s => QuotientGroup.mk (unipotent_mul_diag α hα (Quotient.out s))

/-- `T_cosets` maps into `U0diagU0` for all `t`. -/
lemma mapsTo_T_cosets_U0diagU0 :
    Set.MapsTo (T_cosets v α hα) ⊤ (U0diagU0 v α hα) := by
  intro t _
  cases t with
  | none =>
    -- diag' ∈ U0 * {diag}: since swap · diag · swap = diag' and swap ∈ U0,
    -- we have mk(diag') = mk(swap · diag), which is in mk(U0 · {diag}).
    simp only [T_cosets, U0diagU0]
    -- Swap matrix in GL₂
    set sw : GL (Fin 2) (adicCompletion F v) :=
      ⟨!![0, 1; (1 : adicCompletion F v), 0],
       !![0, 1; (1 : adicCompletion F v), 0], by
        ext i j; fin_cases i <;> fin_cases j <;> simp, by
        ext i j; fin_cases i <;> fin_cases j <;> simp⟩
    have hsw_mem : sw ∈ U0 v := by
      apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
      constructor
      · intro i j; fin_cases i <;> fin_cases j <;> simp [sw]
      · simp [sw, Matrix.det_fin_two]
    -- Show mk(diag') = mk(sw * diag) by showing diag'⁻¹ * (sw * diag) ∈ U0.
    -- Since sw ∈ U0, sw * diag ∈ U0 * {diag}, so mk(sw * diag) ∈ U0diagU0.
    -- We just need diag'⁻¹ * sw * diag ∈ U0.
    refine ⟨sw * diag α hα, Set.mul_mem_mul hsw_mem rfl, ?_⟩
    -- Goal: mk(diag') = mk(sw * diag)
    -- i.e., (diag')⁻¹ * (sw * diag) ∈ U0
    -- Goal: mk(diag') = mk(sw * diag). Use symm + QuotientGroup.eq.
    symm
    apply QuotientGroup.eq.mpr
    -- Goal: (sw * diag)⁻¹ * diag' ∈ U0. Show it equals sw via convert.
    convert hsw_mem using 1
    -- Remaining: (sw * diag)⁻¹ * diag' = sw
    set_option maxHeartbeats 800000 in
    apply Units.ext; ext i j
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_inv_eq_inv_val, Matrix.mul_inv_rev]
    push_cast [diag_def, diag'_def, sw]
    simp only [Matrix.inv_def, Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, zero_sub,
      Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, neg_zero, neg_neg, neg_mul,
      Matrix.smul_of, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zero_mul, one_mul, mul_one, mul_zero,
      add_zero, zero_add, Matrix.mul_apply, Fin.sum_univ_two]
    have hα' : (α : v.adicCompletion F) ≠ 0 := (Subtype.coe_ne_coe).mpr hα
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  | some s =>
    -- unipotent_mul_diag t = unipotent(t) * diag, and unipotent(t) ∈ U0
    apply Set.mem_image_of_mem QuotientGroup.mk
    exact Set.mul_mem_mul
      ((unipotent_mem_U1 (Quotient.out s)).1)
      rfl

/-- `diag'` and `unipotent_mul_diag` give distinct `U0`-cosets: the ratio
`(diag')⁻¹ * unipotent_mul_diag(t)` has a `(1,1)` entry `α⁻¹`, which is not in `O_v`
when `α` is not a unit. -/
lemma T_cosets_none_ne_some (hα_nonunit : ¬IsUnit α)
    (t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α})) :
    T_cosets v α hα none ≠ T_cosets v α hα (some t) := by
  intro h
  simp only [T_cosets] at h
  -- h : mk(diag') = mk(unipotent_mul_diag(Quotient.out t))
  -- So (diag')⁻¹ * unipotent_mul_diag(Quotient.out t) ∈ U0
  have hmem := QuotientGroup.eq.mp h
  -- Extract v-value bound on (1,1) entry from membership in U0.
  have h11 := GL2.v_le_one_of_mem_localFullLevel _ hmem 1 1
  -- Compute the (1,1) entry: (diag')⁻¹ * unipotent_mul_diag(t)
  -- = !![1,0;0,α⁻¹] * !![α,t;0,1] has (1,1) = α⁻¹.
  simp only [Units.val_mul, unipotent_mul_diag, unipotent, Matrix.unitOfDetInvertible,
    val_unitOfInvertible, diag_def, diag'_inv_val, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, zero_mul, one_mul, mul_one, mul_zero, add_zero, zero_add] at h11
  -- h11 : Valued.v (↑α)⁻¹ ≤ 1 means α⁻¹ ∈ O_v.
  -- Combined with α ∈ O_v, α is a unit in O_v. Contradiction with hα_nonunit.
  have hα_ne : (α : v.adicCompletion F) ≠ 0 := (Subtype.coe_ne_coe).mpr hα
  -- α ∈ O_v means v(α) ≤ 1, and h11 says v(α⁻¹) ≤ 1.
  -- Since v(α) * v(α⁻¹) = 1 (for nonzero α), both ≤ 1 implies both = 1.
  -- v(α) = 1 means α is a unit in O_v.
  -- h11 : v(α⁻¹) ≤ 1 means α⁻¹ ∈ O_v. Since α ∈ O_v and α⁻¹ ∈ O_v, α is a unit.
  exact hα_nonunit (⟨⟨α, ⟨(α : v.adicCompletion F)⁻¹, h11⟩,
    by ext; simp [mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα)],
    by ext; simp [inv_mul_cancel₀ ((Subtype.coe_ne_coe).mpr hα)]⟩, rfl⟩)

/-- Distinct `T_cosets` entries give distinct cosets. -/
lemma injOn_T_cosets (hα_nonunit : ¬IsUnit α) :
    Set.InjOn (T_cosets v α hα) ⊤ := by
  intro t₁ _ t₂ _ h
  cases t₁ with
  | none =>
    cases t₂ with
    | none => rfl
    | some s₂ => exact absurd h (T_cosets_none_ne_some α hα hα_nonunit s₂)
  | some s₁ =>
    cases t₂ with
    | none => exact absurd h.symm (T_cosets_none_ne_some α hα hα_nonunit s₁)
    | some s₂ =>
      -- Same argument as injOn_unipotent_mul_diagU1 but with U0 instead of U1.
      -- If mk(unipotent_mul_diag s₁) = mk(unipotent_mul_diag s₂) then
      -- (unipotent_mul_diag s₁)⁻¹ * unipotent_mul_diag s₂ ∈ U0 = GL₂(O_v).
      -- The (0,1) entry of the ratio is α⁻¹(s₂ - s₁) which must be in O_v.
      -- This forces s₁ = s₂ in O_v/α.
      congr 1
      simp only [T_cosets] at h
      have hratio : (unipotent_mul_diag α hα (Quotient.out s₁))⁻¹ *
          (unipotent_mul_diag α hα (Quotient.out s₂)) ∈ U0 v :=
        QuotientGroup.eq.mp h
      -- The ratio is a unipotent matrix by unipotent_mul_diag_inv_mul_unipotent_mul_diag.
      -- Its (0,1) entry α⁻¹(s₂ - s₁) must be in O_v (from membership in localFullLevel).
      have h01_int :=
        GL2.v_le_one_of_mem_localFullLevel _ hratio 0 1
      rw [unipotent_mul_diag_inv_mul_unipotent_mul_diag] at h01_int
      simp only [unipotent, Matrix.unitOfDetInvertible, Fin.isValue, val_unitOfInvertible,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero] at h01_int
      rw [← (QuotientAddGroup.out_eq' s₁), ← (QuotientAddGroup.out_eq' s₂)]
      apply QuotientAddGroup.eq.mpr; apply Ideal.mem_span_singleton'.mpr
      use ⟨_, h01_int⟩
      apply (Subtype.coe_inj).mp; push_cast
      ring_nf; rw [mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]

/-- Every coset in `U0diagU0` is of the form `T_cosets t` for some `t`.
Requires `α` to be a uniformizer (generates the maximal ideal). -/
lemma surjOn_T_cosets_U0diagU0
    (hα_irred : Irreducible α) :
    Set.SurjOn (T_cosets v α hα) ⊤ (U0diagU0 v α hα) := by
  rintro _ ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩
  -- x ∈ U0 = GL₂(O_v). Write x = !![a,b;c,d] with entries in O_v.
  let a : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 0⟩
  let b : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 1⟩
  let c : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 0⟩
  let d : adicCompletionIntegers F v := ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  -- Case split: is d a unit in O_v?
  by_cases hd : IsUnit d
  · -- Case 1: d is a unit. Same as surjOn_unipotent_mul_diagU1_U1diagU1.
    -- Choose t = ⅟d * b, then unipotent_mul_diag(t)⁻¹ * (x * diag) ∈ U0.
    letI invertible_d := hd.invertible
    let t : ↑(adicCompletionIntegers F v) ⧸ (Ideal.span {α}) := (⅟d * b)
    use (some t)
    constructor
    · trivial
    · -- mk(T_cosets(some t)) = mk(x * diag)
      -- t = ⅟d * b. The ratio (unipotent_mul_diag(out t))⁻¹ * (x * diag) is in U0
      -- because diag⁻¹ * (unipotent(-out_t) * x) * diag has all entries in O_v:
      -- entry (0,1) = α⁻¹(b - out_t * d) ∈ O_v since b - out_t * d ∈ Ideal.span {α}.
      simp only [T_cosets]
      apply QuotientGroup.eq.mpr
      unfold unipotent_mul_diag; rw [mul_inv_rev, ← mul_assoc, mul_assoc _ _ x]
      -- Show diag⁻¹ * (unipotent(-out_t) * x) * diag ∈ U0 = localFullLevel.
      -- Use mem_localFullLevel_iff to check entries and det.
      have ht : (b + -Quotient.out t * d) ∈ Ideal.span {α} := by
        apply Ideal.mem_span_singleton'.mpr
        have t_def : (Ideal.Quotient.mk (Ideal.span {α})) (Quotient.out t) = (⅟d * b) := by
          simp only [Ideal.Quotient.mk_out]; rfl
        obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp t_def)
        use -d * q; rw [mul_assoc, hq]; ring_nf; simp
      -- Use the helper: diag⁻¹ * (unipotent(-out_t) * x) * diag ∈ U0
      -- when the (0,1) entry of (unipotent(-out_t) * x) is in Ideal.span {α}.
      refine conjBy_diag_mem_U0_of_apply_zero_one_mem_ideal (α := α) (hα := hα)
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ ((unipotent_mem_U1 _).1)) hx) ?_
      -- (0,1) entry of (unipotent(-out_t) * x) is b + (-out_t)*d ∈ Ideal.span {α}
      simp only [Fin.isValue, Units.val_mul, Matrix.coe_units_inv, unipotent_def, Matrix.inv_def,
        Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, Ring.inverse_one,
        Matrix.adjugate_fin_two_of, neg_zero, one_smul, hx₁, Matrix.mul_apply, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.sum_univ_two, one_mul]
      exact_mod_cast ht
  · -- Case 2: d is not a unit. Since α is irreducible, α generates maximalIdeal.
    -- Every non-unit in O_v is in maximalIdeal = Ideal.span {α}, so α | d.
    have hd_mem : d ∈ Ideal.span {α} := by
      rw [← hα_irred.maximalIdeal_eq]
      exact (IsLocalRing.mem_maximalIdeal d).mpr hd
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton'.mp hd_mem
    -- mk(x * diag) = mk(diag') = T_cosets(none)
    use none
    constructor
    · trivial
    · simp only [T_cosets]
      apply QuotientGroup.eq.mpr
      -- Goal: (diag')⁻¹ * (x * diag) ∈ U0 = localFullLevel v
      -- (diag')⁻¹ * x * diag = !![a*α, b; c, d*α⁻¹] by conjBy_diag'_diag.
      -- Since d = α*d', d*α⁻¹ = d'. All entries in O_v, det = det(x) ∈ O_v^×.
      apply GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one.mpr
      have hα_ne : (α : v.adicCompletion F) ≠ 0 := (Subtype.coe_ne_coe).mpr hα
      constructor
      · -- All entries have v-value ≤ 1.
        intro i j
        -- Rewrite using diag'_inv_val and matrix multiplication
        simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
          diag'_inv_val, diag_def]
        push_cast [hx₁]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, zero_mul, one_mul, mul_one, mul_zero, add_zero, zero_add]
        fin_cases i <;> fin_cases j <;>
          simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
            Matrix.cons_val_zero, Matrix.cons_val_fin_one,
            Fin.mk_one, Matrix.cons_val_one,
            mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add]
        · -- (0,0): a * α ∈ O_v
          exact_mod_cast (a * α).2
        · -- (0,1): b ∈ O_v
          exact GL2.v_le_one_of_mem_localFullLevel _ hx 0 1
        · -- (1,0): (α⁻¹ * c * α) = c ∈ O_v
          rw [show (↑α : adicCompletion F v)⁻¹ * (↑c * ↑α) = ↑c from by
            field_simp]
          exact GL2.v_le_one_of_mem_localFullLevel _ hx 1 0
        · -- (1,1): α⁻¹ * (c * 0 + d * 1) = α⁻¹ * d = d' since d = α*d'
          -- The entry is α⁻¹ * d = d' since d' * α = d (from hd')
          have hdd : (x.val 1 1 : adicCompletion F v) = (d' : adicCompletion F v) * (α : adicCompletion F v) := by
            have := congrArg (Subtype.val (p := fun x => x ∈ adicCompletionIntegers F v)) hd'
            push_cast at this; exact this.symm
          have hα_ne' := (Subtype.coe_ne_coe).mpr hα
          rw [show (d : adicCompletion F v) = x.val 1 1 from rfl, hdd]
          rw [show (↑α : adicCompletion F v)⁻¹ * (↑d' * ↑α) = ↑d' from by
            rw [mul_comm (↑d' : adicCompletion F v) ↑α, ← mul_assoc, inv_mul_cancel₀ hα_ne', one_mul]]
          exact d'.2
      · -- det = det(x): det(diag'⁻¹) * det(x) * det(diag) = α⁻¹ * det(x) * α = det(x).
        sorry

variable (v) in
/-- The double coset `U0 · diag · U0 / U0` is in bijection with `Option (O_v / αO_v)`.
Requires `α` to be a uniformizer (irreducible). -/
theorem bijOn_T_cosets_U0diagU0
    (hα_irred : Irreducible α) :
    Set.BijOn (T_cosets v α hα) ⊤ (U0diagU0 v α hα) :=
  ⟨mapsTo_T_cosets_U0diagU0 α hα,
    injOn_T_cosets α hα hα_irred.1,
    surjOn_T_cosets_U0diagU0 α hα hα_irred⟩

end TCosetFullLevel

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
