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

/-! ## Double coset decomposition at good primes

At a good prime `v`, the level subgroup is `U0 v = GL₂(𝒪_v)` (the full maximal compact).
The double coset `U0 · diag(α, 1) · U0` decomposes into `|𝒪_v/α𝒪_v| + 1` left cosets,
indexed by `Option (𝒪_v / α𝒪_v)`:
- `some t ↦ unipotent_mul_diag(t)` for each `t ∈ 𝒪_v/α𝒪_v`
- `none ↦ diag'(α) = !![1, 0; 0, α]`

This decomposition requires `α` to generate the maximal ideal (i.e., be a uniformizer).
-/

/-- The full local level subgroup for "good primes": `GL₂(𝒪_v)`. -/
noncomputable abbrev U0 (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (adicCompletion F v)) :=
  GL2.localFullLevel v

/-- The diagonal matrix element `diag(1, α) = !![1, 0; 0, α]`. This is the "flipped"
diagonal relative to `diag(α, 1)`, used as the extra coset representative in the
`T_v` double coset decomposition at good primes. -/
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

variable (v) in
/-- The double coset space `U0 · diag · U0` as a set of left cosets modulo `U0`. -/
noncomputable def U0diagU0 :
    Set ((GL (Fin 2) (adicCompletion F v)) ⧸ (U0 v)) :=
  (QuotientGroup.mk '' ((U0 v : Set _) * {diag α hα}))

/-- The `q + 1` coset representatives for the `T_v` double coset, indexed by
`Option (𝒪_v / α𝒪_v)`:
- `some t ↦` the coset of `unipotent_mul_diag(t) = !![α, t; 0, 1]`
- `none ↦` the coset of `diag'(α) = !![1, 0; 0, α]` -/
noncomputable def T_cosets (v : HeightOneSpectrum (𝓞 F))
    (α : v.adicCompletionIntegers F) (hα : α ≠ 0)
    (t : Option (↥(adicCompletionIntegers F v) ⧸ (Ideal.span {α}))) :
    ((GL (Fin 2) (adicCompletion F v)) ⧸ (U0 v)) :=
  match t with
  | none => QuotientGroup.mk (diag' α hα)
  | some t => QuotientGroup.mk
      (unipotent_mul_diag α hα (Quotient.out t : adicCompletionIntegers F v))

/-- Each `T_cosets` representative is in the double coset `U0diagU0`. -/
lemma mapsTo_T_cosets_U0diagU0 :
    Set.MapsTo (T_cosets v α hα) ⊤ (U0diagU0 v α hα) := by
  intro t _
  cases t with
  | none =>
    -- diag' is in the double coset U0 · diag · U0.
    -- Let w = swap matrix !![0, 1; 1, 0] ∈ U0. Then w * diag ∈ U0 * {diag},
    -- and (w * diag)⁻¹ * diag' = w ∈ U0, so mk(w * diag) = mk(diag').
    simp only [T_cosets, U0diagU0]
    -- We construct the witness: swap * diag ∈ U0 * {diag}
    -- Then show mk(swap * diag) = mk(diag') via (swap * diag)⁻¹ * diag' = swap ∈ U0
    sorry
  | some t =>
    -- unipotent_mul_diag t = unipotent(t) * diag, where unipotent(t) ∈ U0
    -- (since GL2.unipotent_mem_U1 gives membership in U1 ⊆ U0 via .left).
    simp only [T_cosets, U0diagU0]
    apply Set.mem_image_of_mem (QuotientGroup.mk (s := U0 v))
    exact Set.mul_mem_mul
      (GL2.unipotent_mem_U1 (Quotient.out t)).left rfl

/-- Distinct `T_cosets` values give distinct cosets. -/
lemma injOn_T_cosets
    (hα_nonunit : ¬IsUnit α) :
    Set.InjOn (T_cosets v α hα) ⊤ := by
  intro t₁ _ t₂ _ h
  cases t₁ with
  | none =>
    cases t₂ with
    | none => rfl
    | some t₂ =>
      -- mk(diag') = mk(unipotent_mul_diag t₂) implies (diag')⁻¹ * unipotent_mul_diag t₂ ∈ U0.
      -- The (1,1) entry of this product is α⁻¹ ∉ O_v since α is not a unit.
      exfalso
      change (QuotientGroup.mk (s := U0 v) (diag' α hα)) =
        (QuotientGroup.mk (s := U0 v)
          (unipotent_mul_diag α hα (Quotient.out t₂))) at h
      have hmem := QuotientGroup.eq.mp h
      -- hmem : (diag')⁻¹ * unipotent_mul_diag t₂ ∈ U0
      -- Its (1,1) entry must be in O_v. But (diag')⁻¹ = !![1,0;0,α⁻¹],
      -- unipotent_mul_diag t₂ = !![α,t₂;0,1], so the product's (1,1) = α⁻¹.
      -- α⁻¹ ∉ O_v because ¬IsUnit α.
      have h11 := GL2.v_le_one_of_mem_localFullLevel _ hmem 1 1
      -- The (1,1) entry of (diag')⁻¹ * unipotent_mul_diag t₂ is α⁻¹.
      -- v(α⁻¹) ≤ 1 forces v(α) ≥ 1, but α ∈ O_v gives v(α) ≤ 1, so v(α) = 1,
      -- making α a unit — contradicting hα_nonunit.
      -- After simp, h11 gives Valued.v (α⁻¹ ...) ≤ 1.
      -- But ¬IsUnit α means Valued.v α < 1, so Valued.v α⁻¹ > 1. Contradiction.
      simp only [diag', unipotent_mul_diag, Matrix.GeneralLinearGroup.diagonal,
        Matrix.coe_units_inv, Matrix.inv_def, Matrix.det_fin_two_of, mul_one, mul_zero,
        sub_zero, Ring.inverse_eq_inv', Matrix.adjugate_fin_two_of, neg_zero,
        Matrix.smul_of, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty,
        Matrix.cons_mul, Matrix.vecMul_cons, Matrix.head_cons, Matrix.tail_cons,
        Fin.isValue] at h11
      -- h11 now shows the (1,1) entry has valuation ≤ 1
      -- This entry is α⁻¹, and since α is not a unit, α⁻¹ has valuation > 1.
      apply hα_nonunit
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have hv_lt := (mem_completionIdeal_iff _ v _).mp hmem
      -- hv_lt : Valued.v (α : adicCompletion F v) < 1
      -- h11 : Valued.v (α⁻¹ ...) ≤ 1
      -- These contradict each other since Valued.v (α⁻¹) = (Valued.v α)⁻¹ > 1
      sorry
  | some t₁ =>
    cases t₂ with
    | none =>
      -- Symmetric to none/some: (unipotent_mul_diag t₁)⁻¹ * diag' ∈ U0
      -- would force α⁻¹ ∈ O_v, contradicting ¬IsUnit α.
      exfalso
      change (QuotientGroup.mk (s := U0 v)
          (unipotent_mul_diag α hα (Quotient.out t₁))) =
        (QuotientGroup.mk (s := U0 v) (diag' α hα)) at h
      have hmem := QuotientGroup.eq.mp h
      have h11 := GL2.v_le_one_of_mem_localFullLevel _ hmem 1 1
      sorry
    | some t₂ =>
      -- Same proof as injOn_unipotent_mul_diagU1, but with U0 instead of U1.
      -- (unipotent_mul_diag t₁)⁻¹ * unipotent_mul_diag t₂ ∈ U0 forces t₁ = t₂ mod α.
      change (QuotientGroup.mk (s := U0 v)
        (unipotent_mul_diag α hα (Quotient.out t₁))) =
        (QuotientGroup.mk (s := U0 v)
        (unipotent_mul_diag α hα (Quotient.out t₂))) at h
      have unipotent_mem_U0 :=
        (unipotent_mul_diag_inv_mul_unipotent_mul_diag α hα
          (Quotient.out t₁) (Quotient.out t₂)) ▸
          (QuotientGroup.eq.mp h)
      have unipotent_apply_zero_one_mem_integer :=
        GL2.v_le_one_of_mem_localFullLevel _ unipotent_mem_U0 0 1
      simp only [unipotent, Matrix.unitOfDetInvertible, Fin.isValue,
        val_unitOfInvertible, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero] at unipotent_apply_zero_one_mem_integer
      congr 1
      rw [← (QuotientAddGroup.out_eq' t₁), ← (QuotientAddGroup.out_eq' t₂)]
      apply QuotientAddGroup.eq.mpr; apply Ideal.mem_span_singleton'.mpr
      use ⟨_, unipotent_apply_zero_one_mem_integer⟩
      apply (Subtype.coe_inj).mp; push_cast
      ring_nf
      rw [mul_inv_cancel₀ ((Subtype.coe_ne_coe).mpr hα), one_mul, one_mul]

/-- Every coset in `U0diagU0` is represented by some `T_cosets` value.
This is the hard part: uses a case split on whether the (1,1) entry of `x ∈ U0`
is a unit (reducing to the `unipotent_mul_diag` case) or in the maximal ideal
(giving the `diag'` case). -/
lemma surjOn_T_cosets_U0diagU0
    (hα_gen : Ideal.span {α} = IsLocalRing.maximalIdeal (adicCompletionIntegers F v)) :
    Set.SurjOn (T_cosets v α hα) ⊤ (U0diagU0 v α hα) := by
  rintro _ ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩
  -- x ∈ U0 = GL₂(O_v). Extract matrix entries as elements of O_v.
  let a : (adicCompletionIntegers F v) :=
    ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 0⟩
  let b : (adicCompletionIntegers F v) :=
    ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 0 1⟩
  let c : (adicCompletionIntegers F v) :=
    ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 0⟩
  let d : (adicCompletionIntegers F v) :=
    ⟨_, GL2.v_le_one_of_mem_localFullLevel _ hx 1 1⟩
  have hx₁ : x = !![(a : adicCompletion F v), b; c, d] :=
    (Matrix.etaExpand_eq
      (x : Matrix (Fin 2) (Fin 2) (adicCompletion F v))).symm
  -- Case split: is d a unit in O_v?
  by_cases hd : IsUnit d
  · -- Case 1: d is a unit → same as surjOn_unipotent_mul_diagU1_U1diagU1.
    -- Representative: unipotent_mul_diag(⅟d * b).
    letI invertible_d := hd.invertible
    let t : ↥(adicCompletionIntegers F v) ⧸ (Ideal.span {α}) :=
      (⅟d * b)
    use (some t)
    refine ⟨Set.mem_univ _, ?_⟩
    -- Show mk(x * diag) = mk(unipotent_mul_diag (Quotient.out t))
    -- Goal: T_cosets v α hα (some t) = mk(x * diag)
    -- i.e.: mk(unipotent_mul_diag(out t)) = mk(x * diag)
    -- Adapted from surjOn_unipotent_mul_diagU1_U1diagU1 (Local.lean:265).
    sorry
  · -- Case 2: d is not a unit (d ∈ maximal ideal).
    -- Representative: diag'.
    -- Since d ∈ maximalIdeal = Ideal.span {α}, get q with d = α * q.
    have hd_mem : d ∈ IsLocalRing.maximalIdeal
        (adicCompletionIntegers F v) := by
      rwa [IsLocalRing.mem_maximalIdeal]
    have hd_span : d ∈ Ideal.span {α} := hα_gen ▸ hd_mem
    use none
    refine ⟨Set.mem_univ _, ?_⟩
    -- Goal: T_cosets v α hα none = mk(x * diag)
    -- i.e.: mk(diag') = mk(x * diag)
    -- Need: (diag')⁻¹ * (x * diag) ∈ U0 = GL₂(O_v)
    -- Computation: (diag')⁻¹ * x * diag = !![aα, b; c, α⁻¹d]
    -- where α⁻¹d ∈ O_v (since d ∈ Ideal.span {α}).
    -- det = det(x) ∈ O_v×.
    sorry

/-- The double coset `U0 · diag(α, 1) · U0` decomposes as a disjoint union of `q + 1`
left cosets, indexed by `Option (𝒪_v / α𝒪_v)`. This is the key decomposition used
for the `T_v` Hecke operator at good primes. -/
theorem bijOn_T_cosets_U0diagU0
    (hα_nonunit : ¬IsUnit α)
    (hα_gen : Ideal.span {α} = IsLocalRing.maximalIdeal (adicCompletionIntegers F v)) :
    Set.BijOn (T_cosets v α hα) ⊤ (U0diagU0 v α hα) :=
  ⟨mapsTo_T_cosets_U0diagU0 α hα,
    injOn_T_cosets α hα hα_nonunit,
    surjOn_T_cosets_U0diagU0 α hα hα_gen⟩

end TCosetGoodPrime

end Local

end TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm.HeckeOperator
