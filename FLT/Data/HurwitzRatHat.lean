import FLT.Data.Hurwitz
import FLT.Data.QHat

open scoped TensorProduct

/-- The base change of the Hurwitz quaternions to ZHat. -/
noncomputable def HurwitzHat : Type := 𝓞 ⊗[ℤ] ZHat

namespace HurwitzHat

/-- The base change of the Hurwitz quaternions to ZHat. -/
scoped notation "𝓞^" => HurwitzHat

noncomputable instance : Ring 𝓞^ := Algebra.TensorProduct.instRing

/-- `𝓞^` is torsion-free as an additive group: this follows from `Module.Flat ℤ 𝓞^`,
which holds because both `𝓞` and `ZHat` are flat over `ℤ`. -/
instance : IsAddTorsionFree 𝓞^ := by
  haveI : NoZeroDivisors 𝓞 := ⟨fun {a b} hab => by
    have hn : Hurwitz.norm a * Hurwitz.norm b = 0 := by
      rw [← Hurwitz.norm_mul]; exact (Hurwitz.norm_eq_zero _).mpr hab
    rcases mul_eq_zero.mp hn with h | h
    · exact Or.inl ((Hurwitz.norm_eq_zero _).mp h)
    · exact Or.inr ((Hurwitz.norm_eq_zero _).mp h)⟩
  haveI : IsDomain 𝓞 := NoZeroDivisors.to_isDomain _
  haveI : IsAddTorsionFree 𝓞 := IsDomain.instIsAddTorsionFreeOfCharZero _
  haveI : Module.Flat ℤ 𝓞 := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  haveI : Module.Flat ℤ (𝓞 ⊗[ℤ] ZHat) := inferInstance
  haveI : Module.Flat ℤ 𝓞^ := by change Module.Flat ℤ (𝓞 ⊗[ℤ] ZHat); infer_instance
  rw [← Module.isTorsionFree_int_iff_isAddTorsionFree]
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact Module.Flat.torsion_eq_bot

/-- The map `𝓞 → 𝓞^` sending `y` to `y ⊗ₜ 1` is surjective modulo `N`.
That is, every element of `𝓞 ⊗[ℤ] ZHat` is congruent to an element of `𝓞` modulo `N`. -/
lemma surjective_pnat_quotient (N : ℕ+) (z : 𝓞 ⊗[ℤ] ZHat) :
    ∃ (y : 𝓞) (w : 𝓞 ⊗[ℤ] ZHat), z = y ⊗ₜ[ℤ] 1 + (N : ℤ) • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a w₀ =>
    obtain ⟨q, r, hqr, _⟩ := ZHat.nat_dense N w₀
    refine ⟨(r : ℤ) • a, a ⊗ₜ[ℤ] q, ?_⟩
    rw [hqr, TensorProduct.tmul_add]
    have h1 : a ⊗ₜ[ℤ] ((r : ℕ) : ZHat) = ((r : ℤ) • a) ⊗ₜ[ℤ] (1 : ZHat) := by
      have : ((r : ℕ) : ZHat) = (r : ℤ) • (1 : ZHat) := by
        rw [zsmul_eq_mul, mul_one]; push_cast; rfl
      rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have h2 : a ⊗ₜ[ℤ] ((N : ℕ) * q : ZHat) = (N : ℤ) • (a ⊗ₜ[ℤ] q) := by
      have : ((N : ℕ) * q : ZHat) = (N : ℤ) • q := by
        rw [zsmul_eq_mul]; push_cast; rfl
      rw [this, TensorProduct.tmul_smul]
    rw [h1, h2]
    abel
  | add x y hx hy =>
    obtain ⟨y₁, w₁, hx⟩ := hx
    obtain ⟨y₂, w₂, hy⟩ := hy
    refine ⟨y₁ + y₂, w₁ + w₂, ?_⟩
    rw [hx, hy, TensorProduct.add_tmul, smul_add]
    abel

end HurwitzHat

/-- The quaternion algebra ℚ + ℚi + ℚj + ℚk. -/
noncomputable def HurwitzRat : Type := ℚ ⊗[ℤ] 𝓞

namespace HurwitzRat

/-- The quaternion algebra ℚ + ℚi + ℚj + ℚk. -/
scoped notation "D" => HurwitzRat

noncomputable instance : Ring D := Algebra.TensorProduct.instRing

/-- For nonzero `α : 𝓞`, the element `1 ⊗ₜ α : D` has the explicit two-sided inverse
`(norm α)⁻¹ ⊗ₜ star α : D`. This is because `α * star α = star α * α = norm α : ℤ` (central). -/
lemma one_tmul_mul_inv_eq_one (α : 𝓞) (hα : α ≠ 0) :
    ((1 : ℚ) ⊗ₜ[ℤ] α : D) *
      (((Hurwitz.norm α : ℚ)⁻¹ ⊗ₜ[ℤ] star α : D)) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  -- ((norm α)⁻¹) ⊗ (α * star α) = 1
  rw [show ((α * star α : 𝓞)) = (((Hurwitz.norm α) : 𝓞)) from
    (Hurwitz.norm_eq_mul_conj α).symm]
  -- Pull the integer (norm α) through the tensor: q ⊗ (n : 𝓞) = (n • q) ⊗ 1
  rw [show ((Hurwitz.norm α : 𝓞)) = ((Hurwitz.norm α : ℤ) • (1 : 𝓞)) from by
    rw [zsmul_eq_mul, mul_one]]
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  -- ((norm α : ℤ) • ((norm α)⁻¹ : ℚ)) ⊗ 1 = 1
  change (((Hurwitz.norm α : ℤ) • (Hurwitz.norm α : ℚ)⁻¹) ⊗ₜ[ℤ] (1 : 𝓞)) = (1 : D)
  rw [zsmul_eq_mul]
  have : (Hurwitz.norm α : ℚ) ≠ 0 := by
    have := Hurwitz.norm_pos_of_ne_zero hα
    exact_mod_cast this.ne'
  rw [mul_inv_cancel₀ this]
  rfl

/-- `star α * α = (norm α : 𝓞)` in 𝓞 — companion to `Hurwitz.norm_eq_mul_conj`. -/
private lemma star_mul_self_eq_norm (α : 𝓞) :
    (Hurwitz.norm α : 𝓞) = star α * α := by
  ext <;> simp only [Hurwitz.intCast_re, Hurwitz.intCast_im_o, Hurwitz.intCast_im_i,
    Hurwitz.intCast_im_oi, Hurwitz.mul_re, Hurwitz.mul_im_o, Hurwitz.mul_im_i, Hurwitz.mul_im_oi,
    Hurwitz.star_re, Hurwitz.star_im_o, Hurwitz.star_im_i, Hurwitz.star_im_oi, Hurwitz.norm] <;>
    ring

/-- The "inverse direction": `((norm α)⁻¹ ⊗ₜ star α) * (1 ⊗ₜ α) = 1` in D. -/
lemma inv_mul_one_tmul_eq_one (α : 𝓞) (hα : α ≠ 0) :
    (((Hurwitz.norm α : ℚ)⁻¹ ⊗ₜ[ℤ] star α : D)) *
      ((1 : ℚ) ⊗ₜ[ℤ] α : D) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [show ((star α * α : 𝓞)) = ((Hurwitz.norm α : 𝓞)) from (star_mul_self_eq_norm α).symm]
  rw [show ((Hurwitz.norm α : 𝓞)) = ((Hurwitz.norm α : ℤ) • (1 : 𝓞)) from by
    rw [zsmul_eq_mul, mul_one]]
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  change (((Hurwitz.norm α : ℤ) • (Hurwitz.norm α : ℚ)⁻¹) ⊗ₜ[ℤ] (1 : 𝓞)) = (1 : D)
  rw [zsmul_eq_mul]
  have : (Hurwitz.norm α : ℚ) ≠ 0 := by
    have := Hurwitz.norm_pos_of_ne_zero hα
    exact_mod_cast this.ne'
  rw [mul_inv_cancel₀ this]
  rfl

/-- For nonzero `α : 𝓞`, the embedding `1 ⊗ₜ α : D` is a unit, with explicit inverse
`(norm α)⁻¹ ⊗ₜ star α`. -/
noncomputable def oneTmulUnit (α : 𝓞) (hα : α ≠ 0) : Dˣ where
  val := (1 : ℚ) ⊗ₜ[ℤ] α
  inv := ((Hurwitz.norm α : ℚ)⁻¹ ⊗ₜ[ℤ] star α : D)
  val_inv := one_tmul_mul_inv_eq_one α hα
  inv_val := inv_mul_one_tmul_eq_one α hα

end HurwitzRat

open scoped HurwitzRat HurwitzHat

/-- The "profinite Hurwitz quaternions" over the finite adeles of ℚ; a free rank 4 module
generated by 1, i, j, and (1+i+j+k)/2. -/
noncomputable def HurwitzRatHat : Type := D ⊗[ℤ] ZHat

namespace HurwitzRatHat

/-- The "profinite Hurwitz quaternions" over the finite adeles of ℚ; a free rank 4 module
generated by 1, i, j, and (1+i+j+k)/2. -/
scoped notation "D^" => HurwitzRatHat

noncomputable instance : Ring D^ := Algebra.TensorProduct.instRing

/-- The inclusion from D=ℚ+ℚi+ℚj+ℚk to D ⊗ 𝔸, with 𝔸 the finite adeles of ℚ. -/
noncomputable abbrev j₁ : D →ₐ[ℤ] D^ := Algebra.TensorProduct.includeLeft
-- (Algebra.TensorProduct.assoc ℤ ℚ 𝓞 ZHat).symm.trans Algebra.TensorProduct.includeLeft

lemma injective_hRat :
    Function.Injective j₁ := by
  haveI : NoZeroDivisors 𝓞 := ⟨fun {a b} hab => by
    have hn : Hurwitz.norm a * Hurwitz.norm b = 0 := by
      rw [← Hurwitz.norm_mul]; exact (Hurwitz.norm_eq_zero _).mpr hab
    rcases mul_eq_zero.mp hn with h | h
    · exact Or.inl ((Hurwitz.norm_eq_zero _).mp h)
    · exact Or.inr ((Hurwitz.norm_eq_zero _).mp h)⟩
  haveI : IsDomain 𝓞 := NoZeroDivisors.to_isDomain _
  haveI : IsAddTorsionFree 𝓞 := IsDomain.instIsAddTorsionFreeOfCharZero _
  haveI : Module.Flat ℤ 𝓞 := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  haveI : Module.Flat ℤ D := by
    change Module.Flat ℤ (ℚ ⊗[ℤ] 𝓞)
    infer_instance
  exact Algebra.TensorProduct.includeLeft_injective (Int.cast_injective (α := ZHat))

/-- The inclusion from the profinite Hurwitz quaternions to to 𝔸+𝔸i+𝔸j+𝔸k,
with 𝔸 the finite adeles of ℚ. -/
noncomputable abbrev j₂ : 𝓞^ →ₐ[ℤ] D^ :=
  ((Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat).symm : ℚ ⊗ 𝓞^ ≃ₐ[ℤ] D ⊗ ZHat).toAlgHom.comp
  (Algebra.TensorProduct.includeRight : 𝓞^ →ₐ[ℤ] ℚ ⊗ 𝓞^)

lemma injective_zHat :
    Function.Injective j₂ := by
  haveI : NoZeroDivisors 𝓞 := ⟨fun {a b} hab => by
    have hn : Hurwitz.norm a * Hurwitz.norm b = 0 := by
      rw [← Hurwitz.norm_mul]; exact (Hurwitz.norm_eq_zero _).mpr hab
    rcases mul_eq_zero.mp hn with h | h
    · exact Or.inl ((Hurwitz.norm_eq_zero _).mp h)
    · exact Or.inr ((Hurwitz.norm_eq_zero _).mp h)⟩
  haveI : IsDomain 𝓞 := NoZeroDivisors.to_isDomain _
  haveI : IsAddTorsionFree 𝓞 := IsDomain.instIsAddTorsionFreeOfCharZero _
  haveI : Module.Flat ℤ 𝓞 := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  haveI : Module.Flat ℤ 𝓞^ := by
    change Module.Flat ℤ (𝓞 ⊗[ℤ] ZHat)
    infer_instance
  intro x y hxy
  have := (AlgEquiv.injective
    (Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat).symm) hxy
  exact Algebra.TensorProduct.includeRight_injective (Int.cast_injective (α := ℚ)) this

-- should I rearrange tensors? Not sure if D^ should be (ℚ ⊗ 𝓞) ⊗ ℤhat or ℚ ⊗ (𝓞 ⊗ Zhat)
lemma canonicalForm (z : D^) : ∃ (N : ℕ+) (z' : 𝓞^), z = j₁ ((N⁻¹ : ℚ) ⊗ₜ 1 : D) * j₂ z' := by
  suffices h : ∀ (w : ℚ ⊗[ℤ] 𝓞^), ∃ (N : ℕ+) (z' : 𝓞^), w = (1 / N : ℚ) ⊗ₜ z' by
    obtain ⟨N, z', hw⟩ := h ((Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat) z)
    refine ⟨N, z', ?_⟩
    have hz : z = (Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat).symm
        ((1 / N : ℚ) ⊗ₜ[ℤ] z') := by
      rw [← hw, AlgEquiv.symm_apply_apply]
    rw [hz]
    have hmul : ((1 / N : ℚ) ⊗ₜ[ℤ] z' : ℚ ⊗[ℤ] 𝓞^)
        = ((1 / N : ℚ) ⊗ₜ (1 : 𝓞^)) * ((1 : ℚ) ⊗ₜ z') := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hmul, map_mul]
    have hj1 : ((Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat).symm
        ((1 / N : ℚ) ⊗ₜ (1 : 𝓞^)) : D^)
        = j₁ (((↑↑N : ℚ)⁻¹ : ℚ) ⊗ₜ[ℤ] (1 : 𝓞) : D) := by
      change _ = (((↑↑N : ℚ)⁻¹ ⊗ₜ[ℤ] (1 : 𝓞)) ⊗ₜ[ℤ] (1 : ZHat) : D^)
      rw [one_div]
      rfl
    rw [hj1]
    rfl
  intro w
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, by simp⟩
  | tmul q x =>
    refine ⟨⟨q.den, q.den_pos⟩, q.num • x, ?_⟩
    rw [show (1 / (↑↑⟨q.den, q.den_pos⟩ : ℕ+) : ℚ) = (q.den : ℚ)⁻¹ from by simp [one_div]]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul,
      ← Rat.mul_den_eq_num, mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Rat.den_ne_zero q)), mul_one]
  | add x y hx hy =>
    obtain ⟨N₁, z₁, rfl⟩ := hx
    obtain ⟨N₂, z₂, rfl⟩ := hy
    refine ⟨N₁ * N₂, (N₁ : ℤ) • z₂ + (N₂ : ℤ) • z₁, ?_⟩
    simp only [TensorProduct.tmul_add,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [one_div, PNat.mul_coe, Nat.cast_mul, mul_inv_rev, zsmul_eq_mul, Int.cast_natCast,
      ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
    rw [add_comm]
    congr
    simp [mul_comm]

/-- Rational scalars `j₁(q ⊗ₜ 1)` are central in `D^`: they commute with the image of `j₂`.
This is because `q ⊗ₜ 1 : D` lies in the image of `ℚ → D = ℚ ⊗ 𝓞`, and `ℚ` is the centre of the
rational quaternions. -/
lemma j₁_rat_mul_comm (q : ℚ) (z : 𝓞^) :
    j₁ ((q ⊗ₜ (1 : 𝓞) : D)) * j₂ z = j₂ z * j₁ ((q ⊗ₜ (1 : 𝓞) : D)) := by
  -- Induct on z viewed as an element of 𝓞 ⊗[ℤ] ZHat
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o s =>
    -- Both sides equal `(q ⊗ o) ⊗ s` in `(ℚ ⊗ 𝓞) ⊗ ZHat`
    change ((q ⊗ₜ[ℤ] (1 : 𝓞)) ⊗ₜ[ℤ] (1 : ZHat) : (ℚ ⊗[ℤ] 𝓞) ⊗[ℤ] ZHat) *
        ((Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat).symm
          ((1 : ℚ) ⊗ₜ[ℤ] (o ⊗ₜ[ℤ] s))) =
        ((Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat).symm
          ((1 : ℚ) ⊗ₜ[ℤ] (o ⊗ₜ[ℤ] s))) *
        ((q ⊗ₜ[ℤ] (1 : 𝓞)) ⊗ₜ[ℤ] (1 : ZHat))
    have h1 : (Algebra.TensorProduct.assoc ℤ ℤ ℤ ℚ 𝓞 ZHat).symm
        ((1 : ℚ) ⊗ₜ[ℤ] (o ⊗ₜ[ℤ] s)) =
        (((1 : ℚ) ⊗ₜ[ℤ] o) ⊗ₜ[ℤ] s : (ℚ ⊗[ℤ] 𝓞) ⊗[ℤ] ZHat) := rfl
    rw [h1, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    simp [mul_one, one_mul, mul_comm]
  | add x y hx hy =>
    rw [map_add, mul_add, add_mul, hx, hy]

/-- Helper: given the constraint `j₁((1/N)⊗1) * j₂(a) * (j₁((1/M)⊗1) * j₂(b)) = 1` in `D^`,
we conclude `a * b = NM` in `𝓞^`. The proof uses centrality of `j₁`-images of rationals
plus `injective_zHat` to descend the equality. -/
private lemma j₂_mul_descent
    (N M : ℕ+) (a b : 𝓞^)
    (h : j₁ ((N⁻¹ : ℚ) ⊗ₜ 1 : D) * j₂ a * (j₁ ((M⁻¹ : ℚ) ⊗ₜ 1 : D) * j₂ b) = 1) :
    a * b = ((N * M : ℕ+) : 𝓞^) := by
  apply injective_zHat
  rw [map_mul]
  -- Use centrality to rearrange and combine the rational scalars
  have hcomm : j₂ a * j₁ ((M⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) =
      j₁ ((M⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * j₂ a := (j₁_rat_mul_comm _ a).symm
  -- Step 1: pull out the rational scalars
  have h1 : j₁ ((N⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * j₁ ((M⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * (j₂ a * j₂ b) = 1 := by
    have heq : j₁ ((N⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * j₂ a *
        (j₁ ((M⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * j₂ b) =
        j₁ ((N⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * j₁ ((M⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * (j₂ a * j₂ b) := by
      rw [mul_assoc (j₁ ((N⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D)) (j₂ a),
          ← mul_assoc (j₂ a), hcomm,
          mul_assoc (j₁ ((M⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D)) (j₂ a) (j₂ b),
          ← mul_assoc (j₁ ((N⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D))]
    rw [← heq]; exact h
  -- Step 2: Combine the j₁ rational scalars into j₁((1/(NM)) ⊗ 1)
  have hj1mul : j₁ ((N⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) * j₁ ((M⁻¹ : ℚ) ⊗ₜ (1 : 𝓞) : D) =
      j₁ (((N * M : ℕ+) : ℚ)⁻¹ ⊗ₜ 1 : D) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    push_cast
    rw [mul_inv]
  rw [hj1mul] at h1
  -- h1 : j₁(((NM)⁻¹) ⊗ 1) * (j₂ a * j₂ b) = 1
  -- Step 3: Multiply both sides on the left by j₁(NM ⊗ 1) to extract j₂ a * j₂ b = (NM : D^)
  have hNM : j₁ (((N * M : ℕ+) : ℚ) ⊗ₜ (1 : 𝓞) : D) *
      (j₁ (((N * M : ℕ+) : ℚ)⁻¹ ⊗ₜ (1 : 𝓞) : D) * (j₂ a * j₂ b)) =
      j₁ (((N * M : ℕ+) : ℚ) ⊗ₜ (1 : 𝓞) : D) := by
    rw [h1, mul_one]
  rw [← mul_assoc] at hNM
  rw [show j₁ (((N * M : ℕ+) : ℚ) ⊗ₜ (1 : 𝓞) : D) *
       j₁ (((N * M : ℕ+) : ℚ)⁻¹ ⊗ₜ (1 : 𝓞) : D) = 1 from by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      mul_inv_cancel₀ (by push_cast; positivity : ((N * M : ℕ+) : ℚ) ≠ 0)]
    rfl] at hNM
  rw [one_mul] at hNM
  -- hNM : j₂ a * j₂ b = j₁(((N*M : ℕ+) : ℚ) ⊗ 1)
  rw [hNM]
  -- Goal: j₁((N*M : ℕ+) : ℚ ⊗ 1) = j₂((N*M : ℕ+) : 𝓞^)
  -- Both equal (NM : D^). The cleanest path: cast NM through ℕ.
  have hL : (((N * M : ℕ+) : ℚ) ⊗ₜ[ℤ] (1 : 𝓞) : D) = (((N * M : ℕ+) : ℕ) : D) := by
    -- (↑NM ⊗ₜ 1 : D) = includeLeft (↑NM : ℚ) = (↑NM : D)
    change (Algebra.TensorProduct.includeLeft : ℚ →ₐ[ℤ] D) (((N * M : ℕ+) : ℕ) : ℚ) = _
    rw [map_natCast]
  have hR : ((N * M : ℕ+) : 𝓞^) = (((N * M : ℕ+) : ℕ) : 𝓞^) := by push_cast; rfl
  rw [hL, hR, map_natCast, map_natCast]

lemma completed_units (z : D^ˣ) : ∃ (u : Dˣ) (v : 𝓞^ˣ), (z : D^) = j₁ u * j₂ v := by
  -- Step 1: Apply canonicalForm to z and z⁻¹
  obtain ⟨N, z', hz⟩ := canonicalForm (z : D^)
  obtain ⟨M, w', hzinv⟩ := canonicalForm ((z⁻¹ : (D^)ˣ) : D^)
  -- Step 2: Use j₂_mul_descent twice to get z' * w' = NM and w' * z' = NM in 𝓞^
  have hzw : z' * w' = ((N * M : ℕ+) : 𝓞^) := by
    apply j₂_mul_descent N M z' w'
    rw [← hz, ← hzinv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hwz : w' * z' = ((N * M : ℕ+) : 𝓞^) := by
    have h := j₂_mul_descent M N w' z' (by
      rw [← hzinv, ← hz, ← Units.val_mul, inv_mul_cancel, Units.val_one])
    rw [show (M * N : ℕ+) = N * M from mul_comm _ _] at h
    exact h
  -- Step 3: Form the left ideal I = {a : 𝓞 | (a ⊗ₜ 1 : 𝓞^) ∈ Submodule.span 𝓞^ {w'}}
  let oToOhat : 𝓞 →ₐ[ℤ] 𝓞^ := Algebra.TensorProduct.includeLeft
  let I : Submodule 𝓞 𝓞 := {
    carrier := {a : 𝓞 | oToOhat a ∈ Submodule.span 𝓞^ ({w'} : Set 𝓞^)}
    add_mem' := fun {a b} ha hb => by
      simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
      exact Submodule.add_mem _ ha hb
    zero_mem' := by
      simp only [Set.mem_setOf_eq, map_zero]
      exact Submodule.zero_mem _
    smul_mem' := fun c a ha => by
      simp only [Set.mem_setOf_eq] at ha ⊢
      change oToOhat (c * a) ∈ _
      rw [map_mul]
      exact Submodule.smul_mem _ (oToOhat c) ha
  }
  -- Step 4: NM ∈ I (since (NM : 𝓞^) = z' * w')
  have hoToOhat_natCast : ∀ k : ℕ, oToOhat ((k : 𝓞)) = (k : 𝓞^) := by
    intro k
    change (Algebra.TensorProduct.includeLeft : 𝓞 →ₐ[ℤ] 𝓞^) (k : 𝓞) = _
    rw [map_natCast]
  have hNM_in_I : ((N * M : ℕ+) : 𝓞) ∈ I := by
    show oToOhat ((N * M : ℕ+) : 𝓞) ∈ Submodule.span 𝓞^ ({w'} : Set 𝓞^)
    rw [show ((N * M : ℕ+) : 𝓞) = (((N * M : ℕ+) : ℕ) : 𝓞) from by push_cast; rfl,
      hoToOhat_natCast,
      show (((N * M : ℕ+) : ℕ) : 𝓞^) = ((N * M : ℕ+) : 𝓞^) from by push_cast; rfl,
      ← hzw]
    exact Submodule.smul_mem _ z' (Submodule.mem_span_singleton_self w')
  have hI_ne_bot : I ≠ ⊥ := by
    intro h
    have h0 : ((N * M : ℕ+) : 𝓞) ∈ (⊥ : Submodule 𝓞 𝓞) := h ▸ hNM_in_I
    rw [Submodule.mem_bot] at h0
    have h_pos : ((N * M : ℕ+) : ℕ) > 0 := PNat.pos _
    have h2 : ((((N * M : ℕ+) : ℕ) : 𝓞) : 𝓞) = ((0 : ℕ) : 𝓞) := by
      simp only [Nat.cast_zero]
      have : ((N * M : ℕ+) : 𝓞) = (((N * M : ℕ+) : ℕ) : 𝓞) := by push_cast; rfl
      rw [← this]; exact h0
    have h3 : ((N * M : ℕ+) : ℕ) = 0 := Nat.cast_injective h2
    omega
  -- Step 5: Apply Hurwitz.left_ideal_princ to get α
  obtain ⟨α, hα_eq⟩ := Hurwitz.left_ideal_princ I
  have hα_in_I : α ∈ I := by rw [hα_eq]; exact Submodule.mem_span_singleton_self α
  have hα_ne_zero : α ≠ 0 := by
    intro h
    apply hI_ne_bot
    rw [hα_eq, h, Submodule.span_singleton_eq_bot.mpr rfl]
  -- α has positive norm
  have hnorm_pos : (Hurwitz.norm α) > 0 := Hurwitz.norm_pos_of_ne_zero hα_ne_zero
  -- Step 6: Extract v_ : 𝓞^ with v_ * w' = oToOhat α
  have hα_mem : oToOhat α ∈ Submodule.span 𝓞^ ({w'} : Set 𝓞^) := hα_in_I
  obtain ⟨v_, hv_⟩ := Submodule.mem_span_singleton.mp hα_mem
  -- hv_ : v_ • w' = oToOhat α, which is v_ * w' = oToOhat α (scalar action is multiplication)
  change v_ * w' = oToOhat α at hv_
  -- Step 7: The T-trick. Take T = norm α ∈ ℕ+.
  set T : ℕ+ := (Hurwitz.norm α).toNat.toPNat' with hTdef
  have hT_pos_nat : 0 < (Hurwitz.norm α).toNat := by
    rw [Int.lt_toNat]; exact_mod_cast hnorm_pos
  have hT_coe : (T : ℕ) = (Hurwitz.norm α).toNat := by
    rw [hTdef]; exact PNat.toPNat'_coe hT_pos_nat
  have hT_int : ((T : ℕ) : ℤ) = Hurwitz.norm α := by
    rw [hT_coe]; exact Int.toNat_of_nonneg hnorm_pos.le
  -- Apply surjective_pnat_quotient T w'
  obtain ⟨β, rem, hβrem⟩ := HurwitzHat.surjective_pnat_quotient T w'
  -- hβrem : w' = β ⊗ₜ 1 + (T : ℤ) • rem  (viewed in 𝓞 ⊗[ℤ] ZHat)
  -- Cast everything into 𝓞^.
  let rem' : 𝓞^ := rem
  have hβrem' : w' = oToOhat β + ((T : ℕ) : ℤ) • rem' := hβrem
  have hβ_eq : oToOhat β = w' - ((T : ℕ) : ℤ) • rem' := by
    rw [hβrem']; abel
  -- Step 7a: Show β ∈ I, i.e., oToOhat β ∈ span 𝓞^ {w'}.
  -- Key: (norm α : 𝓞^) ∈ 𝓞^ * w'.
  -- Proof: norm α = star α * α in 𝓞, so oToOhat (norm α) = oToOhat (star α) * oToOhat α
  --   = oToOhat (star α) * (v_ * w') ∈ 𝓞^ * w'.
  have hnormcast : oToOhat (Hurwitz.norm α : 𝓞) = (Hurwitz.norm α : 𝓞^) := by
    change (Algebra.TensorProduct.includeLeft : 𝓞 →ₐ[ℤ] 𝓞^) (Hurwitz.norm α : 𝓞) = _
    rw [map_intCast]
  have h_stara_alpha : oToOhat (star α) * oToOhat α = (Hurwitz.norm α : 𝓞^) := by
    rw [← map_mul, ← HurwitzRat.star_mul_self_eq_norm α, hnormcast]
  have hnorm_in : (Hurwitz.norm α : 𝓞^) ∈ Submodule.span 𝓞^ ({w'} : Set 𝓞^) := by
    rw [← h_stara_alpha, ← hv_, ← mul_assoc]
    exact Submodule.smul_mem _ (oToOhat (star α) * v_) (Submodule.mem_span_singleton_self w')
  -- Using T central, (T : ℤ) • rem = rem * (T : 𝓞^), and since (T : 𝓞^) ∈ span {w'},
  -- we get (T : ℤ) • rem ∈ span {w'}.
  have hTsmul_in : (((T : ℕ) : ℤ) • rem') ∈ Submodule.span 𝓞^ ({w'} : Set 𝓞^) := by
    rw [hT_int]
    -- Goal: (Hurwitz.norm α : ℤ) • rem' ∈ span {w'}
    have heq : (Hurwitz.norm α : ℤ) • rem' = rem' * (Hurwitz.norm α : 𝓞^) := by
      rw [zsmul_eq_mul, Int.cast_comm]
    rw [heq]
    obtain ⟨r₀, hr₀⟩ := Submodule.mem_span_singleton.mp hnorm_in
    change r₀ * w' = _ at hr₀
    rw [← hr₀, ← mul_assoc]
    exact Submodule.smul_mem _ (rem' * r₀) (Submodule.mem_span_singleton_self w')
  have hβ_in_I : β ∈ I := by
    change oToOhat β ∈ Submodule.span 𝓞^ ({w'} : Set 𝓞^)
    rw [hβ_eq]
    exact Submodule.sub_mem _ (Submodule.mem_span_singleton_self w') hTsmul_in
  -- Step 7b: β = γ * α for some γ : 𝓞
  rw [hα_eq, Submodule.mem_span_singleton] at hβ_in_I
  obtain ⟨γ, hγ⟩ := hβ_in_I
  change γ * α = β at hγ
  -- Step 7c: Define u_ : 𝓞^ so that u_ * oToOhat α = w'
  -- w' = oToOhat β + (T : ℤ) • rem
  --    = oToOhat(γ * α) + rem * (norm α : 𝓞^)
  --    = oToOhat γ * oToOhat α + rem * oToOhat(star α) * oToOhat α
  --    = (oToOhat γ + rem * oToOhat(star α)) * oToOhat α
  let u_ : 𝓞^ := oToOhat γ + rem' * oToOhat (star α)
  have hu_ : u_ * oToOhat α = w' := by
    change (oToOhat γ + rem' * oToOhat (star α)) * oToOhat α = w'
    rw [add_mul, mul_assoc, h_stara_alpha, ← map_mul, hγ]
    -- Goal: oToOhat β + rem * (Hurwitz.norm α : 𝓞^) = w'
    rw [hβrem']
    -- Goal: oToOhat β + rem * (Hurwitz.norm α : 𝓞^) = oToOhat β + (T : ℤ) • rem
    congr 1
    rw [zsmul_eq_mul, Int.cast_comm, hT_int]
  -- Step 8: Show u_ * v_ = 1 and v_ * u_ = 1
  have hNM_pos : ((N * M : ℕ+) : ℕ) > 0 := PNat.pos _
  have huv : u_ * v_ = 1 := by
    -- From (u_ * v_ - 1) * w' = 0 and w' * z' = NM > 0 (in ℕ), conclude u_ * v_ = 1
    have h1 : (u_ * v_ - 1) * w' = 0 := by
      rw [sub_mul, one_mul, mul_assoc, hv_, hu_, sub_self]
    have h2 : (u_ * v_ - 1) * ((N * M : ℕ+) : 𝓞^) = 0 := by
      rw [← hwz, ← mul_assoc, h1, zero_mul]
    -- (u_ * v_ - 1) * (NM : 𝓞^) = 0 means (NM : ℤ) • (u_ * v_ - 1) = 0 (central cast)
    have h3 : ((N * M : ℕ+) : ℕ) • (u_ * v_ - 1) = 0 := by
      have hcast : (((N * M : ℕ+) : ℕ) : 𝓞^) = ((N * M : ℕ+) : 𝓞^) := by push_cast; rfl
      have heq : ((N * M : ℕ+) : ℕ) • (u_ * v_ - 1) = (u_ * v_ - 1) * ((N * M : ℕ+) : 𝓞^) := by
        rw [nsmul_eq_mul, hcast, (Nat.cast_commute ((N * M : ℕ+) : ℕ) (u_ * v_ - 1)).eq, hcast]
      rw [heq, h2]
    -- Torsion-free implies u_ * v_ - 1 = 0
    have h4 : u_ * v_ - 1 = 0 := by
      have hinj := IsAddTorsionFree.nsmul_right_injective (M := 𝓞^) hNM_pos.ne'
      have := hinj (show ((N * M : ℕ+) : ℕ) • (u_ * v_ - 1) = ((N * M : ℕ+) : ℕ) • 0 from by
        rw [smul_zero]; exact h3)
      exact this
    exact sub_eq_zero.mp h4
  have hvu : v_ * u_ = 1 := by
    -- (v_ * u_ - 1) * oToOhat α = 0, then right-multiply by oToOhat (star α) to get
    -- (v_ * u_ - 1) * (Hurwitz.norm α : 𝓞^) = 0.
    have h1 : (v_ * u_ - 1) * oToOhat α = 0 := by
      rw [sub_mul, one_mul, mul_assoc, hu_, hv_, sub_self]
    have h_alpha_stara : oToOhat α * oToOhat (star α) = (Hurwitz.norm α : 𝓞^) := by
      rw [← map_mul, ← Hurwitz.norm_eq_mul_conj, hnormcast]
    have h2 : (v_ * u_ - 1) * (Hurwitz.norm α : 𝓞^) = 0 := by
      rw [← h_alpha_stara, ← mul_assoc, h1, zero_mul]
    have hcast_nat : (((Hurwitz.norm α).toNat : ℕ) : 𝓞^) = (Hurwitz.norm α : 𝓞^) := by
      have h1 : (((Hurwitz.norm α).toNat : ℕ) : ℤ) = Hurwitz.norm α :=
        Int.toNat_of_nonneg hnorm_pos.le
      calc (((Hurwitz.norm α).toNat : ℕ) : 𝓞^)
          = ((((Hurwitz.norm α).toNat : ℕ) : ℤ) : 𝓞^) := by push_cast; rfl
        _ = ((Hurwitz.norm α : ℤ) : 𝓞^) := by rw [h1]
    have h3 : (Hurwitz.norm α).toNat • (v_ * u_ - 1) = 0 := by
      have heq : (Hurwitz.norm α).toNat • (v_ * u_ - 1) =
          (v_ * u_ - 1) * (Hurwitz.norm α : 𝓞^) := by
        rw [nsmul_eq_mul, (Nat.cast_commute ((Hurwitz.norm α).toNat) (v_ * u_ - 1)).eq,
          hcast_nat]
      rw [heq, h2]
    have hnormNat_pos : (Hurwitz.norm α).toNat ≠ 0 := by
      have : 0 < (Hurwitz.norm α).toNat := by
        rw [Int.lt_toNat]; exact_mod_cast hnorm_pos
      omega
    have h4 : v_ * u_ - 1 = 0 := by
      have hinj := IsAddTorsionFree.nsmul_right_injective (M := 𝓞^) hnormNat_pos
      have heq0 : (Hurwitz.norm α).toNat • (v_ * u_ - 1) = (Hurwitz.norm α).toNat • 0 := by
        rw [h3, smul_zero]
      exact hinj heq0
    exact sub_eq_zero.mp h4
  -- Step 9: Build the 𝓞^-unit with value u_ and inverse v_
  let v_unit : 𝓞^ˣ := ⟨u_, v_, huv, hvu⟩
  -- Step 10: Build the D-unit.
  -- From `hzinv : z⁻¹ = j₁((M⁻¹) ⊗ₜ 1) * j₂ w'`, and `w' = u_ * oToOhat α`:
  -- `z⁻¹ = j₁((M⁻¹) ⊗ₜ 1) * j₂(u_) * j₂(oToOhat α) = j₁((M⁻¹) ⊗ₜ 1) * j₂ v_unit * j₁((1 : ℚ) ⊗ₜ α)`
  -- Use centrality of `j₁((M⁻¹) ⊗ₜ 1)` to commute past `j₂ v_unit`, combine j₁'s:
  -- `z⁻¹ = j₂ v_unit * j₁((M⁻¹ : ℚ) ⊗ₜ α)`
  -- So `z = (j₁((M⁻¹ : ℚ) ⊗ₜ α))⁻¹ * (j₂ v_unit)⁻¹`.
  -- `(M⁻¹ : ℚ) ⊗ₜ α = ((M⁻¹ : ℚ) ⊗ₜ 1) * ((1 : ℚ) ⊗ₜ α)` — product of units.
  -- Define the D-unit explicitly.
  let Mrat_inv : Dˣ := {
    val := (((M : ℚ)⁻¹) ⊗ₜ[ℤ] (1 : 𝓞) : D)
    inv := (((M : ℚ)) ⊗ₜ[ℤ] (1 : 𝓞) : D)
    val_inv := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        inv_mul_cancel₀ (by exact_mod_cast (M.pos).ne' : ((M : ℚ)) ≠ 0)]; rfl
    inv_val := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_inv_cancel₀ (by exact_mod_cast (M.pos).ne' : ((M : ℚ)) ≠ 0)]; rfl }
  let αunit : Dˣ := HurwitzRat.oneTmulUnit α hα_ne_zero
  -- The unit `(M⁻¹ ⊗ₜ α : D)` as product Mrat_inv * αunit
  let MαInvUnit : Dˣ := Mrat_inv * αunit
  -- The final D-unit is the inverse of MαInvUnit
  refine ⟨MαInvUnit⁻¹, v_unit⁻¹, ?_⟩
  -- Goal: (z : D^) = j₁(MαInvUnit⁻¹ : D) * j₂(v_unit⁻¹ : 𝓞^)
  -- Strategy: show (j₁(MαInvUnit) * j₂(v_unit)) * z = 1, then rearrange.
  -- We have (j₂ v_unit : D^) = j₂ u_, and (j₁ MαInvUnit : D^) = j₁((M⁻¹ : ℚ) ⊗ₜ α) =
  -- j₁((M⁻¹ : ℚ) ⊗ₜ 1) * j₁((1 : ℚ) ⊗ₜ α).
  -- (not needed below; removed)
  have hv_unit_val : ((v_unit : 𝓞^ˣ) : 𝓞^) = u_ := rfl
  -- Key identity: j₂ w' = j₂ u_ * j₁((1 : ℚ) ⊗ₜ α)
  have hj2oToOhat : j₂ (oToOhat α) = j₁ ((1 : ℚ) ⊗ₜ[ℤ] α : D) := rfl
  have hj2w' : j₂ w' = j₂ u_ * j₁ ((1 : ℚ) ⊗ₜ[ℤ] α : D) := by
    rw [← hu_, map_mul, hj2oToOhat]
  -- Now express z from hzinv + hj2w'
  -- z⁻¹ = j₁((M⁻¹) ⊗ₜ 1) * (j₂ u_ * j₁((1 : ℚ) ⊗ₜ α))
  --     = (j₁((M⁻¹) ⊗ₜ 1) * j₂ u_) * j₁((1 : ℚ) ⊗ₜ α)      -- reassoc
  --     = (j₂ u_ * j₁((M⁻¹) ⊗ₜ 1)) * j₁((1 : ℚ) ⊗ₜ α)       -- central j₁
  --     = j₂ u_ * (j₁((M⁻¹) ⊗ₜ 1) * j₁((1 : ℚ) ⊗ₜ α))       -- reassoc
  --     = j₂ u_ * j₁((M⁻¹ : ℚ) ⊗ₜ α)                          -- combine
  have hzinv_eq : (z⁻¹ : (D^)ˣ).val = j₂ u_ * j₁ (((M : ℚ)⁻¹ ⊗ₜ[ℤ] (1 : 𝓞) : D)) *
      j₁ ((1 : ℚ) ⊗ₜ[ℤ] α : D) := by
    rw [hzinv, hj2w']
    rw [← mul_assoc]
    -- goal: j₁((M⁻¹) ⊗ₜ 1) * j₂ u_ * j₁((1 : ℚ) ⊗ₜ α) = j₂ u_ * j₁((M⁻¹) ⊗ₜ 1) * j₁((1 : ℚ) ⊗ₜ α)
    congr 1
    exact (j₁_rat_mul_comm ((M : ℚ)⁻¹) u_)
  -- Directly compute: ↑z⁻¹ = (j₂ u_) * (j₁ ((M⁻¹)⊗α))
  have hinv_val : (z⁻¹ : (D^)ˣ).val =
      (j₂ u_) * (j₁ (((M : ℚ)⁻¹ ⊗ₜ[ℤ] (1 : 𝓞) : D) * ((1 : ℚ) ⊗ₜ[ℤ] α : D))) := by
    rw [map_mul, ← mul_assoc]; exact hzinv_eq
  -- The RHS: (j₂ u_) * (j₁ (MαInvUnit.val)), and u_ = v_unit.val, MαInvUnit.val = the product.
  have hMα_val2 : ((MαInvUnit : Dˣ) : D) =
      (((M : ℚ)⁻¹ ⊗ₜ[ℤ] (1 : 𝓞) : D)) * ((1 : ℚ) ⊗ₜ[ℤ] α : D) := rfl
  -- So `↑z⁻¹ = j₂ ↑v_unit * j₁ ↑MαInvUnit`.
  have hinv_val2 : (z⁻¹ : (D^)ˣ).val = j₂ ((v_unit : 𝓞^ˣ) : 𝓞^) * j₁ ((MαInvUnit : Dˣ) : D) := by
    rw [hv_unit_val, hMα_val2]; exact hinv_val
  -- Key: in a monoid with an element z that is a unit, ↑z * ↑(z⁻¹) = 1.
  -- Goal: ↑z = j₁ ↑MαInvUnit⁻¹ * j₂ ↑v_unit⁻¹
  -- Strategy: Show that RHS * ↑z⁻¹ = 1 in D^ (or equivalently ↑z * RHS = 1 via inverse)
  -- Actually easier: show ↑z * (j₂ ↑v_unit * j₁ ↑MαInvUnit) = 1, then take inverse.
  have hz_mul : (z : (D^)ˣ).val * ((z⁻¹ : (D^)ˣ).val) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hinv_val2] at hz_mul
  -- hz_mul : ↑z * (j₂ ↑v_unit * j₁ ↑MαInvUnit) = 1
  -- So ↑z = (j₂ ↑v_unit * j₁ ↑MαInvUnit)⁻¹ in terms of... well D^ isn't a group.
  -- But we know: (j₁ ↑MαInvUnit⁻¹ * j₂ ↑v_unit⁻¹) * (j₂ ↑v_unit * j₁ ↑MαInvUnit) = 1
  -- from ring and the unit equations. Combined with hz_mul, cancel.
  -- Better: multiply hz_mul on the right by (j₁ ↑MαInvUnit⁻¹ * j₂ ↑v_unit⁻¹).
  have hprod_inv : (j₁ ((MαInvUnit⁻¹ : Dˣ) : D) * j₂ ((v_unit⁻¹ : 𝓞^ˣ) : 𝓞^)) *
      (j₂ ((v_unit : 𝓞^ˣ) : 𝓞^) * j₁ ((MαInvUnit : Dˣ) : D)) = 1 := by
    rw [mul_assoc, ← mul_assoc (j₂ _) (j₂ _) _, ← map_mul j₂,
      show ((v_unit⁻¹ : 𝓞^ˣ) : 𝓞^) * ((v_unit : 𝓞^ˣ) : 𝓞^) = 1 from by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one],
      map_one, one_mul, ← map_mul j₁,
      show ((MαInvUnit⁻¹ : Dˣ) : D) * ((MαInvUnit : Dˣ) : D) = 1 from by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one],
      map_one]
  -- Multiply hz_mul by hprod_inv on the right
  have : (z : (D^)ˣ).val =
      j₁ ((MαInvUnit⁻¹ : Dˣ) : D) * j₂ ((v_unit⁻¹ : 𝓞^ˣ) : 𝓞^) := by
    have h := congrArg (fun x => x * (j₁ ((MαInvUnit⁻¹ : Dˣ) : D) *
        j₂ ((v_unit⁻¹ : 𝓞^ˣ) : 𝓞^))) hz_mul
    simp only at h
    rw [one_mul, mul_assoc] at h
    -- h : ↑z * ((j₂ ↑v_unit * j₁ ↑MαInvUnit) * (j₁ ↑MαInvUnit⁻¹ * j₂ ↑v_unit⁻¹)) =
    --     j₁ ↑MαInvUnit⁻¹ * j₂ ↑v_unit⁻¹
    -- The inner parens should also equal 1; let me compute.
    have hinner : (j₂ ((v_unit : 𝓞^ˣ) : 𝓞^) * j₁ ((MαInvUnit : Dˣ) : D)) *
        (j₁ ((MαInvUnit⁻¹ : Dˣ) : D) * j₂ ((v_unit⁻¹ : 𝓞^ˣ) : 𝓞^)) = 1 := by
      rw [mul_assoc, ← mul_assoc (j₁ _) (j₁ _) _, ← map_mul j₁,
        show ((MαInvUnit : Dˣ) : D) * ((MαInvUnit⁻¹ : Dˣ) : D) = 1 from by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
        map_one, one_mul, ← map_mul j₂,
        show ((v_unit : 𝓞^ˣ) : 𝓞^) * ((v_unit⁻¹ : 𝓞^ˣ) : 𝓞^) = 1 from by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
        map_one]
    rw [hinner, mul_one] at h
    exact h
  exact this

end HurwitzRatHat
