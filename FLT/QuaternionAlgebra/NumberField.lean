import FLT.Mathlib.Algebra.IsQuaternionAlgebra
import FLT.Mathlib.Topology.Algebra.Valued.ValuationTopology
import FLT.Mathlib.Topology.Instances.Matrix
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Hacks.RightActionInstances
import FLT.NumberField.Completion.Finite
import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
/-!

# Definitions of various compact open subgrups of Dˣ and GL₂(𝔸_F^∞)

We define U₁(v) as a subgroup of GL₂(Fᵥ), and U₁(S) as a subgroup
of GL₂(𝔸_F^∞). We introduce the concept
of a rigidification `r : (D ⊗[F] 𝔸_F^∞) ≅ M₂(𝔸_F^∞)` in order
to push U₁(S) over to a subgroup of `(D ⊗[F] 𝔸_F^∞)ˣ`.

-/
variable (F : Type*) [Field F] [NumberField F] --[NumberField.IsTotallyReal F]

variable (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

open IsDedekindDomain

open scoped NumberField TensorProduct

namespace IsQuaternionAlgebra.NumberField

open scoped TensorProduct.RightActions in
/--
A rigidification of a quaternion algebra D over a number field F
is a fixed choice of `𝔸_F^∞`-algebra isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`. In other
words, it is a choice of splitting of `D ⊗[F] Fᵥ` (i.e. an isomorphism to `M₂(Fᵥ)`)
for all finite places `v` together with a guarantee that the isomorphism works
on the integral level at all but finitely many places. Such a rigidification exists
if and only if F is unramified at all finite places.
-/
abbrev Rigidification :=
    (D ⊗[F] (FiniteAdeleRing (𝓞 F) F) ≃ₐ[FiniteAdeleRing (𝓞 F) F]
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))

/--
A quaternion algebra over a number field is unramified if it is split
at all finite places. This is implemented as the existence of a rigidification
of `D`, that is, an isomorphism `D ⊗[F] 𝔸_F^∞ = M₂(𝔸_F^∞)`.
-/
def IsUnramified : Prop := Nonempty (Rigidification F D)

end IsQuaternionAlgebra.NumberField

open IsQuaternionAlgebra.NumberField IsDedekindDomain

variable {F}

namespace IsDedekindDomain

/-- `M_2(O_v)` as a subring of `M_2(F_v)`. -/
noncomputable def M2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subring (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :=
  (v.adicCompletionIntegers F).matrix

/-- `GL₂(𝒪ᵥ)` as a subgroup of `GL₂(Fᵥ)`. -/
noncomputable def GL2.localFullLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) :=
  MonoidHom.range (Units.map
    (RingHom.mapMatrix (v.adicCompletionIntegers F).subtype).toMonoidHom)

theorem M2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (M2.localFullLevel v).carrier :=
  (NumberField.isOpenAdicCompletionIntegers F v).matrix

theorem M2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (M2.localFullLevel v).carrier :=
  (isCompact_iff_compactSpace.mpr (NumberField.instCompactSpaceAdicCompletionIntegers F v)).matrix

private lemma GL2.localFullLevel_carrier_eq (v : HeightOneSpectrum (𝓞 F)) :
    (GL2.localFullLevel v).carrier = ((M2.localFullLevel v).toSubmonoid.units : Set _) := by
  ext x
  simp only [Subgroup.mem_carrier, SetLike.mem_coe]
  constructor
  · rintro ⟨y, hy⟩
    rw [Submonoid.mem_units_iff]
    constructor
    · change ↑x ∈ (M2.localFullLevel v).toSubmonoid
      rw [← hy]
      intro i j
      exact (y.val i j).prop
    · change ↑x⁻¹ ∈ (M2.localFullLevel v).toSubmonoid
      rw [← hy]
      simp only [Units.coe_map_inv]
      intro i j
      exact (y⁻¹.val i j).prop
  · intro hx
    rw [Submonoid.mem_units_iff] at hx
    obtain ⟨hval, hinv⟩ := hx
    -- Construct the matrix over 𝒪ᵥ and lift x to GL₂(𝒪ᵥ)
    let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨x.val i j, hval i j⟩
    let Minv : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨x.inv i j, hinv i j⟩
    -- M and Minv are mutual inverses
    have hMMinv : M * Minv = 1 := by
      funext i j; ext
      change (∑ k, (M i k).1 * (Minv k j).1) = ((1 : Matrix _ _ (v.adicCompletionIntegers F)) i j).1
      simp only [M, Minv, Matrix.of_apply, Matrix.one_apply]
      have := congr_fun (congr_fun x.val_inv i) j
      simp only [Matrix.mul_apply, Matrix.one_apply] at this
      rw [this]; split_ifs <;> simp
    have hMinvM : Minv * M = 1 := mul_eq_one_comm.mp hMMinv
    let y : GL (Fin 2) (v.adicCompletionIntegers F) :=
      ⟨M, Minv, hMMinv, hMinvM⟩
    exact ⟨y, Units.ext (by
      simp only [y, M, Units.coe_map]
      ext i j; simp [Matrix.map_apply, Matrix.of_apply])⟩

theorem GL2.localFullLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localFullLevel v).carrier :=
  GL2.localFullLevel_carrier_eq v ▸ Submonoid.isOpen_units (M2.localFullLevel.isOpen v)

theorem GL2.localFullLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localFullLevel v).carrier :=
  GL2.localFullLevel_carrier_eq v ▸ Submonoid.units_isCompact (M2.localFullLevel.isCompact v)

lemma GL2.mem_localFullLevel {v : HeightOneSpectrum (𝓞 F)} {x : GL (Fin 2) (v.adicCompletion F)}
    (hx : x ∈ localFullLevel v) :
    ∃ x' : GL (Fin 2) (v.adicCompletionIntegers F),
      Units.map ((v.adicCompletionIntegers F).subtype.mapMatrix.toMonoidHom) x' = x :=
  hx

lemma GL2.mem_localFullLevel' {v : HeightOneSpectrum (𝓞 F)} {x : GL (Fin 2) (v.adicCompletion F)}
    (hx : x ∈ localFullLevel v) :
    ∃ x' : GL (Fin 2) (v.adicCompletionIntegers F), ∀ i j, x' i j = x i j := by
  refine (mem_localFullLevel hx).imp ?_
  simp only [RingHom.toMonoidHom_eq_coe, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe,
    RingHom.mapMatrix_apply]
  rintro y hy
  simp [← hy]

lemma GL2.v_det_val_mem_localFullLevel_eq_one {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} (hx : x ∈ localFullLevel v) :
    Valued.v x.val.det = 1 := by
  obtain ⟨y, hy⟩ := mem_localFullLevel hx
  have hd : IsUnit y.det.val := by simp
  rw [Valued.isUnit_valuationSubring_iff] at hd
  simpa [← hy, Matrix.det_fin_two] using hd

lemma GL2.v_le_one_of_mem_localFullLevel (v : HeightOneSpectrum (𝓞 F)) {x}
    (hx : x ∈ localFullLevel v) (i j) : Valued.v (x i j) ≤ 1 := by
  simp only [localFullLevel, Units.map, RingHom.mapMatrix, Matrix.map, ValuationSubring.subtype,
    Subring.subtype, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_monoidHom_mk, Units.inv_eq_val_inv, Matrix.coe_units_inv, MonoidHom.mem_range,
    MonoidHom.mk'_apply, Matrix.GeneralLinearGroup.ext_iff, Matrix.of_apply] at hx
  obtain ⟨x', hx'⟩ := hx
  simp only [← hx', ← HeightOneSpectrum.mem_adicCompletionIntegers, SetLike.coe_mem]

lemma GL2.mem_localFullLevel_iff_v_le_one_and_v_det_eq_one {v : HeightOneSpectrum (𝓞 F)}
    {x : GL (Fin 2) (v.adicCompletion F)} :
    x ∈ localFullLevel v ↔ (∀ (i j), Valued.v (x i j) ≤ 1) ∧ Valued.v x.val.det = 1 :=
  ⟨fun h ↦ ⟨GL2.v_le_one_of_mem_localFullLevel _ h, GL2.v_det_val_mem_localFullLevel_eq_one h⟩, by
    intro ⟨h₁, h₂⟩
    let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers F) :=
      Matrix.of fun i j => ⟨x i j, h₁ i j⟩
    have det_eq : M.det = x.val.det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]; simp [M]
    have isUnit_M :=
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Valued.isUnit_valuationSubring_iff.mpr (det_eq ▸ h₂)))
    use isUnit_M.unit
    ext i j; fin_cases i; all_goals fin_cases j
    all_goals simp [M]
  ⟩

open Valued

/-- local U_1(v), defined as a subgroup of GL₂(Fᵥ) given by
matrices in GL₂(𝒪ᵥ) congruent to (a *;0 a) mod v. -/
noncomputable def GL2.localTameLevel (v : HeightOneSpectrum (𝓞 F)) :
    Subgroup (GL (Fin 2) (v.adicCompletion F)) where
  carrier := {x ∈ localFullLevel v |
    Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧ Valued.v (x.val 1 0) < 1}
  mul_mem' {a b} ha hb := by
    simp_all only [Set.mem_setOf_eq, Units.val_mul]
    refine ⟨Subgroup.mul_mem _ ha.1 hb.1, ?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.isValue, Fin.sum_univ_two]
      convert_to Valued.v ((a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) +
        (a.val 0 1 * b.val 1 0 - a.val 1 0 * b.val 0 1)) < 1
      · ring_nf
      suffices Valued.v (a.val 0 1 * b.val 1 0) < 1 ∧
                Valued.v (a.val 1 0 * b.val 0 1) < 1 ∧
                Valued.v (a.val 0 0 * b.val 0 0 - a.val 1 1 * b.val 1 1) < 1 by
        apply Valuation.map_add_lt _ this.2.2 ?_
        apply Valuation.map_sub_lt _ this.1 this.2.1
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul, mul_comm]
        apply mul_lt_one_of_lt_of_le hb.2.2
        apply v_le_one_of_mem_localFullLevel _ ha.1
      · rw [map_mul]
        apply mul_lt_one_of_lt_of_le ha.2.2
        apply v_le_one_of_mem_localFullLevel _ hb.1
      · convert_to Valued.v (a.val 0 0 * (b.val 0 0 - b.val 1 1) +
          (a.val 0 0 - a.val 1 1) * b.val 1 1) < 1
        · ring_nf
        apply Valuation.map_add_lt _
        · rw [map_mul, mul_comm]
          apply mul_lt_one_of_lt_of_le hb.2.1
          apply v_le_one_of_mem_localFullLevel _ ha.1
        · rw [map_mul]
          apply mul_lt_one_of_lt_of_le ha.2.1
          apply v_le_one_of_mem_localFullLevel _ hb.1
    · simp only [Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
      apply Valuation.map_add_lt _
      · rw [map_mul]
        apply mul_lt_one_of_lt_of_le ha.2.2
        apply v_le_one_of_mem_localFullLevel _ hb.1
      · rw [map_mul, mul_comm]
        apply mul_lt_one_of_lt_of_le hb.2.2
        apply v_le_one_of_mem_localFullLevel _ ha.1
  one_mem' := by simp [one_mem]
  inv_mem' {a} ha := by
    simp_all only [Set.mem_setOf_eq, inv_mem_iff, Matrix.coe_units_inv, true_and,
      Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, smul_eq_mul, Matrix.cons_val_one,
      ← mul_sub, map_mul, map_inv₀, mul_neg, Valuation.map_neg]
    rw [Valuation.map_sub_swap, v_det_val_mem_localFullLevel_eq_one ha.1]
    simp [ha.2]

private theorem continuous_GL2_entry (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    Continuous (fun x : GL (Fin 2) (v.adicCompletion F) => x.val i j) :=
  Units.continuous_val.matrix_elem i j

theorem GL2.localTameLevel.isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (GL2.localTameLevel v).carrier := by
  -- carrier = {x ��� localFullLevel v | v(x₀₀ - x₁₁) < 1 ∧ v(x₁₀) < 1}
  -- Intersection of three open sets
  change IsOpen ({x | x ∈ localFullLevel v} ∩ {x | Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧
    Valued.v (x.val 1 0) < 1})
  apply IsOpen.inter (localFullLevel.isOpen v)
  apply IsOpen.inter
  · exact (Valued.isOpen_ball _ 1).preimage
      ((continuous_GL2_entry v 0 0).sub (continuous_GL2_entry v 1 1))
  · exact (Valued.isOpen_ball _ 1).preimage (continuous_GL2_entry v 1 0)

theorem GL2.localTameLevel.isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (GL2.localTameLevel v).carrier := by
  -- carrier is a closed subset of the compact localFullLevel
  -- {v < 1} is clopen in a valued field, so the conditions define a closed set
  apply IsCompact.of_isClosed_subset (localFullLevel.isCompact v)
  · change IsClosed ({x | x ∈ localFullLevel v} ∩ {x | Valued.v (x.val 0 0 - x.val 1 1) < 1 ∧
      Valued.v (x.val 1 0) < 1})
    apply IsClosed.inter (localFullLevel.isCompact v).isClosed
    apply IsClosed.inter
    · exact (Valued.isClopen_ball _ 1).1.preimage
        ((continuous_GL2_entry v 0 0).sub (continuous_GL2_entry v 1 1))
    · exact (Valued.isClopen_ball _ 1).1.preimage (continuous_GL2_entry v 1 0)
  · intro x hx; exact hx.1

end IsDedekindDomain

open RestrictedProduct

/-- The canonical F-algebra morphism from `𝔸_F^∞` (the finite adeles of a number field F) to
the local component `F_v` for `v` a finite place of `𝓞 F`. -/
noncomputable
def IsDedekindDomain.FiniteAdeleRing.toAdicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] HeightOneSpectrum.adicCompletion F v where
  __ := RestrictedProduct.evalRingHom _ v
  commutes' _ := rfl

namespace IsDedekindDomain.FiniteAdeleRing

/-- The canonical group homomorphism from `GL_2(𝔸_F^∞)` to the local component `GL_2(F_v)` for `v`
a finite place. -/
noncomputable def GL2.toAdicCompletion
    (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →*
    GL (Fin 2) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (FiniteAdeleRing.toAdicCompletion v)).toMonoidHom

/-- `GL_2(𝔸_F^∞)` is isomorphic and homeomorphic to the
restricted product of the local components `GL_2(F_v)`.
-/
noncomputable def GL2.restrictedProduct :
    GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
    Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units] :=
  ContinuousMulEquiv.restrictedProductMatrixUnits (NumberField.isOpenAdicCompletionIntegers F)

/-- The "value" form of the bridging computation: at every entry `(i,j)` and place `w`,
the matrix entry of `GL2.toAdicCompletion w (rp.symm x)` equals the corresponding
entry of `(x w).val`. -/
lemma GL2.toAdicCompletion_restrictedProduct_symm_val_apply
    (w : HeightOneSpectrum (𝓞 F))
    (x : Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units])
    (i j : Fin 2) :
    ((GL2.toAdicCompletion w
      (FiniteAdeleRing.GL2.restrictedProduct.symm x)).val i j) = (x w).val i j := by
  rfl

/-- The unit-level version of `toAdicCompletion_restrictedProduct_symm_val_apply`:
applying `GL2.toAdicCompletion w` to the inverse image of `x` under the restricted-
product equivalence yields `x w` directly. Useful for transporting global statements
about `GL₂(𝔸_F^∞)` to local statements at each place. -/
lemma GL2.toAdicCompletion_restrictedProduct_symm_apply
    (w : HeightOneSpectrum (𝓞 F))
    (x : Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units]) :
    GL2.toAdicCompletion w
      (FiniteAdeleRing.GL2.restrictedProduct.symm x) = x w := by
  ext i j
  exact GL2.toAdicCompletion_restrictedProduct_symm_val_apply w x i j

/-- Bridging lemma: applying `GL2.toAdicCompletion w` to the embedding of a single
local element `g_loc` at place `v` via the restricted product isomorphism gives
`g_loc` if `w = v` and `1` otherwise. -/
lemma GL2.toAdicCompletion_restrictedProduct_symm_mulSingle_same
    [DecidableEq (HeightOneSpectrum (𝓞 F))]
    (v : HeightOneSpectrum (𝓞 F)) (g_loc : GL (Fin 2) (v.adicCompletion F)) :
    GL2.toAdicCompletion v
      (FiniteAdeleRing.GL2.restrictedProduct.symm
        (RestrictedProduct.mulSingle _ v g_loc)) = g_loc := by
  ext i j
  rw [GL2.toAdicCompletion_restrictedProduct_symm_val_apply,
    RestrictedProduct.mulSingle_eq_same]

lemma GL2.toAdicCompletion_restrictedProduct_symm_mulSingle_ne
    [DecidableEq (HeightOneSpectrum (𝓞 F))]
    {w v : HeightOneSpectrum (𝓞 F)} (hwv : w ≠ v)
    (g_loc : GL (Fin 2) (v.adicCompletion F)) :
    GL2.toAdicCompletion w
      (FiniteAdeleRing.GL2.restrictedProduct.symm
        (RestrictedProduct.mulSingle _ v g_loc)) = 1 := by
  ext i j
  rw [GL2.toAdicCompletion_restrictedProduct_symm_val_apply,
    RestrictedProduct.mulSingle_eq_of_ne _ _ hwv]

end IsDedekindDomain.FiniteAdeleRing

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

/-- If `F` is a number field and `S` is a finite set of finite places of `𝓞 F` then
`GL2.TameLevel S` is the subgroup of `GL₂(𝔸_F^∞)` consisting of things in `GL₂(𝓞ᵥ)` for
all places, and furthermore in the local "`U₁(v)`" subgroup `(a *;0 a) mod v` for all `v ∈ S`.
-/
noncomputable def GL2.TameLevel (S : Finset (HeightOneSpectrum (𝓞 F))) :
  Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) where
    carrier := {x | (∀ v, GL2.toAdicCompletion v x ∈ GL2.localFullLevel v) ∧
      (∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v)}
    mul_mem' {a b} ha hb := by simp_all [mul_mem]
    one_mem' := by simp_all [one_mem]
    inv_mem' {x} hx := by simp_all

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- Helper: GL2.toAdicCompletion v is continuous
private theorem GL2.toAdicCompletion.continuous (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (GL2.toAdicCompletion v :
      GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → GL (Fin 2) (v.adicCompletion F)) :=
  Continuous.units_map _
    (continuous_id.matrix_map (RestrictedProduct.continuous_eval v))

-- Helper: evaluation in the restricted product agrees with GL2.toAdicCompletion
private theorem GL2.restrictedProduct_eval (v : HeightOneSpectrum (𝓞 F))
    (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    (GL2.restrictedProduct x).1 v = GL2.toAdicCompletion v x := by
  ext i j
  rfl

-- The subgroup (M2.localFullLevel v).units equals GL2.localFullLevel v
-- (they have the same carrier by localFullLevel_carrier_eq)
private theorem GL2.localFullLevel_eq_units (v : HeightOneSpectrum (𝓞 F)) :
    GL2.localFullLevel v = (M2.localFullLevel v).units :=
  SetLike.ext' (GL2.localFullLevel_carrier_eq v)

-- Helper: the "full level" set equals preimage through restrictedProduct of forall-mem set
private theorem GL2.fullLevel_eq_preimage :
    {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) |
      ∀ v, GL2.toAdicCompletion v x ∈ GL2.localFullLevel v} =
    GL2.restrictedProduct ⁻¹'
      {f | ∀ v, f.1 v ∈ (M2.localFullLevel v).units} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  exact forall_congr' fun v => by
    rw [← GL2.restrictedProduct_eval, GL2.localFullLevel_eq_units]

-- Helper: the "full level" set is open
private theorem GL2.fullLevel_isOpen :
    IsOpen {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) |
      ∀ v, GL2.toAdicCompletion v x ∈ GL2.localFullLevel v} := by
  rw [GL2.fullLevel_eq_preimage]
  exact (RestrictedProduct.isOpen_forall_mem
    (fun v => Submonoid.isOpen_units (M2.localFullLevel.isOpen v))).preimage
    GL2.restrictedProduct.continuous

-- Helper: the "full level" set is compact
private theorem GL2.fullLevel_isCompact :
    IsCompact {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) |
      ∀ v, GL2.toAdicCompletion v x ∈ GL2.localFullLevel v} := by
  rw [GL2.fullLevel_eq_preimage]
  -- It suffices to show the target set in the restricted product is compact
  -- (preimage under a homeomorphism of a compact set is compact)
  apply (GL2.restrictedProduct.toHomeomorph).isClosedEmbedding.isCompact_preimage
  -- Need CompactSpace on each factor for Tychonoff
  haveI : ∀ v : HeightOneSpectrum (𝓞 F),
      CompactSpace ↥((M2.localFullLevel v).units :
        Subgroup (GL (Fin 2) (v.adicCompletion F))) := fun v =>
    isCompact_iff_compactSpace.mp ((GL2.localFullLevel_eq_units v) ▸
      GL2.localFullLevel.isCompact v)
  -- The set {f | ∀ v, f v ∈ A v} = range(structureMap), which is compact image of compact domain
  suffices IsCompact (Set.range (RestrictedProduct.structureMap
    (fun v => GL (Fin 2) (v.adicCompletion F))
    (fun v => ((M2.localFullLevel v).units :
      Subgroup (GL (Fin 2) (v.adicCompletion F)))) Filter.cofinite)) by
    rwa [RestrictedProduct.range_structureMap] at this
    -- The goal after rwa should match since range_structureMap uses SetLike.mem_coe
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

private theorem GL2.tameLevel_isOpen_aux :
    IsOpen {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) |
      ∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v} := by
  have : {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) |
      ∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v} =
    ⋂ v ∈ (S : Set _), (GL2.toAdicCompletion v) ⁻¹' (GL2.localTameLevel v).carrier := by
    ext x; simp
  rw [this]
  exact S.finite_toSet.isOpen_biInter fun v _ =>
    (GL2.localTameLevel.isOpen v).preimage (GL2.toAdicCompletion.continuous v)

private theorem GL2.tameLevel_isClosed_aux :
    IsClosed {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) |
      ∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v} := by
  have : {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) |
      ∀ v ∈ S, GL2.toAdicCompletion v x ∈ GL2.localTameLevel v} =
    ⋂ v ∈ (S : Set _), (GL2.toAdicCompletion v) ⁻¹' (GL2.localTameLevel v).carrier := by
    ext x; simp
  rw [this]
  exact isClosed_biInter fun v _ =>
    (GL2.localTameLevel.isCompact v).isClosed.preimage (GL2.toAdicCompletion.continuous v)

theorem GL2.TameLevel.isOpen : IsOpen (GL2.TameLevel S).carrier := by
  apply IsOpen.inter
  · exact GL2.fullLevel_isOpen
  · exact GL2.tameLevel_isOpen_aux S

theorem GL2.TameLevel.isCompact : IsCompact (GL2.TameLevel S).carrier := by
  apply IsCompact.of_isClosed_subset GL2.fullLevel_isCompact
  · exact IsClosed.inter GL2.fullLevel_isCompact.isClosed (GL2.tameLevel_isClosed_aux S)
  · intro x hx; exact hx.1

/-- Any element `u` of `GL2.TameLevel S` can be split as a product `u = u_v * u_v'` where
`u_v` is the identity outside the place `v` and `u_v'` is the identity at `v`. Both factors
themselves lie in `GL2.TameLevel S`. -/
lemma GL2.TameLevel.exists_split_at
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F))
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hu : u ∈ GL2.TameLevel S) :
    ∃ (u_v u_v' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)),
      u_v ∈ GL2.TameLevel S ∧ u_v' ∈ GL2.TameLevel S ∧
      u = u_v * u_v' ∧
      (∀ w, w ≠ v → GL2.toAdicCompletion w u_v = 1) ∧
      GL2.toAdicCompletion v u_v' = 1 := by
  classical
  -- Define u_v as the image of `mulSingle v (GL2.toAdicCompletion v u)` under the
  -- restricted product isomorphism, then u_v' := u_v⁻¹ * u.
  set u_v : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    FiniteAdeleRing.GL2.restrictedProduct.symm
      (RestrictedProduct.mulSingle _ v (GL2.toAdicCompletion v u)) with hu_v_def
  set u_v' : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := u_v⁻¹ * u with hu_v'_def
  -- Key facts about u_v under toAdicCompletion at various places.
  have h_uv_at_v : GL2.toAdicCompletion v u_v = GL2.toAdicCompletion v u :=
    GL2.toAdicCompletion_restrictedProduct_symm_mulSingle_same v _
  have h_uv_away : ∀ w, w ≠ v → GL2.toAdicCompletion w u_v = 1 := fun w hwv =>
    GL2.toAdicCompletion_restrictedProduct_symm_mulSingle_ne hwv _
  -- u_v ∈ TameLevel S
  have h_uv_mem : u_v ∈ GL2.TameLevel S := by
    refine ⟨fun w => ?_, fun w hwS => ?_⟩
    · by_cases hwv : w = v
      · subst hwv; rw [h_uv_at_v]; exact hu.1 w
      · rw [h_uv_away w hwv]; exact one_mem _
    · by_cases hwv : w = v
      · subst hwv; rw [h_uv_at_v]; exact hu.2 w hwS
      · rw [h_uv_away w hwv]; exact one_mem _
  -- u_v' ∈ TameLevel S (it's the product of u_v⁻¹ and u)
  have h_uv'_mem : u_v' ∈ GL2.TameLevel S :=
    (GL2.TameLevel S).mul_mem (inv_mem h_uv_mem) hu
  -- u = u_v * u_v'
  have h_prod : u = u_v * u_v' := by
    rw [hu_v'_def, ← mul_assoc, mul_inv_cancel, one_mul]
  -- u_v' is identity at v
  have h_uv'_at_v : GL2.toAdicCompletion v u_v' = 1 := by
    rw [hu_v'_def, map_mul, map_inv, h_uv_at_v, inv_mul_cancel]
  exact ⟨u_v, u_v', h_uv_mem, h_uv'_mem, h_prod, h_uv_away, h_uv'_at_v⟩

set_option maxHeartbeats 800000 in
-- Elaborating `Subgroup.map` against the heavily-staged
-- `FiniteAdeleRing.GL2.restrictedProduct` exceeds default `whnf` budget.
/-- The transported `GL2.TameLevel S` as a subgroup of the restricted product, via the
`FiniteAdeleRing.GL2.restrictedProduct` continuous multiplicative equivalence. -/
noncomputable def GL2.TameLevel.transported
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Subgroup (Πʳ (v : HeightOneSpectrum (𝓞 F)),
      [(GL (Fin 2) (v.adicCompletion F)), (M2.localFullLevel v).units]) :=
  Subgroup.map FiniteAdeleRing.GL2.restrictedProduct.toMulEquiv.toMonoidHom
    (GL2.TameLevel S)

set_option maxHeartbeats 800000 in
-- Same reason as `transported`: heavy `Subgroup.map` + restricted-product elaboration.
/-- The transported `GL2.TameLevel S` subgroup satisfies `isProductAt` at every place `v`.
This is the key ingredient for reducing the global double coset decomposition to the local
one via `mem_coset_and_mulSupport_subset_of_isProductAt`. The proof transports
`GL2.TameLevel.exists_split_at` from the global view through the restricted-product
equivalence, using `GL2.toAdicCompletion_restrictedProduct_symm_apply` as the bridge. -/
lemma GL2.TameLevel.isProductAt_transported
    (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    SubmonoidClass.isProductAt (GL2.TameLevel.transported S) v := by
  classical
  intro u hu
  -- hu : u ∈ Subgroup.map ... GL2.TameLevel S
  -- Unpack: ∃ g ∈ GL2.TameLevel S, restrictedProduct g = u
  obtain ⟨g, hg, hgu⟩ := hu
  -- Apply PR #47's exists_split_at to g
  obtain ⟨g_v, g_v', h_gv_mem, h_gv'_mem, h_prod, h_gv_away, h_gv'_at_v⟩ :=
    GL2.TameLevel.exists_split_at S v hg
  refine ⟨FiniteAdeleRing.GL2.restrictedProduct g_v, ⟨g_v, h_gv_mem, rfl⟩,
          FiniteAdeleRing.GL2.restrictedProduct g_v', ⟨g_v', h_gv'_mem, rfl⟩,
          ?_, ?_, ?_⟩
  · -- u = restrictedProduct g_v * restrictedProduct g_v'
    rw [← hgu, ← map_mul, ← h_prod]
    rfl
  · -- mulSupport (restrictedProduct g_v) ⊆ {v}
    intro w hw
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hw
    have h_eq : (FiniteAdeleRing.GL2.restrictedProduct g_v) w =
        GL2.toAdicCompletion w g_v := by
      conv_rhs => rw [show g_v = FiniteAdeleRing.GL2.restrictedProduct.symm
        (FiniteAdeleRing.GL2.restrictedProduct g_v) from
          (ContinuousMulEquiv.symm_apply_apply _ _).symm]
      exact (GL2.toAdicCompletion_restrictedProduct_symm_apply w _).symm
    rw [h_eq, h_gv_away w hne]
  · -- v ∉ mulSupport (restrictedProduct g_v')
    intro hv
    have h_eq : (FiniteAdeleRing.GL2.restrictedProduct g_v') v =
        GL2.toAdicCompletion v g_v' := by
      conv_rhs => rw [show g_v' = FiniteAdeleRing.GL2.restrictedProduct.symm
        (FiniteAdeleRing.GL2.restrictedProduct g_v') from
          (ContinuousMulEquiv.symm_apply_apply _ _).symm]
      exact (GL2.toAdicCompletion_restrictedProduct_symm_apply v _).symm
    apply hv
    rw [h_eq, h_gv'_at_v]

open scoped TensorProduct.RightActions in
/-- The subgroup of `(D ⊗ 𝔸_F^∞)ˣ` corresponding to the subgroup `U₁(S)` of `GL₂(𝔸_F^∞)`
(that is, matrices congruent to `(a *; 0 a) mod v` for all `v ∈ S`) via the rigidification `r`. -/
noncomputable def QuaternionAlgebra.TameLevel (r : Rigidification F D) :
    Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ :=
  Subgroup.comap (Units.map r.toMonoidHom) (GL2.TameLevel S)

open scoped TensorProduct.RightActions in
theorem Rigidification.continuous_toFun (r : Rigidification F D) :
    Continuous r :=
  letI : ∀ (i : HeightOneSpectrum (𝓞 F)),
      Algebra (FiniteAdeleRing (𝓞 F) F) ((i.adicCompletion F)) :=
    fun i ↦ (RestrictedProduct.evalRingHom _ i).toAlgebra
  IsModuleTopology.continuous_of_linearMap r.toLinearMap

open scoped TensorProduct.RightActions in
theorem Rigidification.continuous_invFun (r : Rigidification F D) :
    Continuous r.symm := by
  haveI : ContinuousAdd (D ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))
  exact IsModuleTopology.continuous_of_linearMap r.symm.toLinearMap

end HeightOneSpectrum

end IsDedekindDomain
