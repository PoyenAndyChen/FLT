/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, Kevin Buzzard
-/
import FLT.AutomorphicForm.QuaternionAlgebra.HeckeOperators.Concrete
import FLT.Mathlib.Algebra.Central.TensorProduct
import FLT.DedekindDomain.IntegralClosure
import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Automorphic Galois representations

For our proof of Fermat's Last Theorem, the following definition is the most convenient.

We say that a 2-dimensional $p$-adic or a mod $p$ Galois representation of the absolute
Galois of a totally real field number field $F$ of even degree is *automorphic* if there
exists a totally definite quaternion algebra $D/F$ unramified at all finite places,
a finite set $S$ of finite places of $F$, and an automorphic form of level $U_1(S)$
(matrices congruent to $(a *;0 a)$ mod $v$ for all $v\in S$) and weight 2 for $D$
such that the Galois representation is associated to the form by the construction of
Carayol, Taylor et al.

## Notes

Several things here are specialized to our case. We demand that the quaternion algebra is
unramified everywhere because this is the only case that we need. We stick to weight 2
because this is the only case that we need. The level is also more restrictive but again
the only thing we need: the automorphic forms it catches are trivial at all infinite places
and at all finite places are either Steinberg or principal series `π(χ₁, χ₂)` with `χᵢ` tame
and `χ₁χ₂` unramified.

-/


open scoped TensorProduct

open IsDedekindDomain NumberField TotallyDefiniteQuaternionAlgebra.WeightTwoAutomorphicForm

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob
local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

universe u -- u for number field / quaternion algebra.

set_option linter.unusedVariables false in -- we don't assume p is prime, p in A,
-- dim(V) = 2 etc etc in the definition itself, but it would be mathematically ridiculous
-- to leave these assumptions out of the definition.

/--
A 2-dimensional Galois representation `ρ` of the absolute Galois group of a totally
real field of even degree is said to be automorphic if it comes from a weight 2 trivial
character square-free level automorphic form on a totally definite quaternion algebra
of discriminant 1. More precisely, the level at each bad prime v has to be of the form
(a *;0 a) mod v.

This is a far more restrictive definition of automorphic than is found in the literature,
however it will suffice for the purpose of proving FLT.
-/
@[nolint unusedArguments]
def GaloisRep.IsAutomorphicOfLevel
    -- `F` is a totally real field
    {F : Type u} [Field F] [NumberField F] [IsTotallyReal F]
    (p : ℕ) [Fact p.Prime]
    {A : Type*} [CommRing A] [TopologicalSpace A] [Algebra ℤ_[p] A]
    [ContinuousSMul ℤ_[p] A]
    -- `V` is the rank 2 free `A`-module on which the Galois group will act
    {V : Type*} [AddCommGroup V] [Module A V] [Module.Finite A V]
      [Module.Free A V] (_hV : Module.finrank A V = 2)
    -- `ρ` is the Galois representation
    (ρ : GaloisRep F A V)
    -- `S` is the level of the modular form
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  -- We say `ρ` is *automorphic* if there's a quaternion algebra D over F of discriminant 1
  ∃ (D : Type u) (_ : Ring D) (_ : Algebra F D) (_ : IsQuaternionAlgebra F D)
    (r : IsQuaternionAlgebra.NumberField.Rigidification F D)
  -- and an `A`-valued automorphic eigenform,
  -- by which we mean a ℤ_p-linear map from the ℤ_p-Hecke algebra for (D,S) to `A`,
    (π : HeckeAlgebra F D r S ℤ_[p] →ₐ[ℤ_[p]] A),
  -- such that for all good primes `v` of `F`
  ∀ (v : HeightOneSpectrum (𝓞 F)) (_hvp : ↑p ∉ v.1) (hvS : v ∉ S),
    -- `ρ` is unramified at `v`,
    ρ.IsUnramifiedAt v ∧
    -- the det of `ρ(Frobᵥ)` (arithmetic Frobenius) is `N(v)` (i.e. `det(ρ) = cyclo`)
    (ρ.toLocal v (Frob v)).det = v.1.absNorm ∧
    -- and the trace of `ρ(Frobᵥ)` is the eigenvalue of the form at `Tᵥ`
    LinearMap.trace A V (ρ.toLocal v (Frob v)) = π (HeckeAlgebra.T D r ℤ_[p] v hvS)

instance {F E D : Type*}
    [Field F]
    [Field E] [Algebra F E]
    [Ring D] [Algebra F D] [IsQuaternionAlgebra F D] :
    IsQuaternionAlgebra E (E ⊗[F] D) where
  isSimpleRing := by
    -- D ⊗[F] E is simple (D central simple, E simple as field).
    -- Then E ⊗[F] D ≅ D ⊗[F] E via TensorProduct.comm, preserving simplicity.
    haveI := @IsQuaternionAlgebra.isSimpleRing F _ D _ _ _
    haveI := @IsQuaternionAlgebra.isCentral F _ D _ _ _
    haveI : IsSimpleRing E := inferInstance
    haveI : IsSimpleRing (D ⊗[F] E) := inferInstance
    exact (IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm F D E).toRingEquiv) inferInstance
  isCentral := by
    -- Z_E(E ⊗_F D) = E ⊗_F Z_F(D) = E ⊗_F F = E.
    haveI := @IsQuaternionAlgebra.isCentral F _ D _ _ _
    infer_instance
  dim_four := by
    -- rank E (E ⊗[F] D) = rank F D = 4.
    haveI : Module.Free F D := Module.Free.of_divisionRing F D
    rw [Module.rank_baseChange]
    simp [@IsQuaternionAlgebra.dim_four F _ D _ _ _]

variable {p : ℕ} [Fact p.Prime] in
noncomputable instance : NormedSpace ℚ_[p] (PadicAlgCl p) := spectralNorm.normedSpace ..

variable (p : ℕ) [Fact p.Prime] in
instance : ContinuousSMul ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
  continuousSMul_of_algebraMap _ _ ((continuous_algebraMap ℚ_[p] _).comp continuous_subtype_val)

/--
Cyclic base change.

Let `E/F` be a finite solvable extension of totally real fields of even degree,
let `p>2` be a prime and let `ρ : Gal(F-bar/F) -> GL_2(Q_p-bar)` be a continuous representation,
which is irreducible even when restricted to `Gal(E-bar/E)`. Let `S` be a finite
set of finite places of `F`, not dividing `p`.

Suppose furthermore
* `ρ` unramified outside `S` and `p`;
* `ρ` descends to `ρ₀ : Gal(F-bar/F) -> GL_2(R)` with `R ⊆ ℚ_p-bar` a subring finite
  free over ℤ_p, and `ρ₀` is flat at all places of F dividing `p`;
* If `v ∈ S` then the restriction of `ρ` to `Fᵥ` has a rank one tame quotient;
* `det(ρ)` is the cyclotomic character.

Then `ρ` is automorphic of level U₁(S) iff ρ|G_E is automorphic of level U₁(S_E),
where S_E is the pullback of S to E.
-/
theorem cyclic_base_change
    -- let F be a totally real number field of even degree
    {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    (hF : Even (Module.finrank ℚ F))
    -- let E/F be a finite solvable extension
    {E : Type*} [Field E] [NumberField E] [IsTotallyReal E]
    [Algebra F E] [IsGalois F E] [IsSolvable (E ≃ₐ[F] E)]
    -- let p be a prime
    (p : ℕ) [Fact p.Prime]
    -- let ρ:Gal(F-bar/F)->GL_2(Q_p-bar) be a continuous representation
    {V : Type} [AddCommGroup V] [Module (ℚ_[p]ᵃˡᵍ) V]
      [Module.Finite (ℚ_[p]ᵃˡᵍ) V] [Module.Free (ℚ_[p]ᵃˡᵍ) V]
      (hV : Module.finrank (ℚ_[p]ᵃˡᵍ) V = 2)
    (ρ : GaloisRep F (ℚ_[p]ᵃˡᵍ) V)
    -- Assume ρ|G_E is irreducible
    (hρirred : GaloisRep.IsIrreducible (ρ.map (algebraMap F E)))
    -- Assume det(rho)=cyclo
    (hρdet : ∀ g, ρ.det g = algebraMap ℤ_[p] (ℚ_[p]ᵃˡᵍ)
      (cyclotomicCharacter (AlgebraicClosure F) p g.toRingEquiv))
    -- Assume rho is flat at all primes of F above p
    -- This is slightly delicate because we need an integral model to
    -- talk about flatness
    (hρflat :
      -- there's an integral model ρ₀ of ρ
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℤ_[p] R) (_ : IsLocalRing R) (_ : IsDomain R)
        (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
        (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R) (_ : IsModuleTopology ℤ_[p] R)
        (_ : Algebra R (ℚ_[p]ᵃˡᵍ)) (_ : IsScalarTower ℤ_[p] R (ℚ_[p]ᵃˡᵍ))
        (_ : ContinuousSMul R (ℚ_[p]ᵃˡᵍ))
        (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module R V₀) (_ : Module.Finite R V₀)
        (_ : Module.Free R V₀) (hW : Module.rank R V₀ = 2)
        (ρ₀ : GaloisRep F R V₀)
        (r₀ : (ℚ_[p]ᵃˡᵍ) ⊗[R] V₀ ≃ₗ[ℚ_[p]ᵃˡᵍ] V),
      (ρ₀.baseChange (ℚ_[p]ᵃˡᵍ)).conj r₀ = ρ ∧
      -- such that ρ₀ is flat at all places of F dividing p
      ∀ v : HeightOneSpectrum (𝓞 F), ↑p ∈ v.asIdeal → ρ₀.IsFlatAt v)
    -- Let S be a finite set of finite places of F, not dividing p
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, ↑p ∉ v.asIdeal)
    -- Assume rho is unramified outside pS
    (hρunram : ∀ v ∉ S, ↑p ∉ v.asIdeal → ρ.IsUnramifiedAt v)
    -- and that if w ∈ S then rho has a tame rank 1 quotient at w
    (hρtame : ∀ w ∈ S, ∃ (π : V →ₗ[ℚ_[p]ᵃˡᵍ] ℚ_[p]ᵃˡᵍ)
      -- i.e. there's a surjection π : V → Q_p-bar
      (_ : Function.Surjective π)
      -- and a 1-d character of Gal(F_w-bar/F_w)
      (δ : GaloisRep (w.adicCompletion F) (ℚ_[p]ᵃˡᵍ) (ℚ_[p]ᵃˡᵍ)),
      -- such that δ is tamely ramified
      localTameAbelianInertiaGroup w ≤ δ.ker ∧
      -- and π is Gal(F_w-bar/F_w)-equivariant
      ∀ g : Γ (w.adicCompletion F), ∀ v : V, π ((ρ.toLocal w) g v) = δ g (π v)) :
    -- Then ρ is automorphic of level S iff
    (ρ.IsAutomorphicOfLevel p hV S) ↔
    -- ρ | Gal(Ebar/E) is automorphic of level (the pullback of S to E)
    ((ρ.map (algebraMap F E)).IsAutomorphicOfLevel p hV
      (HeightOneSpectrum.preimageComapFinset (𝓞 F) F E (𝓞 E) S)) :=
  sorry
