/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jonas Bayer
-/
import Mathlib.Data.Int.Star
import FLT.GlobalLanglandsConjectures.GLnDefs

/-!
# Proof of a case of the global Langlands conjectures.

Class Field Theory was one of the highlights of 19th century mathematics, linking
analysis to arithmetic of extensions of number fields with abelian Galois groups.
In the 1960s the main results had been re-interpreted as the GL(1) case of the global
Langlands conjectures. The general global Langlands conjectures are for GL(n) for any natural
number n, and work over any number field or global function field. Much is known in the function
field case (Lafforgue got a Fields Medal for his work on the topic), but the general number
field case remains largely open even today. For example we have very few results if the
base number field is not totally real or CM. For simplicity, let us stick to GL(n)/Q.

In 1993 Wiles announced his proof of the modularity of semistable elliptic curves over the
rationals. The result gave us a way of constructing automorphic forms from Galois representations;
refinements of the work by Taylor and others over the next decade led to a profound understanding
of the "holomorphic" or "odd" part of global Langlands functoriality for GL(2) over the rationals.
Wiles' work used class field theory (in the form of global Tate duality) crucially in a
central proof that a deformation ring R was isomorphic to a Hecke algebra T.

The fact that Wiles needed the theory for GL(1) to make progress in the GL(2) case,
is surely evidence that at the end of the day the proof for GL(n) is going to be by induction on n.
We will thus attempt to prove the global Langlands conjectures for GL(0).

## Structure of the proof

We will deduce the global Langlands conjectures for GL(0) from a far stronger theorem,
called the *classification theorem for automorphic representations for GL(0) over Q*.
This theorem gives a *canonical isomorphism* between the space of automorphic representations
and the complex numbers. Except in Lean we're not allowed to say "canonical" so instead
our "theorem" is a *definition* of a bijection.

## TODO

State them first.

-/

namespace AutomorphicForm

def GLn.Weight.IsTrivial {n : ℕ} (ρ : Weight n) : Prop := ρ.w.rho = 1

open GLn Manifold

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GL0

variable (ρ : Weight 0)

/-- Make an automorphic form for GL₀/ℚ from a complex number -/
def ofComplex (c : ℂ) : AutomorphicFormForGLnOverQ 0 ρ := {
    toFun := fun _ => c,
    is_smooth := {
      continuous := by continuity
      loc_cst := fun _ => IsLocallyConstant.const c
      smooth := by simp [contMDiff_const]
    }
    is_periodic := by simp
    is_slowly_increasing x := ⟨‖c‖, 0, by simp⟩
    is_finite_cod := by
      intro x
      -- For n=0, GL(Fin 0) ℝ is a point (Subsingleton).
      -- The Lie algebra is trivial, so UEA ≅ ℂ, Z ≅ ℂ,
      -- and any quotient of Z is finite-dimensional.
      haveI : Subsingleton (GL (Fin 0) ℝ) := inferInstance
      -- Step 1: LeftInvariantDerivation is unique (trivial).
      -- Every smooth function on a one-point space is constant,
      -- and derivations kill constants (algebraMap).
      haveI : Unique (LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin 0) (Fin 0) ℝ) (GL (Fin 0) ℝ)) := by
        refine ⟨⟨0⟩, fun a => ?_⟩
        ext f g
        have hf : f = algebraMap ℝ _ (f 1) := by
          ext ⟨y, hy⟩
          simp [Algebra.algebraMap_eq_smul_one]
          congr 1
          exact Subsingleton.elim _ _
        rw [hf]
        have h := a.toDerivation.map_algebraMap (f 1)
        change (a.toDerivation (algebraMap ℝ _ (f 1))) g =
          (0 : C^⊤⟮𝓘(ℝ, Matrix (Fin 0) (Fin 0) ℝ),
            GL (Fin 0) ℝ; 𝓘(ℝ, ℝ), ℝ⟯) g
        simp [h]
      -- LeftInvariantDerivation is Unique, so UEA(0) = ℂ.
      -- algebraMap ℂ → Alg is surjective, Z is f.d.
      let ret : Alg (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ)
          →ₐ[ℂ] ℂ := UniversalEnvelopingAlgebra.lift ℂ 0
      have h_section : ∀ a, algebraMap ℂ
          (Alg (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ))
          (ret a) = a := by
        intro a
        letI : Ring
            (Alg (GL (Fin 0) ℝ)
              (Matrix (Fin 0) (Fin 0) ℝ)) :=
          inferInstanceAs
            (Ring (UniversalEnvelopingAlgebra ℂ _))
        let A :=
          Alg (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ)
        have key : (Algebra.ofId ℂ A).comp ret =
            AlgHom.id ℂ A := by
          change (Algebra.ofId ℂ A).comp ret =
            AlgHom.id ℂ A
          have h1 : (Algebra.ofId ℂ A).comp ret =
            (UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A))
              ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).symm
                ((Algebra.ofId ℂ A).comp ret)) :=
            ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).apply_symm_apply _).symm
          have h2 : AlgHom.id ℂ A =
            (UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A))
              ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).symm
                (AlgHom.id ℂ A)) :=
            ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).apply_symm_apply _).symm
          rw [h1, h2]; congr 1; ext l
          simp [show l = 0 from Subsingleton.elim _ _]
        have h := AlgHom.congr_fun key a
        simp only [AlgHom.comp_apply,
          Algebra.ofId_apply] at h
        exact h
      have hAlg_surj : Function.Surjective
          (algebraMap ℂ (Alg (GL (Fin 0) ℝ)
            (Matrix (Fin 0) (Fin 0) ℝ))) :=
        fun a => ⟨ret a, h_section a⟩
      let toZ : ℂ →ₗ[ℂ]
          ↥(Z (GL (Fin 0) ℝ)
            (Matrix (Fin 0) (Fin 0) ℝ)) :=
        { toFun := fun z => ⟨algebraMap ℂ _ z, Subalgebra.algebraMap_mem _ z⟩
          map_add' := by intro a b; ext; simp [map_add]
          map_smul' := by intro a b; ext; simp [Algebra.smul_def] }
      have htoZ_surj : Function.Surjective toZ := by
        intro ⟨a, ha⟩
        obtain ⟨z, hz⟩ := hAlg_surj a
        exact ⟨z, by ext; exact hz⟩
      haveI : Module.Finite ℂ ↥(Z (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ)) :=
        Module.Finite.of_surjective toZ htoZ_surj
      exact Module.Finite.quotient _ _
    has_finite_level := by
      let U : Subgroup (GL (Fin 0) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) := {
        carrier := {1},
        one_mem' := by simp,
        mul_mem' := by simp
        inv_mem' := by simp
      }
      apply Exists.intro U
      exact {
          is_open := by
            convert isOpen_univ
            ext x
            simp [show x = 1 from Subsingleton.elim x 1]
          is_compact := by aesop
          finite_level := by simp
      }
  }

-- the weakest form of the classification theorem
noncomputable def classification : AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ := {
  toFun := fun f ↦ f 1
  invFun := fun c ↦ ofComplex ρ c
  left_inv := by
    rw [Function.LeftInverse]
    simp only [ofComplex]
    intro x
    have h: x.toFun = fun _ => x.toFun 1 := by
      exact funext fun g ↦ congrArg x.toFun <| Subsingleton.eq_one g
    simp_rw [← h]
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    simp [ofComplex]
}

end GL0

namespace GLn

-- Let's write down an inverse
-- For general n, it will only work for ρ the trivial representation, but we didn't
-- define the trivial representation yet.
-- Some of the other fields will work for all n.
def ofComplex (z : ℂ) {n : ℕ} (ρ : Weight n) (hρ : ρ.IsTrivial) :
    AutomorphicFormForGLnOverQ n ρ where
      toFun _ := z
      is_smooth := {
        continuous := by continuity
        loc_cst := fun _ => IsLocallyConstant.const z
        smooth := by simp [contMDiff_const]
      }
      is_periodic := by simp
      is_slowly_increasing x := ⟨‖z‖, 0, by simp⟩
      is_finite_cod := sorry -- needs a better name
      has_finite_level := sorry -- needs a better name

-- no idea why it's not computable
noncomputable def classification (ρ : Weight 0) : AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ where
  toFun f := f 1
  invFun z := ofComplex z ρ (by
    unfold Weight.IsTrivial
    ext g
    rw [show g = 1 from Subsingleton.elim g 1, map_one, map_one])
  left_inv := by
    rw [Function.LeftInverse]
    simp only [ofComplex]
    intro x
    have h : x.toFun = fun _ => x.toFun 1 := by
      exact funext fun g ↦ congrArg x.toFun <| Subsingleton.eq_one g
    simp_rw [← h]
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    simp [ofComplex]

-- Can this be beefed up to an isomorphism of complex
-- vector spaces?

end GLn

end AutomorphicForm
