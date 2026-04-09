/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Instances.ZMod
import FLT.Deformations.RepresentationTheory.GaloisRep
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

abbrev WeierstrassCurve.n_torsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E ⟮k⟯) n

--variable (n : ℕ) in
--#synth AddCommGroup (E.n_torsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.n_torsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.n_torsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.n_torsion n) = n^2 := sorry

/-! ### Helper lemmas for `group_theory_lemma` -/

section group_theory_lemma_helpers

/-- Bezout-based: if d • x = 0 and n • x = 0 in an abelian group, then gcd(d,n) • x = 0. -/
private lemma smul_natGcd_eq_zero' {A : Type*} [AddCommGroup A]
    (d n : ℕ) {x : A} (hd : (d : ℤ) • x = 0) (hn : (n : ℤ) • x = 0) :
    (Nat.gcd d n : ℤ) • x = 0 := by
  rw [show (Nat.gcd d n : ℤ) = ((d : ℤ).gcd (n : ℤ) : ℤ) from by simp [Int.gcd_natCast_natCast],
      Int.gcd_eq_gcd_ab (d : ℤ) (n : ℤ), add_smul, mul_comm (d : ℤ), mul_smul,
      mul_comm (n : ℤ), mul_smul, hd, hn, smul_zero, smul_zero, add_zero]

/-- The d-torsion of the n-torsion equals the gcd(d,n)-torsion (as cardinalities).
Concretely: A[n][d] has the same number of elements as A[gcd(d,n)], because an element
x satisfies both n • x = 0 and d • x = 0 if and only if gcd(d,n) • x = 0. -/
private theorem card_torsionBy_of_torsionBy' {A : Type*} [AddCommGroup A] (n d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A n) d) =
    Nat.card (Submodule.torsionBy ℤ A (Nat.gcd d n)) := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun x => ⟨x.1.1, ?_⟩) ⟨?_, ?_⟩
  · rw [Submodule.mem_torsionBy_iff]
    have hd : (d : ℤ) • (x.1 : A) = 0 := by
      have h := x.2; rw [Submodule.mem_torsionBy_iff] at h
      exact_mod_cast congr_arg Subtype.val h
    have hn : (n : ℤ) • (x.1 : A) = 0 := by
      have h := x.1.2; rw [Submodule.mem_torsionBy_iff] at h; exact h
    exact smul_natGcd_eq_zero' d n hd hn
  · intro x y heq
    simp only [Subtype.mk.injEq] at heq
    ext; exact heq
  · intro ⟨a, ha⟩
    rw [Submodule.mem_torsionBy_iff] at ha
    have hd : (d : ℤ) • a = 0 := by
      obtain ⟨k, hk⟩ : (Nat.gcd d n : ℤ) ∣ d := by exact_mod_cast Nat.gcd_dvd_left d n
      rw [hk, mul_comm, mul_smul, ha, smul_zero]
    have hn : (n : ℤ) • a = 0 := by
      obtain ⟨k, hk⟩ : (Nat.gcd d n : ℤ) ∣ n := by exact_mod_cast Nat.gcd_dvd_right d n
      rw [hk, mul_comm, mul_smul, ha, smul_zero]
    refine ⟨⟨⟨a, ?_⟩, ?_⟩, rfl⟩
    · rw [Submodule.mem_torsionBy_iff]; exact hn
    · rw [Submodule.mem_torsionBy_iff]
      change (d : ℤ) • (⟨a, _⟩ : Submodule.torsionBy ℤ A n) = 0
      ext; simp [hd]

/-- The torsion submodule distributes over pi types. -/
private def torsionBy_pi_equiv' {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    (R : Type*) [CommRing R] [∀ i, Module R (M i)] (a : R) :
    Submodule.torsionBy R (∀ i, M i) a ≃ ∀ i, Submodule.torsionBy R (M i) a where
  toFun x := fun i => ⟨(x.1 i), by
    rw [Submodule.mem_torsionBy_iff]
    have h := x.2; rw [Submodule.mem_torsionBy_iff] at h
    exact congr_fun h i⟩
  invFun f := ⟨fun i => (f i).1, by
    rw [Submodule.mem_torsionBy_iff]
    funext i
    have h := (f i).2; rw [Submodule.mem_torsionBy_iff] at h
    simp [h]⟩
  left_inv x := by ext; rfl
  right_inv f := by ext; rfl

/-- The cardinality of the d-torsion of ZMod n (for n > 0, d : ℕ) is gcd(d, n).
Uses the fact that ZMod n is an additive cyclic group and the kernel formula
from `IsAddCyclic.card_nsmulAddMonoidHom_ker`. -/
private theorem card_torsionBy_zmod_nat' (n d : ℕ) [NeZero n] :
    Nat.card (Submodule.torsionBy ℤ (ZMod n) (d : ℤ)) = Nat.gcd d n := by
  have h_eq : Nat.card (Submodule.torsionBy ℤ (ZMod n) (d : ℤ)) =
    Nat.card ((nsmulAddMonoidHom d : ZMod n →+ ZMod n).ker) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (Equiv.refl _) ?_
    intro x
    simp [Submodule.mem_torsionBy_iff, AddMonoidHom.mem_ker, nsmulAddMonoidHom,
          Nat.cast_smul_eq_nsmul ℤ]
  rw [h_eq, IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod, Nat.gcd_comm]

/-- Extension of `card_torsionBy_zmod_nat'` to integer argument d. -/
private theorem card_torsionBy_zmod' (n : ℕ) [NeZero n] (d : ℤ) :
    Nat.card (Submodule.torsionBy ℤ (ZMod n) d) = Int.gcd d n := by
  have h_eq : Submodule.torsionBy ℤ (ZMod n) d =
      Submodule.torsionBy ℤ (ZMod n) (d.natAbs : ℤ) := by
    ext x
    simp only [Submodule.mem_torsionBy_iff]
    rcases Int.natAbs_eq d with hd | hd <;>
    · constructor
      · intro h; rw [hd] at h; simpa using h
      · intro h; rw [hd]; simpa using h
  rw [h_eq, card_torsionBy_zmod_nat']
  simp [Int.gcd, Int.natAbs_natCast]

/-- The cardinality of the d-torsion of (Fin r → ZMod n) is (Int.gcd d n)^r. -/
private theorem card_torsionBy_pi_zmod' (n r : ℕ) [NeZero n] (d : ℤ) :
    Nat.card (Submodule.torsionBy ℤ (Fin r → ZMod n) d) = (Int.gcd d n) ^ r := by
  rw [Nat.card_congr (torsionBy_pi_equiv' ℤ d), Nat.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, card_torsionBy_zmod']

/-- Transport torsion cardinalities across an additive equivalence. -/
private lemma card_torsionBy_addEquiv' {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A d) = Nat.card (Submodule.torsionBy ℤ B d) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv e.toEquiv ?_
  intro a
  constructor
  · intro ha
    rw [Submodule.mem_torsionBy_iff] at ha ⊢
    change (d : ℤ) • (e a) = 0
    rw [← map_zsmul e, ha, map_zero]
  · intro hb
    rw [Submodule.mem_torsionBy_iff] at hb ⊢
    change (d : ℤ) • a = 0
    have hb' : (d : ℤ) • (e a) = 0 := hb
    have := congr_arg e.symm hb'
    rwa [map_zsmul, map_zero, AddEquiv.symm_apply_apply] at this

/-- The cardinality of the d-torsion of a pi type of ZMod's is the product of gcds. -/
private theorem card_torsionBy_pi_zmod_general' {ι : Type*} [Fintype ι] (n : ι → ℕ)
    [∀ i, NeZero (n i)] (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (n i)) (d : ℤ)) =
      ∏ i : ι, Nat.gcd d (n i) := by
  rw [Nat.card_congr (torsionBy_pi_equiv' ℤ (d : ℤ)), Nat.card_pi]
  congr 1; ext i; exact card_torsionBy_zmod_nat' (n i) d

/-- The cardinality of the d-torsion of a direct sum of ZMod's equals the product of gcds. -/
private theorem card_torsionBy_directSum_zmod' {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (DirectSum ι (fun i => ZMod (n i))) (d : ℤ)) =
      ∏ i : ι, Nat.gcd d (n i) := by
  rw [← card_torsionBy_pi_zmod_general' n d]
  exact card_torsionBy_addEquiv' (DirectSum.addEquivProd (fun i => ZMod (n i))) d

/-- If two Fintype-indexed families of positive naturals yield the same multiset,
there exists an equivalence between the index types preserving the values.
This follows from the general theory of multisets. -/
private lemma equiv_of_multiset_map_eq {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ}
    (h : Finset.univ.val.map n₁ = Finset.univ.val.map n₂) :
    ∃ (e : ι₁ ≃ ι₂), ∀ i, n₁ i = n₂ (e i) := by
  classical
  -- Equal multisets ⟹ equal fiber cardinalities ⟹ fiber equivalences
  have h_fiber : ∀ c : ℕ, Nonempty ({i : ι₁ // n₁ i = c} ≃ {j : ι₂ // n₂ j = c}) := by
    intro c
    apply Fintype.card_eq.mp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have hc : Multiset.count c (Finset.univ.val.map n₁) =
        Multiset.count c (Finset.univ.val.map n₂) := congr_arg _ h
    simp only [Multiset.count_map] at hc
    -- Convert Multiset.filter to Finset.filter
    have conv₁ : Multiset.card (Multiset.filter (fun a => c = n₁ a) Finset.univ.val) =
        (Finset.univ.filter (fun a => n₁ a = c)).card := by
      rw [← Finset.filter_val]; congr 1; ext x; simp [eq_comm]
    have conv₂ : Multiset.card (Multiset.filter (fun a => c = n₂ a) Finset.univ.val) =
        (Finset.univ.filter (fun a => n₂ a = c)).card := by
      rw [← Finset.filter_val]; congr 1; ext x; simp [eq_comm]
    rw [conv₁, conv₂] at hc
    exact hc
  -- Build the global equivalence from fiber equivalences
  exact ⟨Equiv.ofFiberEquiv (fun c => (h_fiber c).some),
    fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

/-- The multiset of invariant factors > 1 is uniquely determined by the function
d ↦ ∏ᵢ gcd(d, nᵢ). This is the hard combinatorial core: two multisets of naturals > 1
that give the same product of gcds for every d must be equal. -/
private theorem multiset_eq_of_prod_gcd_eq' {s t : Multiset ℕ}
    (hs : ∀ x ∈ s, 1 < x) (ht : ∀ x ∈ t, 1 < x)
    (h : ∀ d : ℕ, (s.map (Nat.gcd d)).prod = (t.map (Nat.gcd d)).prod) :
    s = t := by
  sorry

private theorem directSum_zmod_addEquiv_of_torsionBy_eq'
    {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {n₁ : ι₁ → ℕ} {n₂ : ι₂ → ℕ} [∀ i, NeZero (n₁ i)] [∀ i, NeZero (n₂ i)]
    (hn₁ : ∀ i, 1 < n₁ i) (hn₂ : ∀ i, 1 < n₂ i)
    (h : ∀ d : ℕ, ∏ i : ι₁, Nat.gcd d (n₁ i) = ∏ i : ι₂, Nat.gcd d (n₂ i)) :
    Nonempty (DirectSum ι₁ (fun i => ZMod (n₁ i)) ≃+
             DirectSum ι₂ (fun i => ZMod (n₂ i))) := by
  -- Step 1: Show the multisets of moduli are equal
  have h_multi : Finset.univ.val.map n₁ = Finset.univ.val.map n₂ := by
    apply multiset_eq_of_prod_gcd_eq'
    · intro x hx; obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx; exact hn₁ i
    · intro x hx; obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx; exact hn₂ i
    · intro d
      simp only [Multiset.map_map, Function.comp]
      rw [← Finset.prod_eq_multiset_prod, ← Finset.prod_eq_multiset_prod]
      exact h d
  -- Step 2: Get an equivalence between index types
  obtain ⟨σ, hσ⟩ := equiv_of_multiset_map_eq h_multi
  -- Step 3: Build the isomorphism via pi types
  -- ⨁ᵢ₁ ZMod(n₁ i₁) ≃ ∀ i₁, ZMod(n₁ i₁) ≃ ∀ i₁, ZMod(n₂ (σ i₁)) ≃ ∀ i₂, ZMod(n₂ i₂) ≃ ⨁ᵢ₂ ZMod(n₂ i₂)
  refine ⟨(DirectSum.addEquivProd (fun i => ZMod (n₁ i))).trans ?_ |>.trans
    (DirectSum.addEquivProd (fun i => ZMod (n₂ i))).symm⟩
  exact (AddEquiv.piCongrRight fun i₁ => (ZMod.ringEquivCongr (hσ i₁)).toAddEquiv).trans
    (RingEquiv.piCongrLeft (fun i₂ => ZMod (n₂ i₂)) σ).toAddEquiv

/-- Two finite abelian groups with the same d-torsion cardinality for all d are isomorphic.
This follows from the uniqueness of the invariant factor decomposition: the function
d ↦ |G[d]| determines the multiset of elementary divisors p^e in the structure theorem
decomposition G ≃ ⨁ᵢ ℤ/nᵢℤ. -/
private theorem addEquiv_of_torsionBy_card_eq' {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Finite G] [Finite H]
    (h : ∀ d : ℕ, Nat.card (Submodule.torsionBy ℤ G d) =
      Nat.card (Submodule.torsionBy ℤ H d)) :
    Nonempty (G ≃+ H) := by
  classical
  -- Apply the structure theorem to both groups
  obtain ⟨ι₁, _, n₁, hn₁, ⟨e₁⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' G
  obtain ⟨ι₂, _, n₂, hn₂, ⟨e₂⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' H
  haveI : ∀ i, NeZero (n₁ i) := fun i => ⟨by linarith [hn₁ i]⟩
  haveI : ∀ i, NeZero (n₂ i) := fun i => ⟨by linarith [hn₂ i]⟩
  -- Transfer torsion cardinality condition to products of gcds
  have h_prod : ∀ d : ℕ, ∏ i : ι₁, Nat.gcd d (n₁ i) = ∏ i : ι₂, Nat.gcd d (n₂ i) := by
    intro d
    rw [← card_torsionBy_directSum_zmod' n₁ d, ← card_torsionBy_addEquiv' e₁ d,
        h d, card_torsionBy_addEquiv' e₂ d, card_torsionBy_directSum_zmod' n₂ d]
  -- Use the direct sum isomorphism
  obtain ⟨φ⟩ := directSum_zmod_addEquiv_of_torsionBy_eq' hn₁ hn₂ h_prod
  exact ⟨e₁.trans (φ.trans e₂.symm)⟩

end group_theory_lemma_helpers

theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  -- Step 1: A[n] is finite (from h at d = n, giving |A[n]| = n^r > 0)
  have hfin : Finite (Submodule.torsionBy ℤ A n) :=
    Nat.finite_of_card_ne_zero (by rw [h n dvd_rfl]; exact pow_ne_zero _ hn.ne')
  -- Step 2: (Fin r → ZMod n) is finite
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : Finite (Fin r → ZMod n) := Pi.finite
  -- Step 3: Apply uniqueness of invariant factors.
  -- We show the d-torsion cardinalities of A[n] and (Fin r → ZMod n) agree for ALL d.
  -- For any d: |A[n][d]| = |A[gcd(d,n)]| (by card_torsionBy_of_torsionBy')
  --            = gcd(d,n)^r           (by h, since gcd(d,n) | n)
  --            = |(Fin r → ZMod n)[d]| (by card_torsionBy_pi_zmod')
  apply addEquiv_of_torsionBy_card_eq'
  intro d
  rw [card_torsionBy_of_torsionBy', card_torsionBy_pi_zmod', Int.gcd_natCast_natCast]
  exact h _ (Nat.gcd_dvd_right d n)

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.n_torsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.n_torsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- follows easily from the above
noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.n_torsion n) := sorry

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : E ⟮K⟯ →+ E ⟮L⟯ := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation_smul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E ⟮K⟯) := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable def WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E ⟮K⟯) where
      one_smul P := by cases P <;> rfl
      mul_smul g h P := by cases P <;> rfl
      smul_zero g := map_zero _
      smul_add g P Q := map_add _ P Q

-- the next `sorry` is data but the only thing which should be missing is
-- the continuity argument, which follows from the finiteness asserted above.

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).n_torsion n) := sorry
