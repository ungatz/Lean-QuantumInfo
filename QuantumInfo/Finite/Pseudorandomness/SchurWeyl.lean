/-
Copyright (c) 2026 Sanad. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sanad
-/
import QuantumInfo.Finite.Pseudorandomness.TensorPower

/-! # Schur–Weyl Duality (Partial)

This file defines the permutation representation φ : S_k → U(H^{⊗k}) and proves
the fundamental commutativity [ψ(U), φ(π)] = 0 between the diagonal unitary
representation and the permutation representation.

## Main definitions

* `permMatrix d k σ` — the matrix on `(Fin k → d)` that permutes tensor factors by σ.
* `permRep d k` — the permutation representation as a group homomorphism
  `Equiv.Perm (Fin k) →* 𝐔[Fin k → d]`.

## Main results

* `permMatrix_unitary` — permutation matrices are unitary.
* `diagUnitary_mul_permMatrix_comm` — commutativity of the two representations.

## Later additions (sorry'd)

* `commutant_eq_spanPerm` — the commutant of {U^{⊗k}} equals span of permutation operators.
* `schurWeylDecomposition` — the full Schur–Weyl decomposition of H^{⊗k}.
-/

noncomputable section

open Matrix BigOperators

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Permutation Representation -/

/-- The permutation matrix on the tensor product space `Fin k → d`.
Given σ : Equiv.Perm (Fin k), this permutes the tensor factors:
  `(φ(σ) · v)(i₁, ..., iₖ) = v(i_{σ⁻¹(1)}, ..., i_{σ⁻¹(k)})`.

As a matrix: `permMatrix d k σ f g = if f = g ∘ σ.symm then 1 else 0`,
i.e., it maps basis vector |g⟩ to |g ∘ σ.symm⟩ = |g ∘ σ⁻¹⟩. -/
def permMatrix (d : Type*) [DecidableEq d] (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Matrix (Fin k → d) (Fin k → d) ℂ :=
  Matrix.of fun f g => if f = g ∘ σ.symm then 1 else 0

@[simp]
theorem permMatrix_apply (k : ℕ) (σ : Equiv.Perm (Fin k)) (f g : Fin k → d) :
    permMatrix d k σ f g = if f = g ∘ σ.symm then 1 else 0 := by
  rfl

/-- A right-composition form of `permMatrix_apply` that is often more convenient in proofs. -/
theorem permMatrix_apply_comp (k : ℕ) (σ : Equiv.Perm (Fin k)) (f g : Fin k → d) :
    permMatrix d k σ f g = if g = f ∘ σ then 1 else 0 := by
  rw [permMatrix_apply]
  by_cases h : g = f ∘ σ
  · have h' : f = g ∘ σ.symm := by
      ext i
      simpa [Function.comp_apply] using (congrFun h (σ.symm i)).symm
    rw [if_pos h', if_pos h]
  · have h' : ¬ f = g ∘ σ.symm := by
      intro hfg
      apply h
      ext i
      simpa [Function.comp_apply] using (congrFun hfg (σ i)).symm
    rw [if_neg h', if_neg h]

/-- The identity permutation gives the identity matrix. -/
@[simp]
theorem permMatrix_one (k : ℕ) :
    permMatrix d k 1 = 1 := by
  ext f g
  rw [permMatrix_apply, Matrix.one_apply]
  simp

/-- The column indexed by `f` is the computational basis vector indexed by `f ∘ σ.symm`. -/
theorem permMatrix_col (k : ℕ) (σ : Equiv.Perm (Fin k)) (f : Fin k → d) :
    (permMatrix d k σ).col f = Pi.single (f ∘ σ.symm) 1 := by
  ext g
  simp [Matrix.col, Pi.single_apply, permMatrix_apply]

/-- Acting on a computational basis vector permutes the tensor factors by `σ`. -/
@[simp]
theorem permMatrix_mulVec_single (k : ℕ) (σ : Equiv.Perm (Fin k)) (f : Fin k → d) :
    permMatrix d k σ *ᵥ Pi.single f 1 = Pi.single (f ∘ σ.symm) 1 := by
  rw [Matrix.mulVec_single_one, permMatrix_col]

/-- The permutation matrix for a composition is the product of permutation matrices. -/
theorem permMatrix_mul (k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    permMatrix d k (σ * τ) = permMatrix d k σ * permMatrix d k τ := by
  ext f g
  rw [Matrix.mul_apply, Finset.sum_eq_single (g ∘ τ.symm)]
  · have hτ : permMatrix d k τ (g ∘ τ.symm) g = 1 := by
      rw [permMatrix_apply]
      simp
    rw [hτ, mul_one, permMatrix_apply, permMatrix_apply]
    have hsymm : (σ * τ).symm = τ.symm * σ.symm := by
      ext i
      have h : (σ * τ).symm i = (τ.symm * σ.symm) i := by
        rw [Equiv.symm_apply_eq]
        simp [Equiv.Perm.mul_apply]
      exact congrArg Fin.val h
    have hcomp : g ∘ (σ * τ).symm = (g ∘ τ.symm) ∘ σ.symm := by
      ext i
      rw [hsymm]
      rfl
    rw [hcomp]
  · intro h _ hh
    have hh' : permMatrix d k τ h g = 0 := by
      rw [permMatrix_apply]
      simp [hh]
    rw [hh', mul_zero]
  · intro h_abs
    exact absurd (Finset.mem_univ _) h_abs

/-- The conjTranspose of a permutation matrix is the permutation matrix for the inverse. -/
theorem conjTranspose_permMatrix (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (permMatrix d k σ)ᴴ = permMatrix d k σ⁻¹ := by
  ext f g
  rw [Matrix.conjTranspose_apply, permMatrix_apply, permMatrix_apply]
  by_cases h : g = f ∘ σ.symm
  · have h' : f = g ∘ σ := by
      ext i
      simpa [Function.comp_apply] using (congrFun h (σ i)).symm
    have h'' : f = g ∘ (σ⁻¹).symm := by
      simpa using h'
    rw [if_pos h, if_pos h'']
    simp
  · have h' : ¬ f = g ∘ σ := by
      intro hfg
      apply h
      ext i
      simpa [Function.comp_apply] using (congrFun hfg (σ.symm i)).symm
    have h'' : ¬ f = g ∘ (σ⁻¹).symm := by
      simpa using h'
    rw [if_neg h, if_neg h'']
    simp

/-- Permutation matrices are unitary. -/
theorem permMatrix_unitary (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    permMatrix d k σ ∈ 𝐔[Fin k → d] := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, _root_.conjTranspose_permMatrix]
  rw [← permMatrix_mul]
  simp

/-- The permutation representation as a monoid homomorphism. -/
def permRep (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    Equiv.Perm (Fin k) →* 𝐔[Fin k → d] where
  toFun σ := ⟨permMatrix d k σ, permMatrix_unitary k σ⟩
  map_one' := by
    apply Subtype.ext
    exact permMatrix_one (d := d) k
  map_mul' σ τ := by
    apply Subtype.ext
    exact permMatrix_mul (d := d) k σ τ

/-! ## Commutativity of the Two Representations -/

/-- **Key commutativity result**: The diagonal unitary representation and the permutation
representation commute. That is, for all U : 𝐔[d] and σ : Equiv.Perm (Fin k),
  `U^{⊗k} * φ(σ) = φ(σ) * U^{⊗k}`.

Intuitively: applying the same unitary U to every tensor factor and then permuting factors
gives the same result as permuting first and then applying U to every factor. -/
theorem diagUnitary_mul_permMatrix_comm (k : ℕ) (U : 𝐔[d]) (σ : Equiv.Perm (Fin k)) :
    (unitaryTensorPower k U).val * permMatrix d k σ =
    permMatrix d k σ * (unitaryTensorPower k U).val := by
  ext f h
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single (h ∘ σ.symm)]
  · rw [Finset.sum_eq_single (f ∘ σ)]
    · have hleft : permMatrix d k σ (h ∘ σ.symm) h = 1 := by
        rw [permMatrix_apply]
        simp
      have hright : permMatrix d k σ f (f ∘ σ) = 1 := by
        rw [permMatrix_apply_comp]
        simp
      rw [hleft, hright, mul_one, one_mul, unitaryTensorPower_apply, unitaryTensorPower_apply]
      refine Fintype.prod_equiv σ.symm
        (fun i : Fin k => U.val (f i) (h (σ.symm i)))
        (fun i : Fin k => U.val (f (σ i)) (h i)) ?_
      intro i
      simp
    · intro g _ hg
      have hg' : permMatrix d k σ f g = 0 := by
        rw [permMatrix_apply_comp]
        simp [hg]
      rw [hg', zero_mul]
    · intro h_abs
      exact absurd (Finset.mem_univ _) h_abs
  · intro g _ hg
    have hg' : permMatrix d k σ g h = 0 := by
      rw [permMatrix_apply]
      simp [hg]
    rw [hg', mul_zero]
  · intro h_abs; exact absurd (Finset.mem_univ _) h_abs

/-- The commutativity as a `Commute` statement. -/
theorem commute_tensorPower_permMatrix (k : ℕ) (U : 𝐔[d]) (σ : Equiv.Perm (Fin k)) :
    Commute (unitaryTensorPower k U).val (permMatrix d k σ) := by
  show (unitaryTensorPower k U).val * permMatrix d k σ =
      permMatrix d k σ * (unitaryTensorPower k U).val
  exact diagUnitary_mul_permMatrix_comm k U σ

/-! ## Commutant (sorry'd — requires Schur–Weyl duality) -/

/-- The commutant of the diagonal unitary representation: the set of all matrices on H^{⊗k}
that commute with U^{⊗k} for every U : 𝐔[d]. -/
def unitaryCommutant (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    Set (Matrix (Fin k → d) (Fin k → d) ℂ) :=
  {T | ∀ U : 𝐔[d], Commute (unitaryTensorPower k U).val T}

/-- Permutation matrices are in the commutant. -/
theorem permMatrix_mem_unitaryCommutant (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    permMatrix d k σ ∈ unitaryCommutant d k :=
  fun U => commute_tensorPower_permMatrix k U σ

/-- **Schur–Weyl commutant theorem** (sorry'd): The commutant of {U^{⊗k} | U ∈ 𝐔[d]}
equals the linear span of {φ(σ) | σ ∈ S_k}. This is one formulation of Schur–Weyl duality. -/
theorem commutant_eq_spanPerm (k : ℕ) :
    unitaryCommutant d k =
    (↑(Submodule.span ℂ {M | ∃ σ : Equiv.Perm (Fin k), M = permMatrix d k σ}) :
      Set (Matrix (Fin k → d) (Fin k → d) ℂ)) := by
  sorry

end
