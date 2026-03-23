/-
Copyright (c) 2026 Sanad. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sanad
-/
import QuantumInfo.Finite.Unitary
import QuantumInfo.Finite.MState

/-! # Tensor Powers of Unitaries and States

This file defines k-fold tensor powers of matrices, unitaries, and mixed states,
using `Fin k → d` as the index type for the k-fold tensor product space.

## Main definitions

* `Matrix.tensorPower M k` — the k-fold tensor power of a matrix M, with entries
  `(M^{⊗k})_{f,g} = ∏ i, M (f i) (g i)`.
* `unitaryTensorPower` — the tensor power as a monoid homomorphism `𝐔[d] →* 𝐔[Fin k → d]`.
* `MState.tensorPower ρ k` — the k-fold tensor product state ρ^{⊗k}.

## Index convention

The k-fold tensor product space H^{⊗k} is indexed by `Fin k → d`, where `d` is the
Hilbert space dimension type. This is consistent with Mathlib's `PiTensorProduct` and
`TensorPower` definitions. The existing project convention of `d₁ × d₂` for bipartite
systems corresponds to the special case `Fin 2 → d ≃ d × d`.
-/

noncomputable section

open Matrix BigOperators Kronecker Finset

variable {d : Type*} [Fintype d] [DecidableEq d]

namespace Matrix

/-- The k-fold tensor power of a matrix, defined componentwise as a product:
  `(M^{⊗k})_{f,g} = ∏ i : Fin k, M (f i) (g i)`.
  This gives the matrix representing M acting independently on each tensor factor. -/
def tensorPower (M : Matrix d d ℂ) (k : ℕ) : Matrix (Fin k → d) (Fin k → d) ℂ :=
  Matrix.of fun f g => ∏ i : Fin k, M (f i) (g i)

@[simp]
theorem tensorPower_apply {d : Type*} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (k : ℕ) (f g : Fin k → d) :
    M.tensorPower k f g = ∏ i : Fin k, M (f i) (g i) :=
  rfl

/-- The tensor power of the identity matrix is the identity. -/
@[simp]
theorem tensorPower_one (k : ℕ) :
    (1 : Matrix d d ℂ).tensorPower k = 1 := by
  ext f g
  by_cases hfg : f = g
  · subst hfg
    simp [tensorPower_apply]
  · simp [tensorPower_apply, Matrix.one_apply, hfg]
    obtain ⟨i, hi⟩ : ∃ i : Fin k, f i ≠ g i := by
      by_contra h
      apply hfg
      exact funext <| by simpa using h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The conjTranspose distributes over tensor power. -/
@[simp]
theorem conjTranspose_tensorPower (M : Matrix d d ℂ) (k : ℕ) :
    (M.tensorPower k)ᴴ = (Mᴴ).tensorPower k := by
  ext f g
  simp [tensorPower_apply, Matrix.conjTranspose_apply]

/-- star distributes over tensor power. -/
@[simp]
theorem star_tensorPower (M : Matrix d d ℂ) (k : ℕ) :
    star (M.tensorPower k) = (star M).tensorPower k := by
  rw [star_eq_conjTranspose, star_eq_conjTranspose]
  exact conjTranspose_tensorPower M k

/-- The tensor power is multiplicative: `(A * B)^{⊗k} = A^{⊗k} * B^{⊗k}`.

This is the key algebraic property that makes tensor power a monoid homomorphism.
The proof uses the generalized distributive law (`Fintype.prod_sum`):
`∏ i, ∑ j, f i j = ∑ x, ∏ i, f i (x i)`. -/
theorem tensorPower_mul (A B : Matrix d d ℂ) (k : ℕ) :
    (A * B).tensorPower k = A.tensorPower k * B.tensorPower k := by
  ext f h
  simp only [tensorPower_apply, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  congr 1; ext g
  exact Finset.prod_mul_distrib

/-- The tensor power of a unitary matrix is unitary. -/
theorem tensorPower_mem_unitaryGroup (U : 𝐔[d]) (k : ℕ) :
    U.val.tensorPower k ∈ 𝐔[Fin k → d] := by
  rw [Matrix.mem_unitaryGroup_iff, star_tensorPower, ← tensorPower_mul]
  have := Matrix.mem_unitaryGroup_iff.mp U.2
  rw [this, tensorPower_one]

end Matrix

/-- The k-fold tensor power as a monoid homomorphism from 𝐔[d] to 𝐔[Fin k → d].
This is the diagonal unitary representation ψ : U(d) → U(H^{⊗k}), U ↦ U^{⊗k}. -/
def unitaryTensorPower (k : ℕ) : 𝐔[d] →* 𝐔[Fin k → d] where
  toFun U := ⟨U.val.tensorPower k, Matrix.tensorPower_mem_unitaryGroup U k⟩
  map_one' := by
    apply Subtype.ext
    simp [Matrix.tensorPower_one]
  map_mul' U V := by
    apply Subtype.ext
    show ((U * V : 𝐔[d]).val).tensorPower k =
      U.val.tensorPower k * V.val.tensorPower k
    rw [Submonoid.coe_mul, Matrix.tensorPower_mul]

@[simp]
theorem unitaryTensorPower_val (k : ℕ) (U : 𝐔[d]) :
    (unitaryTensorPower k U).val = U.val.tensorPower k :=
  rfl

@[simp]
theorem unitaryTensorPower_apply (k : ℕ) (U : 𝐔[d]) (f g : Fin k → d) :
    (unitaryTensorPower k U).val f g = ∏ i : Fin k, U.val (f i) (g i) :=
  rfl

namespace MState

/-- The k-fold tensor power of a mixed state, reusing the library n-copy construction. -/
abbrev tensorPower (ρ : MState d) (k : ℕ) : MState (Fin k → d) :=
  ρ ⊗ᴹ^ k

@[simp]
theorem tensorPower_eq_npow (ρ : MState d) (k : ℕ) :
    ρ.tensorPower k = ρ ⊗ᴹ^ k :=
  rfl

@[simp]
theorem tensorPower_m (ρ : MState d) (k : ℕ) :
    (ρ.tensorPower k).m = ρ.m.tensorPower k := by
  ext f g
  rfl

/-- Unitary conjugation commutes with tensor power:
  applying `U^{⊗k}` to `ρ^{⊗k}` matches tensoring the conjugated state. -/
theorem U_conj_tensorPower (ρ : MState d) (U : 𝐔[d]) (k : ℕ) :
    (ρ.tensorPower k).U_conj (unitaryTensorPower k U) = (ρ.U_conj U).tensorPower k := by
  apply MState.ext_m
  change (((ρ.tensorPower k).M.conj (unitaryTensorPower k U).val).mat) =
      ((ρ.U_conj U).tensorPower k).m
  rw [HermitianMat.conj_apply_mat, unitaryTensorPower_val, MState.mat_M, tensorPower_m, tensorPower_m]
  rw [Matrix.conjTranspose_tensorPower]
  have hU_conj_m : (ρ.U_conj U).m = U.val * ρ.m * U.valᴴ := by
    change ((ρ.M.conj U.val).mat = U.val * ρ.m * U.valᴴ)
    simp
  rw [hU_conj_m, Matrix.tensorPower_mul, Matrix.tensorPower_mul]

end MState
