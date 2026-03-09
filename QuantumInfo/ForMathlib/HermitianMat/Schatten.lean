/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Rpow

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
variable [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {x q r : ℝ}

/-! # Schatten norms

-/

noncomputable section

/--
The Schatten p-norm of a matrix A is (Tr[(A*A)^(p/2)])^(1/p).
-/
noncomputable def schattenNorm (A : Matrix d d ℂ) (p : ℝ) : ℝ :=
  RCLike.re ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).cfc (· ^ (p/2))).trace ^ (1/p)

/-
For a positive Hermitian matrix A, ||A||_p = (Tr(A^p))^(1/p).
-/
theorem schattenNorm_hermitian_pow {A : HermitianMat d ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) :
    schattenNorm A.mat p = (A ^ p).trace ^ (1/p) := by
  convert congr_arg (· ^ (1 / p)) _ using 1
  convert congr_arg _ (A.cfc_sq_rpow_eq_cfc_rpow hA p hp) using 1
  unfold HermitianMat.trace
  convert rfl
  convert (A ^ 2).mat_cfc (· ^ (p / 2))
  ext
  simp only [HermitianMat.conjTranspose_mat, HermitianMat.mat_pow]
  convert rfl using 2
  rw [sq]
  exact Matrix.IsHermitian.cfc_eq _ _

theorem schattenNorm_nonneg (A : Matrix d d ℂ) (p : ℝ) : 0 ≤ schattenNorm A p := by
  refine Real.rpow_nonneg ?_ (1 / p)
  rw [ Matrix.trace ] at *
  simp_all [ Matrix.IsHermitian.cfc ] ;
  simp [ Matrix.mul_apply, Matrix.diagonal ] at *;
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  ring_nf
  exact add_nonneg ( mul_nonneg (by positivity) ( Real.rpow_nonneg ( by
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j ) _ ) ) ( mul_nonneg ( Real.rpow_nonneg ( by
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j ) _ ) (by positivity) )

lemma schattenNorm_pow_eq
  (A : HermitianMat d ℂ) (hA : 0 ≤ A) (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    schattenNorm (A ^ k).mat p = (schattenNorm A.mat (k * p)) ^ k := by
  rw [ schattenNorm_hermitian_pow, schattenNorm_hermitian_pow ] <;> try positivity;
  · rw [ ← Real.rpow_mul ] <;> ring_nf <;> norm_num [ hp.ne', hk.ne' ];
    · rw [ mul_comm, ← HermitianMat.rpow_mul ];
      exact hA;
    · -- Since $A$ is positive, $A^{k*p}$ is also positive, and the trace of a positive matrix is non-negative.
      have h_pos : 0 ≤ A ^ (k * p) := by
        exact HermitianMat.rpow_nonneg hA;
      exact HermitianMat.trace_nonneg h_pos;
  · exact HermitianMat.rpow_nonneg hA

lemma trace_eq_schattenNorm_rpow
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (r : ℝ) (hr : 0 < r) :
    (A ^ r).trace = (schattenNorm A.mat r) ^ r := by
  rw [schattenNorm_hermitian_pow hA hr, ← Real.rpow_mul] <;> norm_num [hr.ne']
  apply HermitianMat.trace_nonneg
  exact HermitianMat.rpow_nonneg hA

def singularValues (A : Matrix d d ℂ) : d → ℝ :=
  fun i => Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i)

lemma singularValues_nonneg (A : Matrix d d ℂ) (i : d) :
    0 ≤ singularValues A i := by
  apply Real.sqrt_nonneg

open InnerProductSpace in
/--
Scalar trace Young inequality for PSD matrices:
⟪A, B⟫ ≤ Tr[A^p]/p + Tr[B^q]/q for PSD A, B and conjugate p, q > 1.
-/
lemma HermitianMat.trace_young
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace / p + (B ^ q).trace / q := by
  --TODO Cleanup
  have h_schatten : ∀ (i j : d), (A.H.eigenvalues i) * (B.H.eigenvalues j) ≤ (A.H.eigenvalues i)^p / p + (B.H.eigenvalues j)^q / q := by
    intro i j
    have h_young : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → (1 < p → 1 / p + 1 / q = 1 → a * b ≤ (a^p) / p + (b^q) / q) := by
      intro a b ha hb hp hpq
      have h_young : a * b ≤ (a^p) / p + (b^q) / q := by
        have h_conj : 1 / p + 1 / q = 1 := hpq
        have h_pos : 0 < p ∧ 0 < q := by
          use zero_lt_one.trans hp
          refine lt_of_not_ge fun h ↦ ?_
          rw [ div_eq_mul_inv, div_eq_mul_inv ] at h_conj
          nlinarith [inv_nonpos.2 h, inv_mul_cancel₀ (by linarith : p ≠ 0)]
        have := @Real.geom_mean_le_arith_mean
        specialize this { 0, 1 } ( fun i => if i = 0 then p⁻¹ else q⁻¹ ) ( fun i => if i = 0 then a ^ p else b ^ q ) ; simp_all [ ne_of_gt ];
        simpa only [ div_eq_inv_mul ] using this h_pos.1.le h_pos.2.le ( Real.rpow_nonneg ha _ ) ( Real.rpow_nonneg hb _ )
      exact h_young
    refine h_young _ _ ?_ ?_ hp hpq
    · exact (zero_le_iff.mp hA).eigenvalues_nonneg _
    · exact (zero_le_iff.mp hB).eigenvalues_nonneg _
  convert Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ( h_schatten i j ) ( show 0 ≤ ‖(A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val) i j‖ ^ 2 by positivity ) using 1;
  convert HermitianMat.inner_eq_doubly_stochastic_sum A B using 1;
  simp [ Finset.sum_add_distrib, add_mul, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm, HermitianMat.trace_rpow_eq_sum ];
  simp [ ← Finset.mul_sum, ← Finset.sum_comm, ];
  congr! 2;
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := Matrix.unitary_row_sum_norm_sq ( A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val ) ?_ i;
    · rw [ this, mul_one ];
    · simp [ Matrix.mul_assoc ];
      simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ];
  · refine' Finset.sum_congr rfl fun i _ => _;
    have := Matrix.unitary_col_sum_norm_sq ( A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val ) ?_ i <;> simp_all [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
    simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

/-- For PSD `A` and Hermitian `B`, the product
`C = A^{1/2} * B` satisfies `C^* C = (A.conj B.mat).mat = B * A * B`. -/
lemma conjTranspose_half_mul_eq_conj
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) :
    ((A ^ (1/2 : ℝ)).mat * B.mat).conjTranspose * ((A ^ (1/2 : ℝ)).mat * B.mat)
    = (A.conj B.mat).mat := by
  have := HermitianMat.pow_half_mul hA; simp_all [ ← mul_assoc ] ;
  simp only [mul_assoc, this]

lemma schattenNorm_half_mul_rpow_eq_trace_conj
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A)
    {α : ℝ} (hα : 0 < α) :
    (schattenNorm ((A ^ (1/2 : ℝ)).mat * B.mat) (2 * α)) ^ (2 * α) =
    ((A.conj B.mat) ^ α).trace := by
  have h_conj : ((A ^ (1 / 2 : ℝ)).mat * B.mat).conjTranspose * ((A ^ (1 / 2 : ℝ)).mat * B.mat) = (A.conj B.mat).mat := by
    exact conjTranspose_half_mul_eq_conj hA;
  unfold schattenNorm;
  rw [ ← Real.rpow_mul ] <;> norm_num [ hα.ne' ];
  · ring_nf; norm_num [ hα.ne' ];
    rw [ ← Matrix.IsHermitian.cfc_eq ];
    rw [ Matrix.conjTranspose_conjTranspose ];
    exact congrArg Complex.re (congrArg Matrix.trace (congrArg (cfc fun x => x ^ α) h_conj));
  · have h_eigenvalues_nonneg : ∀ i, 0 ≤ (Matrix.isHermitian_mul_conjTranspose_self ((A ^ (1 / 2 : ℝ)).mat * B.mat).conjTranspose).eigenvalues i := by
      intro i; exact (by
      have := Matrix.eigenvalues_conjTranspose_mul_self_nonneg ( ( A ^ ( 1 / 2 : ℝ ) ).mat * B.mat ) i; aesop;);
    simp_all [ Matrix.trace, Matrix.IsHermitian.cfc ];
    simp_all [ Matrix.mul_apply, Matrix.diagonal ];
    refine' Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => _;
    field_simp;
    exact mul_nonneg ( Real.rpow_nonneg ( h_eigenvalues_nonneg j ) _ ) (by positivity)

/-!
The *Schatten–Hölder inequality* for matrix products:
For matrices `A`, `B` and exponents `r, p, q > 0` with `1/r = 1/p + 1/q`,
the Schatten `r`-norm of the product satisfies
  `‖A * B‖_{S^r} ≤ ‖A‖_{S^p} * ‖B‖_{S^q}`.
This version includes the quasi-norm case (r, p, q < 1).
-/
lemma schattenNorm_mul_le (A B : Matrix d d ℂ) {r p q : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hq : 0 < q) (hpqr : 1 / r = 1 / p + 1 / q) :
    schattenNorm (A * B) r ≤ schattenNorm A p * schattenNorm B q := by
  sorry

lemma HermitianMat.trace_rpow_conj_le
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / (2 * α) = 1 / p + 1 / q) :
    ((A.conj B.mat) ^ α).trace ≤
    (((A ^ (p / 2)).trace) ^ (1 / p) * ((B ^ q).trace) ^ (1 / q)) ^ (2 * α) := by
  -- Raise both sides of the inequality to the power of $2\alpha$.
  have h_exp : ((A.conj B.mat) ^ α).trace ≤ (schattenNorm (A ^ (1 / 2 : ℝ)).mat p * schattenNorm B.mat q) ^ (2 * α) := by
    have h_exp : (schattenNorm ((A ^ (1 / 2 : ℝ)).mat * B.mat) (2 * α)) ^ (2 * α) = ((A.conj B.mat) ^ α).trace := by
      exact schattenNorm_half_mul_rpow_eq_trace_conj hA hα
    rw [← h_exp]
    -- Apply the Schatten-Hölder inequality to the matrices $A^{1/2} * B$.
    refine Real.rpow_le_rpow ?_ (schattenNorm_mul_le _ _ (by positivity) hp hq hpq) (by positivity)
    exact schattenNorm_nonneg _ _
  rw [schattenNorm_hermitian_pow (rpow_nonneg hA) hp, schattenNorm_hermitian_pow hB hq] at h_exp
  have h_exp_simp : (A ^ (1 / 2 : ℝ)) ^ p = A ^ (p / 2 : ℝ) := by
    rw [← HermitianMat.rpow_mul hA]
    ring_nf
  rw [h_exp_simp] at h_exp
  exact h_exp
