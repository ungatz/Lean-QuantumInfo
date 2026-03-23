import QuantumInfo.Finite.Pseudorandomness.Twirl
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Schatten
import QuantumInfo.ForMathlib.HermitianMat.Trace
import Mathlib.Algebra.Order.Chebyshev

/-! # Norms On Superoperators

This file defines the finite-dimensional superoperator norms used later in the
pseudorandomness development.

## Conventions

* `superoperatorNorm_2to2` uses `schattenNorm _ 2` on matrices, i.e. the
  finite-dimensional Hilbert-Schmidt/Frobenius norm.
* `diamondNorm` is the repo's working finite-dimensional stabilized trace-norm
  definition, using ancilla dimension equal to the input dimension.

At this stage we only package the definitions. Deeper analytical properties are
left to later files.
-/

noncomputable section

open ComplexOrder
open scoped MatrixOrder
set_option maxHeartbeats 4000000

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The finite-dimensional `2→2` norm of a superoperator, defined using the
matrix Schatten-2 norm on domain and codomain. -/
noncomputable def superoperatorNorm_2to2
    {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]
    (Φ : MatrixMap dIn dOut ℂ) : ℝ :=
  sSup { schattenNorm (Φ X) 2 / schattenNorm X 2 |
    (X : Matrix dIn dIn ℂ) (_ : schattenNorm X 2 ≠ 0) }

/-- A finite-dimensional working definition of the diamond norm, given by the
stabilized trace norm with ancilla dimension equal to the input dimension. This
file does not yet prove equivalence with more abstract completely bounded
trace-norm formulations. -/
noncomputable def diamondNorm (Φ : MatrixMap d d ℂ) : ℝ :=
  sSup { ((MatrixMap.kron Φ (MatrixMap.id d ℂ) X).traceNorm / X.traceNorm) |
    (X : Matrix (d × d) (d × d) ℂ) (_ : X.traceNorm ≠ 0) }

/-- The Schatten norm of the zero matrix. -/
theorem schattenNorm_zero {d : Type*} [Fintype d] [DecidableEq d] {p : ℝ} (hp : 0 < p) :
    schattenNorm (0 : Matrix d d ℂ) p = 0 := by
  rw [schattenNorm_eq_sum_singularValues_rpow (A := (0 : Matrix d d ℂ)) hp]
  have hsv : ∀ i : d, singularValues (0 : Matrix d d ℂ) i = 0 := by
    intro i
    unfold singularValues
    have hz :
        (Matrix.isHermitian_mul_conjTranspose_self ((0 : Matrix d d ℂ).conjTranspose)).eigenvalues = 0 := by
      exact
        (Matrix.isHermitian_mul_conjTranspose_self ((0 : Matrix d d ℂ).conjTranspose)).eigenvalues_eq_zero_iff.2
          (by simp)
    rw [congrFun hz i]
    simp
  simp [hsv, hp.ne', Real.zero_rpow hp.ne']

/-- The trace of `Aᴴ * A` expands as the sum of squared entry norms. -/
lemma trace_conjTranspose_mul_self_re_eq_sum_norm_sq
    {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    Complex.re ((A.conjTranspose * A).trace) = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
  calc
    Complex.re ((A.conjTranspose * A).trace)
      = ∑ x, ∑ y, ((A y x).re * (A y x).re + (A y x).im * (A y x).im) := by
          simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Complex.mul_re]
    _ = ∑ x, ∑ y, ‖A y x‖ ^ (2 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro y _
          calc
            (A y x).re * (A y x).re + (A y x).im * (A y x).im = Complex.normSq (A y x) := by
              rw [Complex.normSq_apply]
            _ = ‖A y x‖ ^ (2 : ℝ) := by
              simpa using (Complex.sq_norm (A y x)).symm
    _ = ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) := by
          rw [Finset.sum_comm]

section FrobeniusNorm

open scoped Matrix.Norms.Frobenius

/-- At `p = 2`, the Schatten norm agrees with the Frobenius norm. -/
lemma schattenNorm_two_eq_frobenius
    {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    schattenNorm A 2 = ‖A‖ := by
  unfold schattenNorm
  rw [show ((fun t : ℝ => t ^ (2 / 2 : ℝ)) : ℝ → ℝ) = id by
    funext t
    norm_num]
  rw [← Matrix.IsHermitian.cfc_eq (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose) id]
  rw [Matrix.conjTranspose_conjTranspose]
  have hsa : IsSelfAdjoint (A.conjTranspose * A) := by
    simpa [Matrix.conjTranspose_conjTranspose] using
      (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).isSelfAdjoint
  rw [cfc_id ℝ (A.conjTranspose * A) hsa]
  rw [Matrix.frobenius_norm_def]
  congr 1
  exact trace_conjTranspose_mul_self_re_eq_sum_norm_sq A

/-- The trace norm is the sum of the singular values. -/
lemma traceNorm_eq_sum_singularValues
    {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    A.traceNorm = ∑ i : d, singularValues A i := by
  let H : HermitianMat d ℂ := ⟨A.conjTranspose * A, by
    simp [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  ⟩
  unfold Matrix.traceNorm
  rw [CFC.sqrt_eq_real_sqrt (A.conjTranspose * A) (by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.posSemidef_conjTranspose_mul_self A)]
  rw [cfcₙ_eq_cfc (a := A.conjTranspose * A) (f := Real.sqrt)]
  have hmat : cfc Real.sqrt (A.conjTranspose * A) = (H.cfc Real.sqrt).mat := by
    simp [H, HermitianMat.mat_cfc]
  rw [hmat]
  rw [← HermitianMat.trace_eq_trace_rc (A := H.cfc Real.sqrt)]
  rw [HermitianMat.trace_cfc_eq]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [H, singularValues]

/-- The Schatten-2 norm is bounded above by the trace norm. -/
lemma schattenNorm_two_le_traceNorm
    {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    schattenNorm A 2 ≤ A.traceNorm := by
  have hp : (0 : ℝ) < 2 := by
    norm_num
  rw [schattenNorm_eq_sum_singularValues_rpow A hp, traceNorm_eq_sum_singularValues A]
  have h_nonneg : ∀ i : d, 0 ≤ singularValues A i := by
    intro i
    unfold singularValues
    exact Real.sqrt_nonneg _
  have hsum_nonneg : 0 ≤ ∑ i : d, singularValues A i := by
    exact Finset.sum_nonneg fun i _ => h_nonneg i
  have hsq : ∑ i : d, singularValues A i ^ 2 ≤ (∑ i : d, singularValues A i) ^ 2 := by
    simpa using
      Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := singularValues A) (fun i _ => h_nonneg i)
  have hsqrt : Real.sqrt (∑ i : d, singularValues A i ^ 2) ≤ ∑ i : d, singularValues A i :=
    (Real.sqrt_le_iff).2 ⟨hsum_nonneg, hsq⟩
  simpa [Real.sqrt_eq_rpow] using hsqrt

/-- The trace norm is bounded by `sqrt(dim)` times the Schatten-2 norm. -/
lemma traceNorm_le_sqrt_card_mul_schattenNorm_two
    {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    A.traceNorm ≤ Real.sqrt (Fintype.card d) * schattenNorm A 2 := by
  have hp : (0 : ℝ) < 2 := by
    norm_num
  rw [traceNorm_eq_sum_singularValues A, schattenNorm_eq_sum_singularValues_rpow A hp]
  have h_nonneg : ∀ i : d, 0 ≤ singularValues A i := by
    intro i
    unfold singularValues
    exact Real.sqrt_nonneg _
  have hsum_nonneg : 0 ≤ ∑ i : d, singularValues A i := by
    exact Finset.sum_nonneg fun i _ => h_nonneg i
  have hsq : (∑ i : d, singularValues A i) ^ 2 ≤
      (Fintype.card d : ℝ) * ∑ i : d, singularValues A i ^ 2 := by
    simpa [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := singularValues A))
  have hsqrt : ∑ i : d, singularValues A i ≤
      Real.sqrt ((Fintype.card d : ℝ) * ∑ i : d, singularValues A i ^ 2) := by
    exact (Real.le_sqrt hsum_nonneg (by positivity)).2 hsq
  rw [Real.sqrt_mul (by positivity)] at hsqrt
  simpa [Real.sqrt_eq_rpow, mul_assoc] using hsqrt

/-- Zero detection for the Schatten-2 norm. -/
lemma schattenNorm_two_eq_zero_iff
    {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) :
    schattenNorm A 2 = 0 ↔ A = 0 := by
  rw [schattenNorm_two_eq_frobenius]
  exact norm_eq_zero

/-- The working `2→2` norm is nonnegative. -/
theorem superoperatorNorm_2to2_nonneg
    {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]
    (Φ : MatrixMap dIn dOut ℂ) :
    0 ≤ superoperatorNorm_2to2 Φ := by
  unfold superoperatorNorm_2to2
  refine Real.sSup_nonneg ?_
  intro r hr
  rcases hr with ⟨X, _, rfl⟩
  exact div_nonneg (schattenNorm_nonneg _ _) (schattenNorm_nonneg _ _)

/-- The working diamond norm is nonnegative. -/
theorem diamondNorm_nonneg (Φ : MatrixMap d d ℂ) :
    0 ≤ diamondNorm Φ := by
  unfold diamondNorm
  refine Real.sSup_nonneg ?_
  intro r hr
  rcases hr with ⟨X, _, rfl⟩
  exact div_nonneg (Matrix.traceNorm_nonneg _) (Matrix.traceNorm_nonneg _)

/-- The working `2→2` norm vanishes exactly on the zero superoperator. -/
theorem superoperatorNorm_2to2_eq_zero_iff
    {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]
    (Φ : MatrixMap dIn dOut ℂ) :
    superoperatorNorm_2to2 Φ = 0 ↔ Φ = 0 := by
  let S : Set ℝ := { schattenNorm (Φ X) 2 / schattenNorm X 2 |
    (X : Matrix dIn dIn ℂ) (_ : schattenNorm X 2 ≠ 0) }
  have hbound : BddAbove S := by
    let L : Matrix dIn dIn ℂ →L[ℂ] Matrix dOut dOut ℂ := LinearMap.toContinuousLinearMap Φ
    refine ⟨‖L‖, ?_⟩
    rintro r ⟨X, hX, rfl⟩
    have hXpos : 0 < schattenNorm X 2 :=
      lt_of_le_of_ne (schattenNorm_nonneg X 2) hX.symm
    have hle : schattenNorm (Φ X) 2 ≤ ‖L‖ * schattenNorm X 2 := by
      simpa [L, schattenNorm_two_eq_frobenius] using (ContinuousLinearMap.le_opNorm L X)
    exact (div_le_iff₀ hXpos).2 hle
  constructor
  · intro hzero
    apply LinearMap.ext
    intro X
    by_cases hX0 : X = 0
    · simp [hX0]
    · have hXnorm : schattenNorm X 2 ≠ 0 := by
        intro h
        exact hX0 ((schattenNorm_two_eq_zero_iff X).mp h)
      by_contra hPhiX
      have hPhiXnorm : schattenNorm (Φ X) 2 ≠ 0 := by
        intro h
        exact hPhiX ((schattenNorm_two_eq_zero_iff (Φ X)).mp h)
      have hPhiXpos : 0 < schattenNorm (Φ X) 2 :=
        lt_of_le_of_ne (schattenNorm_nonneg (Φ X) 2) hPhiXnorm.symm
      have hratio_mem : schattenNorm (Φ X) 2 / schattenNorm X 2 ∈ S := by
        exact ⟨X, hXnorm, rfl⟩
      have hle := le_csSup hbound hratio_mem
      change schattenNorm (Φ X) 2 / schattenNorm X 2 ≤ superoperatorNorm_2to2 Φ at hle
      rw [hzero] at hle
      have hXpos : 0 < schattenNorm X 2 :=
        lt_of_le_of_ne (schattenNorm_nonneg X 2) hXnorm.symm
      have : 0 < schattenNorm (Φ X) 2 / schattenNorm X 2 := by
        exact div_pos hPhiXpos hXpos
      linarith
  · intro hΦ
    apply le_antisymm
    · unfold superoperatorNorm_2to2
      rw [hΦ]
      apply Real.sSup_le
      · rintro r ⟨X, _, rfl⟩
        simp [schattenNorm_zero (d := dOut) (p := (2 : ℝ)) (by norm_num)]
      · norm_num
    · exact superoperatorNorm_2to2_nonneg Φ

/-- The working diamond norm vanishes exactly on the zero superoperator. -/
theorem diamondNorm_eq_zero_iff (Φ : MatrixMap d d ℂ) :
    diamondNorm Φ = 0 ↔ Φ = 0 := by
  sorry -- [GAP][diamond-zero-iff] need zero detection for the stabilized trace-norm definition

end FrobeniusNorm

/-- The working diamond norm dominates the working `2→2` norm. -/
theorem superoperatorNorm_2to2_le_diamondNorm (Φ : MatrixMap d d ℂ) :
    superoperatorNorm_2to2 Φ ≤ diamondNorm Φ := by
  sorry -- [GAP][diamond-ge-2to2] need the comparison between the stabilized trace norm and the Schatten-2 operator norm

namespace MatrixMap

/-- A CP sandwich around `H` yields the corresponding diamond-norm control on `Φ - H`. -/
theorem cp_sandwich_diamond_bound
    {d : Type*} [Fintype d] [DecidableEq d]
    {Φ H : MatrixMap d d ℂ} {ε : ℝ}
    (hLower : (Φ - (((1 - ε : ℝ) : ℂ) • H)).IsCompletelyPositive)
    (hUpper : ((((1 + ε : ℝ) : ℂ) • H) - Φ).IsCompletelyPositive)
    (hε : 0 ≤ ε) :
    diamondNorm (Φ - H) ≤ ε * diamondNorm H := by
  sorry -- [GAP][cp-order-diamond-bound] need the project-specific CP-sandwich estimate for the working diamond norm

end MatrixMap

/-- The Haar twirl channel has working diamond norm at most `1`. -/
theorem diamondNorm_haarTwirlChannel_le_one (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    diamondNorm (haarTwirlChannel d k) ≤ 1 := by
  sorry -- [GAP][diamond-tp-bound] need the CPTP bound on the working diamond norm for the Haar twirl
