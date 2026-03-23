/-
Copyright (c) 2026 Sanad. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Sanad
-/
import QuantumInfo.Finite.Pseudorandomness.HaarUnitary
import QuantumInfo.Finite.Pseudorandomness.TensorPower
import QuantumInfo.Finite.CPTPMap.Unbundled
import QuantumInfo.ForMathlib.HermitianMat.Inner
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # k-fold Twirl Channels

This file defines the k-fold twirl channel at the unbundled `MatrixMap` level.
The construction is matrix-centric: we define the fixed-unitary conjugation
superoperator, then integrate its Choi matrix against a measure on `𝐔[d]`.

## Main definitions

* `unitaryConjMatrixMap` — conjugation by a fixed unitary as a `MatrixMap`
* `kFoldConjMatrixMap` — conjugation by `U^{⊗k}`
* `kFoldTwirlChannel` — the k-fold twirl channel for an arbitrary measure on `𝐔[d]`
* `haarTwirlChannel` — the specialization to the Haar probability measure
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

open MeasureTheory
open ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Conjugation by a fixed unitary as an unbundled `MatrixMap`. -/
def unitaryConjMatrixMap {n : Type*} [Fintype n] [DecidableEq n] (U : 𝐔[n]) : MatrixMap n n ℂ :=
  MatrixMap.conj U.val

/-- Conjugation by the tensor-power unitary `U^{⊗k}`. -/
def kFoldConjMatrixMap (U : 𝐔[d]) (k : ℕ) : MatrixMap (Fin k → d) (Fin k → d) ℂ :=
  unitaryConjMatrixMap (unitaryTensorPower k U)

/-- Conjugation by a unitary is completely positive. -/
theorem unitaryConjMatrixMap_isCompletelyPositive {n : Type*} [Fintype n] [DecidableEq n]
    (U : 𝐔[n]) :
    (unitaryConjMatrixMap U).IsCompletelyPositive := by
  simpa [unitaryConjMatrixMap] using MatrixMap.conj_isCompletelyPositive U.val

/-- Conjugation by a unitary is trace preserving. -/
theorem unitaryConjMatrixMap_isTracePreserving {n : Type*} [Fintype n] [DecidableEq n]
    (U : 𝐔[n]) :
    (unitaryConjMatrixMap U).IsTracePreserving := by
  intro X
  simp [unitaryConjMatrixMap, Matrix.trace_mul_cycle U.val, ← Matrix.star_eq_conjTranspose]

/-- Conjugation by `U^{⊗k}` is completely positive. -/
theorem kFoldConjMatrixMap_isCompletelyPositive (U : 𝐔[d]) (k : ℕ) :
    (kFoldConjMatrixMap U k).IsCompletelyPositive := by
  simpa [kFoldConjMatrixMap] using
    unitaryConjMatrixMap_isCompletelyPositive (n := Fin k → d) (unitaryTensorPower k U)

/-- Conjugation by `U^{⊗k}` is trace preserving. -/
theorem kFoldConjMatrixMap_isTracePreserving (U : 𝐔[d]) (k : ℕ) :
    (kFoldConjMatrixMap U k).IsTracePreserving := by
  simpa [kFoldConjMatrixMap] using
    unitaryConjMatrixMap_isTracePreserving (n := Fin k → d) (unitaryTensorPower k U)

/-- The k-fold twirl channel, defined by integrating the Choi matrix of
`U ↦ conj(U^{⊗k})` against a measure on the unitary group. -/
def kFoldTwirlChannel (μ : Measure 𝐔[d]) (k : ℕ) : MatrixMap (Fin k → d) (Fin k → d) ℂ :=
  MatrixMap.of_choi_matrix (∫ U, (kFoldConjMatrixMap (d := d) U k).choi_matrix ∂μ)

/-- The Haar k-fold twirl channel on `𝐔[d]`. -/
def haarTwirlChannel (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    MatrixMap (Fin k → d) (Fin k → d) ℂ :=
  kFoldTwirlChannel (d := d) (haarMeasure_unitaryGroup d) k

/-- The Choi matrix of the k-fold twirl channel is the Bochner integral of the
Choi matrices of the fixed-unitary conjugation maps. -/
@[simp]
theorem kFoldTwirlChannel_choi_matrix (μ : Measure 𝐔[d]) (k : ℕ) :
    (kFoldTwirlChannel (d := d) μ k).choi_matrix =
      ∫ U, (kFoldConjMatrixMap (d := d) U k).choi_matrix ∂μ := by
  simp [kFoldTwirlChannel]

/-- The Choi matrix of the Haar twirl channel. -/
@[simp]
theorem haarTwirlChannel_choi_matrix (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    (haarTwirlChannel d k).choi_matrix =
      ∫ U, (kFoldConjMatrixMap (d := d) U k).choi_matrix ∂haarMeasure_unitaryGroup d := by
  simp [haarTwirlChannel]

lemma continuous_unitaryTensorPower_val (k : ℕ) :
    Continuous (fun U : 𝐔[d] =>
      ((unitaryTensorPower k U).val : Matrix (Fin k → d) (Fin k → d) ℂ)) := by
  classical
  rw [show (fun U : 𝐔[d] =>
      ((unitaryTensorPower k U).val : Matrix (Fin k → d) (Fin k → d) ℂ)) =
      fun U => (U.val.tensorPower k : Matrix (Fin k → d) (Fin k → d) ℂ) by
        funext U
        simp [unitaryTensorPower_val]]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun a : 𝐔[d] => ∏ l, (a.val) (i l) (j l))
  apply continuous_finset_prod Finset.univ
  intro l _
  have h1 : Continuous (fun a : 𝐔[d] => a.val (i l)) :=
    (continuous_apply (i := i l)).comp continuous_subtype_val
  exact (continuous_apply (i := j l)).comp h1

lemma continuous_kFoldConj_choi (k : ℕ) :
    Continuous (fun U : 𝐔[d] => (kFoldConjMatrixMap (d := d) U k).choi_matrix) := by
  classical
  let g : 𝐔[d] → Matrix (Fin k → d) (Fin k → d) ℂ :=
    fun U => ((unitaryTensorPower k U).val : _)
  have hg : Continuous g := continuous_unitaryTensorPower_val (d := d) k
  have hchoi : ∀ U : 𝐔[d], (kFoldConjMatrixMap (d := d) U k).choi_matrix =
      Matrix.vecMulVec
        (fun x : (Fin k → d) × (Fin k → d) => g U x.1 x.2)
        (fun x => star (g U x.1 x.2)) := by
    intro U
    simpa [kFoldConjMatrixMap, unitaryConjMatrixMap, g, MatrixMap.conj, MatrixMap.of_kraus] using
      (MatrixMap.choi_of_kraus_R
        (κ := Unit)
        (K := fun _ : Unit => ((unitaryTensorPower k U).val : Matrix _ _ ℂ)))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have hgi1 : Continuous (fun U : 𝐔[d] => g U i.1) :=
    (continuous_apply (i := i.1)).comp hg
  have hi : Continuous (fun U : 𝐔[d] => g U i.1 i.2) :=
    (continuous_apply (i := i.2)).comp hgi1
  have hgj1 : Continuous (fun U : 𝐔[d] => g U j.1) :=
    (continuous_apply (i := j.1)).comp hg
  have hj0 : Continuous (fun U : 𝐔[d] => g U j.1 j.2) :=
    (continuous_apply (i := j.2)).comp hgj1
  have hj : Continuous (fun U : 𝐔[d] => star (g U j.1 j.2)) :=
    continuous_star.comp hj0
  simpa [hchoi, Matrix.vecMulVec] using hi.mul hj

lemma integrable_kFoldConj_choi (μ : Measure 𝐔[d]) [IsProbabilityMeasure μ] (k : ℕ) :
    Integrable (fun U : 𝐔[d] => (kFoldConjMatrixMap (d := d) U k).choi_matrix) μ := by
  rw [← MeasureTheory.integrableOn_univ]
  simpa using
    (ContinuousOn.integrableOn_compact
      (μ := μ)
      (K := Set.univ)
      (isCompact_univ : IsCompact (Set.univ : Set (𝐔[d])))
      (continuous_kFoldConj_choi (d := d) k).continuousOn)

/-- The `k`-fold twirl of a probability measure on the unitary group is completely positive. -/
theorem kFoldTwirlChannel_isCompletelyPositive (μ : Measure 𝐔[d]) [IsProbabilityMeasure μ] (k : ℕ) :
    (kFoldTwirlChannel (d := d) μ k).IsCompletelyPositive := by
  rw [MatrixMap.choi_PSD_iff_CP_map]
  rw [kFoldTwirlChannel_choi_matrix]
  let s : Set (Matrix ((Fin k → d) × (Fin k → d)) ((Fin k → d) × (Fin k → d)) ℂ) :=
    {A | A.PosSemidef}
  have hs_convex : Convex ℝ s := by
    intro A hA B hB a b ha hb hab
    have hA' : A.PosSemidef := by simpa [s] using hA
    have hB' : B.PosSemidef := by simpa [s] using hB
    have hA'' : (a • A).PosSemidef := Matrix.PosSemidef.rsmul hA' ha
    have hB'' : (b • B).PosSemidef := Matrix.PosSemidef.rsmul hB' hb
    simpa [s] using Matrix.PosSemidef.add hA'' hB''
  have hs_closed : IsClosed s := by
    simpa [s] using
      (HermitianMat.Matrix.PosSemiDef_isClosed :
        IsClosed {A : Matrix ((Fin k → d) × (Fin k → d)) ((Fin k → d) × (Fin k → d)) ℂ |
          A.PosSemidef})
  have hmem : ∀ᵐ U : 𝐔[d] ∂μ, (kFoldConjMatrixMap (d := d) U k).choi_matrix ∈ s := by
    filter_upwards with U
    simpa [s] using
      (MatrixMap.choi_PSD_iff_CP_map (kFoldConjMatrixMap (d := d) U k)).1
        (kFoldConjMatrixMap_isCompletelyPositive (d := d) U k)
  simpa [s] using
    (Convex.integral_mem hs_convex hs_closed hmem
      (integrable_kFoldConj_choi (d := d) (μ := μ) k))

/-- The `k`-fold twirl of a probability measure on the unitary group is trace preserving. -/
theorem kFoldTwirlChannel_isTracePreserving (μ : Measure 𝐔[d]) [IsProbabilityMeasure μ] (k : ℕ) :
    (kFoldTwirlChannel (d := d) μ k).IsTracePreserving := by
  rw [MatrixMap.IsTracePreserving_iff_trace_choi]
  rw [kFoldTwirlChannel_choi_matrix]
  let L :
      Matrix (((Fin k → d) × (Fin k → d))) (((Fin k → d) × (Fin k → d))) ℂ →ₗ[ℂ]
        Matrix (Fin k → d) (Fin k → d) ℂ :=
    { toFun := Matrix.traceLeft
      map_add' := by
        intro A B
        exact Matrix.traceLeft_add
      map_smul' := by
        intro c A
        exact Matrix.traceLeft_smul c }
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hint := integrable_kFoldConj_choi (d := d) (μ := μ) k
  calc
    (∫ U, (kFoldConjMatrixMap (d := d) U k).choi_matrix ∂μ).traceLeft
        = ∫ U, ((kFoldConjMatrixMap (d := d) U k).choi_matrix).traceLeft ∂μ := by
            simpa [L] using
              (ContinuousLinearMap.integral_comp_comm
                (L := { toLinearMap := L, cont := hL }) hint).symm
    _ = ∫ U, (1 : Matrix (Fin k → d) (Fin k → d) ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with U
      exact
        (MatrixMap.IsTracePreserving_iff_trace_choi (kFoldConjMatrixMap (d := d) U k)).1
          (kFoldConjMatrixMap_isTracePreserving (d := d) U k)
    _ = 1 := by
      simpa using
        (MeasureTheory.integral_eq_const
          (μ := μ)
          (c := (1 : Matrix (Fin k → d) (Fin k → d) ℂ))
          (ae_of_all _ fun _ => rfl))

/-- The Haar `k`-fold twirl channel is completely positive. -/
theorem haarTwirlChannel_isCompletelyPositive (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    (haarTwirlChannel d k).IsCompletelyPositive := by
  simpa [haarTwirlChannel] using
    kFoldTwirlChannel_isCompletelyPositive (d := d) (μ := haarMeasure_unitaryGroup d) k

/-- The Haar `k`-fold twirl channel is trace preserving. -/
theorem haarTwirlChannel_isTracePreserving (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    (haarTwirlChannel d k).IsTracePreserving := by
  simpa [haarTwirlChannel] using
    kFoldTwirlChannel_isTracePreserving (d := d) (μ := haarMeasure_unitaryGroup d) k
