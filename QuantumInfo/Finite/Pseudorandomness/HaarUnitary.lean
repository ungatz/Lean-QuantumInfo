import QuantumInfo.ForMathlib.HermitianMat.Unitary
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.Bounded

/-! # Haar Probability Measure on `𝐔[d]`

This file packages the normalized Haar measure on the finite-dimensional unitary group
`𝐔[d] = Matrix.unitaryGroup d ℂ` in a form convenient for later pseudorandomness files.

## Main declarations

* `haarMeasure_unitaryGroup` — the Haar probability measure on `𝐔[d]`
* `haarMeasure_unitaryGroup_univ` — normalization on `Set.univ`
* `haarMeasure_unitaryGroup_isMulLeftInvariant` — left invariance
* `haarMeasure_unitaryGroup_eq_of_isProbabilityMeasure` — uniqueness among probability Haar measures
-/

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Use the Borel σ-algebra on `𝐔[d]`. This does not infer automatically from the subgroup
structure alone in the current project imports. -/
instance : MeasurableSpace (𝐔[d]) :=
  borel _

instance : BorelSpace (𝐔[d]) :=
  ⟨rfl⟩

/-- The finite-dimensional unitary group is compact as a closed bounded subset of matrix space. -/
instance : CompactSpace (𝐔[d]) := by
  letI : T2Space (Matrix d d ℂ) := inferInstance
  let S : Set (Matrix d d ℂ) := ↑(𝐔[d])
  have hclosed : IsClosed S := by
    have hS : S = {A : Matrix d d ℂ | A * star A = 1} := by
      ext A
      simp [S, Matrix.mem_unitaryGroup_iff]
    rw [hS]
    exact isClosed_eq
      (Continuous.mul continuous_id (Continuous.star continuous_id))
      continuous_const
  have hbounded : Bornology.IsBounded S := by
    by_cases hnt : Nontrivial (Matrix d d ℂ)
    · letI := hnt
      rw [Metric.isBounded_iff_subset_closedBall 0]
      use 1
      intro A hA
      simp only [Metric.mem_closedBall, dist_zero_right]
      have hnorm : ‖A‖ = (1 : ℝ) := CStarRing.norm_of_mem_unitary hA
      rw [hnorm]
    · letI : Subsingleton (Matrix d d ℂ) := not_nontrivial_iff_subsingleton.mp hnt
      rw [Metric.isBounded_iff_subset_closedBall 0]
      use 0
      intro A hA
      simp [Subsingleton.elim A 0]
  have hcompact : IsCompact (closure S) := hbounded.isCompact_closure
  have hcompact' : IsCompact S := by
    simpa [hclosed.closure_eq] using hcompact
  exact isCompact_iff_compactSpace.mp (by simpa [S] using hcompact')

instance : LocallyCompactSpace (𝐔[d]) := by
  infer_instance

/-- The Haar probability measure on the unitary group `𝐔[d]`, normalized so that `univ`
has total mass `1`. -/
noncomputable def haarMeasure_unitaryGroup (d : Type*) [Fintype d] [DecidableEq d] :
    MeasureTheory.Measure (𝐔[d]) :=
  MeasureTheory.Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (𝐔[d]))

/-- The chosen Haar measure on `𝐔[d]` is normalized to have total mass `1`. -/
theorem haarMeasure_unitaryGroup_univ :
    haarMeasure_unitaryGroup d Set.univ = 1 := by
  simpa [haarMeasure_unitaryGroup, TopologicalSpace.PositiveCompacts.coe_top] using
    (MeasureTheory.Measure.haarMeasure_self
      (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (𝐔[d]))))

instance : MeasureTheory.IsProbabilityMeasure (haarMeasure_unitaryGroup d) where
  measure_univ := haarMeasure_unitaryGroup_univ (d := d)

instance : (haarMeasure_unitaryGroup d).IsHaarMeasure := by
  dsimp [haarMeasure_unitaryGroup]
  infer_instance

/-- The chosen Haar measure on `𝐔[d]` is left invariant. -/
theorem haarMeasure_unitaryGroup_isMulLeftInvariant :
    (haarMeasure_unitaryGroup d).IsMulLeftInvariant := by
  dsimp [haarMeasure_unitaryGroup]
  infer_instance

/-- Uniqueness of the normalized Haar probability measure on `𝐔[d]`. -/
theorem haarMeasure_unitaryGroup_eq_of_isProbabilityMeasure
    (μ : MeasureTheory.Measure (𝐔[d])) [μ.IsHaarMeasure] [MeasureTheory.IsProbabilityMeasure μ] :
    μ = haarMeasure_unitaryGroup d := by
  apply MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure
