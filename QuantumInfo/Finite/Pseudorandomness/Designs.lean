import QuantumInfo.Finite.Pseudorandomness.Norms
import QuantumInfo.Finite.Ensemble
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! # State And Unitary Designs

This file packages two layers of design notions:

* finite pure-state and finite unitary ensembles built on the existing
  `PEnsemble` / `Distribution.RandVar` APIs;
* matrix-level approximate unitary design notions for measures on `𝐔[d]`.

For state designs, the reference `k`-th moment is defined using the normalized
measure induced on the unit sphere of `EuclideanSpace ℂ d`.
-/

open MeasureTheory
open ComplexOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {k : ℕ}

namespace MatrixMap

/-- The completely positive order on unbundled matrix maps: `Φ ≤ Ψ` means
`Ψ - Φ` is completely positive. -/
def CPOrder
    {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]
    (Φ Ψ : MatrixMap dIn dOut ℂ) : Prop :=
  (Ψ - Φ).IsCompletelyPositive

namespace CPOrder

theorem refl
    {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]
    (Φ : MatrixMap dIn dOut ℂ) :
    CPOrder Φ Φ := by
  unfold CPOrder
  simpa using MatrixMap.IsCompletelyPositive.zero dIn dOut (R := ℂ)

theorem antisymm
    {dIn dOut : Type*} [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]
    {Φ Ψ : MatrixMap dIn dOut ℂ}
    (h₁ : CPOrder Φ Ψ) (h₂ : CPOrder Ψ Φ) :
    Φ = Ψ := by
  unfold CPOrder at h₁ h₂
  have hΨΦ : (Ψ - Φ).choi_matrix.PosSemidef :=
    (MatrixMap.choi_PSD_iff_CP_map (Ψ - Φ)).1 h₁
  have hΦΨ : (Φ - Ψ).choi_matrix.PosSemidef :=
    (MatrixMap.choi_PSD_iff_CP_map (Φ - Ψ)).1 h₂
  have hchoi_neg : (Φ - Ψ).choi_matrix = -(Ψ - Φ).choi_matrix := by
    ext i j
    simp [MatrixMap.choi_matrix, sub_eq_add_neg]
  have hneg : (-(Ψ - Φ).choi_matrix).PosSemidef := by
    rw [← hchoi_neg]
    exact hΦΨ
  have hzero : (Ψ - Φ).choi_matrix = 0 :=
    (Matrix.PosSemidef.zero_posSemidef_neg_posSemidef_iff
      (A := (Ψ - Φ).choi_matrix)).1 ⟨hΨΦ, hneg⟩
  have hsub : Ψ - Φ = 0 := MatrixMap.choi_matrix_inj hzero
  exact (sub_eq_zero.mp hsub).symm

end CPOrder
end MatrixMap

/-! ## State Ensembles -/

/-- A finite pure-state ensemble, built on the existing `PEnsemble` API. -/
structure StateEnsemble (d : Type*) [Fintype d] [DecidableEq d] where
  ι : Type*
  instFintype : Fintype ι
  data : PEnsemble d ι

attribute [instance] StateEnsemble.instFintype

namespace StateEnsemble

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Access the pure states of a finite state ensemble. -/
abbrev states (E : StateEnsemble d) : E.ι → Ket d := E.data.states

/-- Access the probability distribution of a finite state ensemble. -/
abbrev distr (E : StateEnsemble d) : Distribution E.ι := E.data.distr

/-- Wrap an existing `PEnsemble` as a bundled `StateEnsemble`. -/
def ofPEnsemble {α : Type*} [Fintype α] (e : PEnsemble d α) : StateEnsemble d :=
  { ι := α, instFintype := inferInstance, data := e }

/-- The average mixed state of a finite pure-state ensemble. -/
def averageState (E : StateEnsemble d) : MState d :=
  Ensemble.mix (↑E.data : MEnsemble d E.ι)

/-- The `k`-th moment operator of a finite pure-state ensemble. -/
def momentOp (E : StateEnsemble d) (k : ℕ) :
    Matrix (Fin k → d) (Fin k → d) ℂ :=
  Ensemble.pure_average (fun ψ => (MState.pure ψ).m.tensorPower k) E.data

/-- The spectral pure-state ensemble of a mixed state, viewed as a bundled state ensemble. -/
def spectral (ρ : MState d) : StateEnsemble d :=
  { ι := d, instFintype := inferInstance, data := Ensemble.spectral_ensemble ρ }

end StateEnsemble

section StateDesigns

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The unit sphere corresponding to pure states in dimension `d`, expressed in
`EuclideanSpace ℂ d` so the sphere uses the Hilbert-space norm. -/
abbrev KetSphere (d : Type*) [Fintype d] := Metric.sphere (0 : EuclideanSpace ℂ d) 1

/-- View a ket as a point on the unit sphere of `EuclideanSpace ℂ d`. -/
noncomputable def ketToSphere (ψ : Ket d) : KetSphere d := by
  refine ⟨(show EuclideanSpace ℂ d from ψ.vec), ?_⟩
  have hnorm : ‖(show EuclideanSpace ℂ d from ψ.vec)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simpa using congrArg Real.sqrt ψ.normalized'
  simpa [Metric.mem_sphere, dist_eq_norm] using hnorm

/-- View a point on the unit sphere of `EuclideanSpace ℂ d` as a ket. -/
noncomputable def sphereToKet (x : KetSphere d) : Ket d := by
  refine { vec := x.1, normalized' := ?_ }
  have hx : ‖(x : EuclideanSpace ℂ d)‖ = 1 := by simp
  rw [EuclideanSpace.norm_eq] at hx
  have hsq : ∑ i, ‖(x : EuclideanSpace ℂ d) i‖ ^ 2 = 1 := by
    have hnonneg : 0 ≤ ∑ i, ‖(x : EuclideanSpace ℂ d) i‖ ^ 2 := by
      positivity
    nlinarith [Real.sq_sqrt hnonneg, hx]
  simpa using hsq

instance instNonemptyKetSphere : Nonempty (KetSphere d) :=
  ⟨ketToSphere (d := d) default⟩

/-- The normalized reference measure on pure states, obtained from the sphere
measure induced by `volume` on `EuclideanSpace ℂ d`. -/
noncomputable def uniformSphereMeasure : ProbabilityMeasure (KetSphere d) :=
  MeasureTheory.FiniteMeasure.normalize
    (⟨Measure.toSphere (volume : Measure (EuclideanSpace ℂ d)), inferInstance⟩ :
      FiniteMeasure (KetSphere d))

/-- The reference `k`-th moment operator for pure-state designs. -/
noncomputable def haarStateMomentOp (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d] (k : ℕ) :
    Matrix (Fin k → d) (Fin k → d) ℂ :=
  ∫ x : KetSphere d, (MState.pure (sphereToKet x)).m.tensorPower k ∂(uniformSphereMeasure (d := d))

/-- A finite pure-state ensemble is an exact state `k`-design if its `k`-th
moment operator matches the reference sphere moment. -/
def IsStateDesign (E : StateEnsemble d) (k : ℕ) : Prop :=
  E.momentOp k = haarStateMomentOp d k

/-- A finite pure-state ensemble is a state `1`-design if its average state is
the maximally mixed state. -/
def IsState1Design (E : StateEnsemble d) : Prop :=
  E.averageState = MState.uniform

/-- A finite pure-state ensemble is a state `2`-design if it is a state `2`-design
in the exact moment-operator sense. -/
def IsState2Design (E : StateEnsemble d) : Prop :=
  IsStateDesign E 2

/-- A finite pure-state ensemble is an `ε`-approximate state `k`-design if its
moment operator is `ε`-close to the reference moment in Schatten-2 norm. -/
def IsApproxStateDesign (E : StateEnsemble d) (k : ℕ) (ε : ℝ) : Prop :=
  schattenNorm (E.momentOp k - haarStateMomentOp d k) 2 ≤ ε

/-- Exact state designs are `0`-approximate state designs. -/
theorem IsStateDesign_imp_approx_zero {E : StateEnsemble d} {k : ℕ}
    (h : IsStateDesign E k) : IsApproxStateDesign E k 0 := by
  unfold IsApproxStateDesign IsStateDesign at *
  rw [h, sub_self]
  have hp : (0 : ℝ) < 2 := by
    norm_num
  have hzero :
      schattenNorm (0 : Matrix (Fin k → d) (Fin k → d) ℂ) 2 = 0 :=
    schattenNorm_zero (d := Fin k → d) (p := (2 : ℝ)) hp
  rw [hzero]

/-- The spectral ensemble of the maximally mixed state is a state `1`-design. -/
theorem spectral_ensemble_uniform_isState1Design :
    IsState1Design (StateEnsemble.spectral (d := d) (MState.uniform : MState d)) := by
  simp [IsState1Design, StateEnsemble.averageState, StateEnsemble.spectral,
    Ensemble.spectral_ensemble_mix]

end StateDesigns

/-! ## Unitary Ensembles -/

/-- A finite unitary ensemble, built on the existing `Distribution.RandVar` API. -/
structure UnitaryEnsemble (d : Type*) [Fintype d] [DecidableEq d] where
  ι : Type*
  instFintype : Fintype ι
  data : Distribution.RandVar ι (𝐔[d])

attribute [instance] UnitaryEnsemble.instFintype

namespace UnitaryEnsemble

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Access the unitary matrices in a finite unitary ensemble. -/
abbrev unitaries (E : UnitaryEnsemble d) : E.ι → 𝐔[d] := E.data.var

/-- Access the probability distribution of a finite unitary ensemble. -/
abbrev distr (E : UnitaryEnsemble d) : Distribution E.ι := E.data.distr

/-- Wrap an existing random variable valued in `𝐔[d]` as a bundled
`UnitaryEnsemble`. -/
def ofRandVar {α : Type*} [Fintype α] (e : Distribution.RandVar α (𝐔[d])) :
    UnitaryEnsemble d :=
  { ι := α, instFintype := inferInstance, data := e }

/-- The discrete measure on `𝐔[d]` induced by a finite unitary ensemble. -/
def toMeasure (E : UnitaryEnsemble d) : Measure 𝐔[d] :=
  Measure.sum (fun i : E.ι => ENNReal.ofReal (E.distr i : ℝ) • Measure.dirac (E.unitaries i))

/-- The `k`-th moment superoperator of a finite unitary ensemble, viewed through
the existing twirl-channel API. -/
def momentMap (E : UnitaryEnsemble d) (k : ℕ) :
    MatrixMap (Fin k → d) (Fin k → d) ℂ :=
  kFoldTwirlChannel (d := d) E.toMeasure k

/-- The pointwise action of the `k`-th moment superoperator of a finite unitary
ensemble. -/
def momentChannel (E : UnitaryEnsemble d) (k : ℕ)
    (A : Matrix (Fin k → d) (Fin k → d) ℂ) :
    Matrix (Fin k → d) (Fin k → d) ℂ :=
  E.momentMap k A

/-- The Choi matrix of the finite-ensemble moment map is the Choi matrix of the
corresponding discrete twirl measure. -/
@[simp]
theorem momentMap_choi_matrix (E : UnitaryEnsemble d) (k : ℕ) :
    (E.momentMap k).choi_matrix =
      ∫ U, (kFoldConjMatrixMap (d := d) U k).choi_matrix ∂E.toMeasure := by
  simp [momentMap, kFoldTwirlChannel_choi_matrix]

end UnitaryEnsemble

/-- A finite unitary ensemble is an exact unitary `k`-design if its induced
moment map matches the Haar twirl channel. -/
def IsUnitaryDesign (E : UnitaryEnsemble d) (k : ℕ) : Prop :=
  E.momentMap k = haarTwirlChannel d k

/-- A finite unitary ensemble is a unitary `1`-design if it is an exact
unitary `1`-design. -/
def IsUnitary1Design (E : UnitaryEnsemble d) : Prop :=
  IsUnitaryDesign E 1

/-- A finite unitary ensemble is a unitary `2`-design if it is an exact
unitary `2`-design. -/
def IsUnitary2Design (E : UnitaryEnsemble d) : Prop :=
  IsUnitaryDesign E 2

/-- A finite unitary ensemble is an additive `ε`-approximate unitary `k`-design
if its induced moment map is `ε`-close to the Haar twirl in working diamond norm. -/
def IsApproxUnitaryDesign (E : UnitaryEnsemble d) (k : ℕ) (ε : ℝ) : Prop :=
  diamondNorm (E.momentMap k - haarTwirlChannel d k) ≤ ε

/-! ## Approximate Unitary Designs For Measures -/

/-- A measure `μ` is an `ε`-approximate tensor-product expander if its `k`-fold
twirl is within `ε` of the Haar twirl in the superoperator `2→2` norm. -/
def IsTPEDesign (μ : Measure 𝐔[d]) (k : ℕ) (ε : ℝ) : Prop :=
  superoperatorNorm_2to2 (kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k) ≤ ε

/-- A measure `μ` is an additive `ε`-approximate `k`-design if its `k`-fold
twirl is within `ε` of the Haar twirl in the working diamond norm. -/
def IsAdditiveDesign (μ : Measure 𝐔[d]) (k : ℕ) (ε : ℝ) : Prop :=
  diamondNorm (kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k) ≤ ε

/-- A measure `μ` is a multiplicative `ε`-approximate `k`-design if its `k`-fold
twirl is sandwiched between `(1 - ε) Φ_Haar` and `(1 + ε) Φ_Haar` in the
completely positive order. -/
def IsMultiplicativeDesign (μ : Measure 𝐔[d]) (k : ℕ) (ε : ℝ) : Prop :=
  MatrixMap.CPOrder ((((1 - ε : ℝ) : ℂ) • haarTwirlChannel d k))
    (kFoldTwirlChannel (d := d) μ k) ∧
  MatrixMap.CPOrder (kFoldTwirlChannel (d := d) μ k)
    ((((1 + ε : ℝ) : ℂ) • haarTwirlChannel d k))

/-- An exact `k`-design is one whose `k`-fold twirl is exactly the Haar twirl. -/
def IsExactDesign (μ : Measure 𝐔[d]) (k : ℕ) : Prop :=
  kFoldTwirlChannel (d := d) μ k = haarTwirlChannel d k

/-- Exact finite unitary designs are exactly exact designs of their induced
discrete measures. -/
theorem isUnitaryDesign_iff_isExactDesign (E : UnitaryEnsemble d) (k : ℕ) :
    IsUnitaryDesign E k ↔ IsExactDesign (d := d) E.toMeasure k := by
  rfl

/-- Additive approximate finite unitary designs are exactly additive designs of
their induced discrete measures. -/
theorem isApproxUnitaryDesign_iff_isAdditiveDesign
    (E : UnitaryEnsemble d) (k : ℕ) (ε : ℝ) :
    IsApproxUnitaryDesign E k ε ↔ IsAdditiveDesign (d := d) E.toMeasure k ε := by
  rfl

/-- Haar measure is an exact design by definition. -/
theorem haarMeasure_exactDesign (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) :
    IsExactDesign (d := d) (haarMeasure_unitaryGroup d) k := by
  rfl

theorem isMultiplicativeDesign_zero_iff_isExactDesign (μ : Measure 𝐔[d]) (k : ℕ) :
    IsMultiplicativeDesign (d := d) μ k 0 ↔ IsExactDesign (d := d) μ k := by
  let T : MatrixMap (Fin k → d) (Fin k → d) ℂ := kFoldTwirlChannel (d := d) μ k
  let H : MatrixMap (Fin k → d) (Fin k → d) ℂ := haarTwirlChannel d k
  constructor
  · intro h
    rcases h with ⟨hLower, hUpper⟩
    change T = H
    exact MatrixMap.CPOrder.antisymm
      (by simpa [T, H] using hUpper)
      (by simpa [T, H] using hLower)
  · intro h
    have hTH : T = H := by
      simpa [T, H, IsExactDesign] using h
    change MatrixMap.CPOrder ((((1 - 0 : ℝ) : ℂ) • H)) T ∧
        MatrixMap.CPOrder T ((((1 + 0 : ℝ) : ℂ) • H))
    rw [hTH]
    simpa [T, H] using
      And.intro (MatrixMap.CPOrder.refl H) (MatrixMap.CPOrder.refl H)

theorem IsExactDesign.isMultiplicativeDesign_zero
    {μ : Measure 𝐔[d]} {k : ℕ} (h : IsExactDesign (d := d) μ k) :
    IsMultiplicativeDesign (d := d) μ k 0 :=
  (isMultiplicativeDesign_zero_iff_isExactDesign (d := d) μ k).2 h

theorem isAdditiveDesign_zero_iff_isExactDesign (μ : Measure 𝐔[d]) (k : ℕ) :
    IsAdditiveDesign (d := d) μ k 0 ↔ IsExactDesign (d := d) μ k := by
  let Δ : MatrixMap (Fin k → d) (Fin k → d) ℂ :=
    kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k
  constructor
  · intro h
    unfold IsAdditiveDesign at h
    change diamondNorm Δ ≤ 0 at h
    have hzero : diamondNorm Δ = 0 :=
      le_antisymm h (diamondNorm_nonneg Δ)
    exact sub_eq_zero.mp ((diamondNorm_eq_zero_iff Δ).mp hzero)
  · intro h
    unfold IsAdditiveDesign
    change diamondNorm Δ ≤ 0
    have hzero : diamondNorm Δ = 0 := by
      apply (diamondNorm_eq_zero_iff Δ).mpr
      exact sub_eq_zero.mpr h
    simp [hzero]

theorem IsExactDesign.isAdditiveDesign_zero
    {μ : Measure 𝐔[d]} {k : ℕ} (h : IsExactDesign (d := d) μ k) :
    IsAdditiveDesign (d := d) μ k 0 :=
  (isAdditiveDesign_zero_iff_isExactDesign (d := d) μ k).2 h

theorem isTPEDesign_zero_iff_isExactDesign (μ : Measure 𝐔[d]) (k : ℕ) :
    IsTPEDesign (d := d) μ k 0 ↔ IsExactDesign (d := d) μ k := by
  let Δ : MatrixMap (Fin k → d) (Fin k → d) ℂ :=
    kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k
  constructor
  · intro h
    unfold IsTPEDesign at h
    change superoperatorNorm_2to2 Δ ≤ 0 at h
    have hzero : superoperatorNorm_2to2 Δ = 0 :=
      le_antisymm h (superoperatorNorm_2to2_nonneg Δ)
    exact sub_eq_zero.mp ((superoperatorNorm_2to2_eq_zero_iff Δ).mp hzero)
  · intro h
    unfold IsTPEDesign
    change superoperatorNorm_2to2 Δ ≤ 0
    have hzero : superoperatorNorm_2to2 Δ = 0 := by
      apply (superoperatorNorm_2to2_eq_zero_iff Δ).mpr
      exact sub_eq_zero.mpr h
    simp [hzero]

theorem IsExactDesign.isTPEDesign_zero
    {μ : Measure 𝐔[d]} {k : ℕ} (h : IsExactDesign (d := d) μ k) :
    IsTPEDesign (d := d) μ k 0 :=
  (isTPEDesign_zero_iff_isExactDesign (d := d) μ k).2 h

theorem IsAdditiveDesign.isTPEDesign
    {μ : Measure 𝐔[d]} {k : ℕ} {ε : ℝ}
    (h : IsAdditiveDesign (d := d) μ k ε) :
    IsTPEDesign (d := d) μ k ε := by
  change diamondNorm (kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k) ≤ ε at h
  change superoperatorNorm_2to2 (kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k) ≤ ε
  exact le_trans
    (superoperatorNorm_2to2_le_diamondNorm
      (kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k))
    h

theorem IsMultiplicativeDesign.isAdditiveDesign
    {μ : Measure 𝐔[d]} {k : ℕ} {ε : ℝ}
    (h : IsMultiplicativeDesign (d := d) μ k ε) (hε : 0 ≤ ε) :
    IsAdditiveDesign (d := d) μ k ε := by
  rcases h with ⟨hLower, hUpper⟩
  let T : MatrixMap (Fin k → d) (Fin k → d) ℂ := kFoldTwirlChannel (d := d) μ k
  let H : MatrixMap (Fin k → d) (Fin k → d) ℂ := haarTwirlChannel d k
  have hbound1 : diamondNorm (T - H) ≤ ε * diamondNorm H := by
    have hLower' : (T - (((1 - ε : ℝ) : ℂ) • H)).IsCompletelyPositive := by
      simpa [T, H, MatrixMap.CPOrder] using hLower
    have hUpper' : ((((1 + ε : ℝ) : ℂ) • H) - T).IsCompletelyPositive := by
      simpa [T, H, MatrixMap.CPOrder] using hUpper
    exact MatrixMap.cp_sandwich_diamond_bound hLower' hUpper' hε
  have hbound2 : diamondNorm H ≤ 1 := diamondNorm_haarTwirlChannel_le_one d k
  change diamondNorm (kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k) ≤ ε
  calc
    diamondNorm (kFoldTwirlChannel (d := d) μ k - haarTwirlChannel d k) = diamondNorm (T - H) := by
      rfl
    _ ≤ ε * diamondNorm H := hbound1
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hbound2 hε
    _ = ε := by ring
