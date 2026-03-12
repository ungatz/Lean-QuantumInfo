/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-!
Quantities of quantum _relative entropy_, namely the (standard) quantum relative
entropy, and generalizations such as sandwiched Rényi relative entropy.
-/

noncomputable section

variable {d d₁ d₂ d₃ m n : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype m] [Fintype n]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq m] [DecidableEq n]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}


open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix

/-
The operator norm of a matrix is the operator norm of the linear map it represents, with respect to the Euclidean norm.
-/
/-- The operator norm of a matrix, with respect to the Euclidean norm (l2 norm) on the domain and codomain. -/
noncomputable def Matrix.opNorm [RCLike 𝕜] (A : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-
An isometry preserves the Euclidean norm.
-/
theorem Matrix.isometry_preserves_norm (A : Matrix n m 𝕜) (hA : A.Isometry) (x : EuclideanSpace 𝕜 m) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  rw [ ← sq_eq_sq₀ ( by positivity ) ( by positivity ), Matrix.Isometry ] at *;
  simp [ EuclideanSpace.norm_eq]
  have h_inner : ∀ x y : EuclideanSpace 𝕜 m, inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x y := by
    intro x y
    have h_inner_eq : inner 𝕜 (toEuclideanLin A x) (toEuclideanLin A y) = inner 𝕜 x (toEuclideanLin A.conjTranspose (toEuclideanLin A y)) := by
      simp [ Matrix.toEuclideanLin, inner ];
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, ];
      simp [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
      exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
    simp_all [ Matrix.toEuclideanLin];
  convert congr_arg Real.sqrt ( congr_arg ( fun z => ‖z‖ ) ( h_inner x x ) ) using 1;
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ];
  · simp [ EuclideanSpace.norm_eq, inner_self_eq_norm_sq_to_K ]

/-
The operator norm of an isometry is 1 (assuming the domain is non-empty).
-/
theorem Matrix.opNorm_isometry [Nonempty m] (A : Matrix n m 𝕜) (hA : A.Isometry) : Matrix.opNorm A = 1 := by
  have h_opNorm : ∀ x : EuclideanSpace 𝕜 m, ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
    convert Matrix.isometry_preserves_norm A hA;
  refine' le_antisymm ( csInf_le _ _ ) ( le_csInf _ _ );
  · exact ⟨ 0, fun c hc => hc.1 ⟩;
  · aesop;
  · exact ⟨ 1, ⟨zero_le_one, fun x => le_of_eq (by simp [h_opNorm])⟩ ⟩;
  · norm_num +zetaDelta at *;
    intro b hb h; specialize h ( EuclideanSpace.single ( Classical.arbitrary m ) 1 ) ; aesop;

variable (d₁ d₂) in
/-- The matrix representation of the map $v \mapsto v \otimes \sum_k |k\rangle|k\rangle$.
    The output index is `(d1 \times d2) \times d2`. -/
def map_to_tensor_MES : Matrix ((d₁ × d₂) × d₂) d₁ ℂ :=
  Matrix.of fun ((i, j), k) l => if i = l ∧ j = k then 1 else 0

theorem map_to_tensor_MES_prop (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (map_to_tensor_MES d₁ d₂).conjTranspose * (Matrix.kronecker A (1 : Matrix d₂ d₂ ℂ)) * (map_to_tensor_MES d₁ d₂) =
    A.traceRight := by
  ext i j; simp [map_to_tensor_MES, Matrix.mul_apply]
  simp [ Finset.sum_ite, Matrix.one_apply]
  rw [ Finset.sum_sigma' ];
  rw [ Finset.sum_congr rfl (g := fun x => A ( i, x.1.2 ) ( j, x.1.2 ))]
  · apply Finset.sum_bij (fun x _ => x.1.2)
    · simp
    · aesop
    · simp
    · simp
  · aesop

/-- The isometry V_rho from the paper. -/
noncomputable def V_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix ((dA × dB) × dB) dA ℂ :=
  let ρA_inv_sqrt := ρAB.traceRight⁻¹.sqrt
  let ρAB_sqrt := ρAB.sqrt
  let I_B := (1 : Matrix dB dB ℂ)
  let term1 := ρAB_sqrt.mat ⊗ₖ I_B
  let term2 := map_to_tensor_MES dA dB
  term1 * term2 * ρA_inv_sqrt.mat

open scoped MatrixOrder ComplexOrder

/-- The isometry V_sigma from the paper. -/
noncomputable def V_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dB × (dB × dC)) dC ℂ :=
  (V_rho (σBC.reindex (Equiv.prodComm dB dC))).reindex
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))
    (Equiv.refl _)

/--
V_rho^H * V_rho simplifies to sandwiching the traceRight by the inverse square root.
-/
lemma V_rho_conj_mul_self_eq (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    let ρA := ρAB.traceRight
    let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
    (V_rho ρAB)ᴴ * (V_rho ρAB) = ρA_inv_sqrt * ρAB.traceRight.mat * ρA_inv_sqrt := by
  -- By definition of $V_rho$, we can write out the product $V_rho^H * V_rho$.
  simp [V_rho];
  simp [ ← Matrix.mul_assoc ];
  have h_simp : (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ))ᴴ * (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ)) = Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (ρAB : Matrix (dA × dB) (dA × dB) ℂ) (1 : Matrix dB dB ℂ) := by
    have h_simp : (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)ᴴ * (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ) = ρAB := by
      convert ρAB.sqrt_sq ( show 0 ≤ ρAB from ?_ ) using 1;
      · simp [ HermitianMat.sqrt ];
      · have := hρ.2;
        constructor;
        · simp [Matrix.IsHermitian]
        · intro x; by_cases hx : x = 0 <;> simp_all
          exact le_of_lt ( this x hx );
    ext ⟨ i, j ⟩ ⟨ k, l ⟩
    simp [ ← h_simp, Matrix.mul_apply ]
    ring_nf
    by_cases hij : j = l
    · simp [ hij, Matrix.one_apply ]
      simp [← Finset.sum_filter]
      refine' Finset.sum_bij ( fun x _ => x.1 ) _ _ _ _ <;> simp
      intro a b
      exact Or.inl ( by simpa using congr_fun ( congr_fun ( ρAB.sqrt.2 ) i ) ( a, b ) )
    · simp [ hij, Matrix.one_apply ]
      exact Finset.sum_eq_zero (by aesop)
  simp_all [ mul_assoc, Matrix.mul_assoc ];
  simp [ ← Matrix.mul_assoc, ← map_to_tensor_MES_prop ]

/--
The partial trace (left) of a positive definite matrix is positive definite.
-/
lemma PosDef_traceRight [Nonempty dB] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceRight.mat.PosDef := by
  have h_trace_right_pos_def : ∀ (x : EuclideanSpace ℂ dA), x ≠ 0 → 0 < ∑ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
    intro x hx_ne_zero
    have h_inner_pos : ∀ k : dB, 0 ≤ (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) := by
      have := hA.2;
      intro k
      specialize this ( fun i => if h : i.2 = k then x i.1 else 0 )
      simp_all only [ne_eq, dite_eq_ite, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.mat_apply, mul_ite, mul_zero, HermitianMat.val_eq_coe, Matrix.submatrix_apply]
      convert this ( show ( fun i : dA × dB => if i.2 = k then x i.1 else 0 ) ≠ 0 from fun h => hx_ne_zero <| by ext i; simpa using congr_fun h ( i, k ) ) |> le_of_lt using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i : dA => ( i, k ) ) Finset.univ ) ) ] <;> simp [ Finset.sum_image, Finset.sum_ite ];
      · refine' Finset.sum_congr rfl fun i hi => _;
        refine' congr_arg _ ( Finset.sum_bij ( fun j _ => ( j, k ) ) _ _ _ _ ) <;> simp
      · exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm;
    obtain ⟨k, hk⟩ : ∃ k : dB, (star x) ⬝ᵥ (Matrix.mulVec (A.val.submatrix (fun i => (i, k)) (fun i => (i, k))) x) > 0 := by
      have := hA.2 ( fun i => x i.1 * ( if i.2 = Classical.arbitrary dB then 1 else 0 ) )
      simp_all only [ne_eq, dotProduct, Pi.star_apply, RCLike.star_def, Matrix.mulVec,
        HermitianMat.val_eq_coe, Matrix.submatrix_apply, HermitianMat.mat_apply, mul_ite, mul_one, mul_zero]
      contrapose! this
      simp_all only [ne_eq, funext_iff, Pi.zero_apply, ite_eq_right_iff, Prod.forall, forall_eq,
        not_forall, Finset.sum_ite, Finset.sum_const_zero, add_zero] ;
      refine' ⟨ Function.ne_iff.mp hx_ne_zero, _ ⟩;
      convert this ( Classical.arbitrary dB ) using 1;
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.univ.image fun i : dA => ( i, Classical.arbitrary dB ) ) ) ]
      · simp only [Finset.coe_univ, Prod.mk.injEq, and_true, implies_true, Set.injOn_of_eq_iff_eq,
          Finset.sum_image, ↓reduceIte, gt_iff_lt]
        congr! 3;
        refine' Finset.sum_bij ( fun y hy => y.1 ) _ _ _ _ <;> simp
      · simp only [Finset.mem_univ, Finset.mem_image, true_and, not_exists, ne_eq, mul_eq_zero,
          map_eq_zero, ite_eq_right_iff, forall_const, Prod.forall, Prod.mk.injEq, not_and, forall_eq]
        exact fun a b hb => Or.inl fun h => False.elim <| hb <| h.symm ▸ rfl
    exact lt_of_lt_of_le hk ( Finset.single_le_sum ( fun k _ => h_inner_pos k ) ( Finset.mem_univ k ) );
  refine' ⟨A.traceRight.2, fun x hx => _ ⟩;
  · convert h_trace_right_pos_def x hx using 1;
    unfold HermitianMat.traceRight
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, HermitianMat.mat_mk, HermitianMat.val_eq_coe]
    simp only [Matrix.mulVec, dotProduct, mul_comm, Matrix.submatrix_apply, HermitianMat.mat_apply];
    simp only [Matrix.traceRight, HermitianMat.mat_apply, Matrix.of_apply, mul_comm, Finset.mul_sum]
    rw [Finset.sum_comm_cycle]

lemma PosDef_traceLeft [Nonempty dA] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceLeft.mat.PosDef := by
  exact PosDef_traceRight (A.reindex (Equiv.prodComm _ _)) (hA.reindex _)

/--
V_rho is an isometry.
-/
theorem V_rho_isometry [Nonempty dB] (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    (V_rho ρAB)ᴴ * (V_rho ρAB) = 1 := by
  -- Since ρA is positive definite, we can use the fact that ρA_inv_sqrt * ρA * ρA_inv_sqrt = I.
  have h_pos_def : (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) * (ρAB.traceRight : Matrix dA dA ℂ) * (ρAB.traceRight⁻¹.sqrt : Matrix dA dA ℂ) = 1 := by
    convert HermitianMat.sqrt_inv_mul_self_mul_sqrt_inv_eq_one _;
    exact PosDef_traceRight _ hρ
  rw [← h_pos_def]
  exact V_rho_conj_mul_self_eq ρAB hρ

/--
V_sigma is an isometry.
-/
theorem V_sigma_isometry [Nonempty dB] (σBC : HermitianMat (dB × dC) ℂ) (hσ : σBC.mat.PosDef) :
    (V_sigma σBC).conjTranspose * (V_sigma σBC) = 1 := by
  simp [V_sigma]
  exact V_rho_isometry _ (hσ.reindex _)

/-
Definition of W_mat with correct reindexing.
-/
open HermitianMat
open scoped MatrixOrder

variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC]

/-- The operator W from the paper, defined as a matrix product. -/
noncomputable def W_mat (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) : Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ :=
  let ρA := ρAB.traceRight
  let σC := σBC.traceLeft
  let ρAB_sqrt := (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)
  let σC_inv_sqrt := (σC⁻¹.sqrt : Matrix dC dC ℂ)
  let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
  let σBC_sqrt := (σBC.sqrt : Matrix (dB × dC) (dB × dC) ℂ)

  let term1 := ρAB_sqrt ⊗ₖ σC_inv_sqrt
  let term2 := ρA_inv_sqrt ⊗ₖ σBC_sqrt
  let term2_reindexed := term2.reindex (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm

  term1 * term2_reindexed

/--
The operator norm of a matrix product is at most the product of the operator norms.
-/
theorem Matrix.opNorm_mul_le {l m n 𝕜 : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
  have h_opNorm_mul_le : ∀ (A : Matrix l m 𝕜) (B : Matrix m n 𝕜), Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
    intro A B
    have h_comp : Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
      ext; simp [toEuclideanLin]
    convert ContinuousLinearMap.opNorm_comp_le ( Matrix.toEuclideanLin A |> LinearMap.toContinuousLinearMap ) ( Matrix.toEuclideanLin B |> LinearMap.toContinuousLinearMap ) using 1;
    unfold Matrix.opNorm;
    exact congr_arg _ ( by aesop );
  exact h_opNorm_mul_le A B

theorem Matrix.opNorm_reindex_proven {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (e : m ≃ l) (f : n ≃ p) (A : Matrix m n 𝕜) :
    Matrix.opNorm (A.reindex e f) = Matrix.opNorm A := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, fun c hc => hc.1 ⟩;
    · refine' ⟨ norm_nonneg _, fun x => _ ⟩;
      convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( Matrix.toEuclideanLin A ) ) ( fun i => x ( f i ) ) using 1;
      · simp [ Matrix.toEuclideanLin, EuclideanSpace.norm_eq ];
        rw [ ← Equiv.sum_comp e.symm ] ; aesop;
      · simp [ EuclideanSpace.norm_eq, Matrix.opNorm ];
        exact Or.inl ( by rw [ ← Equiv.sum_comp f ] );
  · refine' ContinuousLinearMap.opNorm_le_bound _ _ fun a => _;
    · exact ContinuousLinearMap.opNorm_nonneg _;
    · convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( toEuclideanLin ( Matrix.reindex e f A ) ) ) ( fun i => a ( f.symm i ) ) using 1;
      · simp [ EuclideanSpace.norm_eq, Matrix.toEuclideanLin ];
        rw [ ← Equiv.sum_comp e.symm ] ; simp [ Matrix.mulVec, dotProduct ] ;
        grind;
      · congr! 2;
        simp [ EuclideanSpace.norm_eq]
        conv_lhs => rw [ ← Equiv.sum_comp f.symm ] ;

/--
Define U_rho as the Kronecker product of V_rho and the identity.
-/
noncomputable def U_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix (((dA × dB) × dB) × dC) (dA × dC) ℂ :=
  Matrix.kronecker (V_rho ρAB) (1 : Matrix dC dC ℂ)

/--
Define U_sigma as the Kronecker product of the identity and V_sigma.
-/
noncomputable def U_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dA × (dB × (dB × dC))) (dA × dC) ℂ :=
  Matrix.kronecker (1 : Matrix dA dA ℂ) (V_sigma σBC)

/--
The operator norm of the conjugate transpose is equal to the operator norm.
-/
theorem Matrix.opNorm_conjTranspose_eq_opNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    Matrix.opNorm Aᴴ = Matrix.opNorm A := by
  unfold Matrix.opNorm
  rw [← ContinuousLinearMap.adjoint.norm_map (toEuclideanLin A).toContinuousLinearMap]
  rw [toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

theorem isometry_mul_conjTranspose_le_one {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1) :
    V * V.conjTranspose ≤ 1 := by
  have h_pos : (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp [ sub_mul, mul_sub, ← Matrix.mul_assoc ];
    simp [ Matrix.mul_assoc, hV ];
  have h_pos : (1 - V * Vᴴ) = (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) := by
    simp_all [ Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul ];
  have h_pos : Matrix.PosSemidef (1 - V * Vᴴ) := by
    rw [ h_pos ] at *; apply Matrix.posSemidef_conjTranspose_mul_self;
  grind

/-
If `A†A = I` and `B†B = I` (both isometries into the same space), then `||(A†B)|| ≤ 1`,
  equivalently `(A†B)†(A†B) ≤ I`.
-/
theorem conjTranspose_isometry_mul_isometry_le_one {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix k m ℂ) (B : Matrix k n ℂ)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (A.conjTranspose * B).conjTranspose * (A.conjTranspose * B) ≤ 1 := by
  have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ 1 := by
    have h_le : (Bᴴ * A) * (Bᴴ * A)ᴴ ≤ (Bᴴ * B) := by
      have h_le : (A * Aᴴ) ≤ 1 := by
        apply isometry_mul_conjTranspose_le_one A hA;
      -- Apply the fact that if $X \leq Y$, then $CXC^* \leq CYC^*$ for any matrix $C$.
      have h_conj : ∀ (C : Matrix n k ℂ) (X Y : Matrix k k ℂ), X ≤ Y → C * X * Cᴴ ≤ C * Y * Cᴴ :=
        fun C X Y a => Matrix.PosSemidef.mul_mul_conjTranspose_mono C a
      simpa [ Matrix.mul_assoc ] using h_conj Bᴴ ( A * Aᴴ ) 1 h_le;
    aesop;
  simpa [ Matrix.mul_assoc ] using h_le

/-! ### Helper lemmas for operator_ineq_SSA -/

/- Reindexing preserves the HermitianMat ordering. -/
theorem HermitianMat.reindex_le_reindex_iff {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (e : d ≃ d₂) (A B : HermitianMat d ℂ) :
    A.reindex e ≤ B.reindex e ↔ A ≤ B := by
  constructor <;> intro h <;> rw [HermitianMat.le_iff] at * <;> aesop;

/- Inverse of a Kronecker product of HermitianMat. -/
theorem HermitianMat.inv_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Nonempty m] [Nonempty n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    [A.NonSingular] [B.NonSingular] :
    (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  have h_inv : (A ⊗ₖ B).mat * (A⁻¹ ⊗ₖ B⁻¹).mat = 1 := by
    have h_inv : (A ⊗ₖ B).mat * (A⁻¹ ⊗ₖ B⁻¹).mat = (A.mat * A⁻¹.mat) ⊗ₖ (B.mat * B⁻¹.mat) := by
      ext i j; simp [ Matrix.mul_apply, Matrix.kroneckerMap ] ;
      simp only [mul_assoc, Finset.sum_mul]
      simp only [Finset.mul_sum]
      rw [ ← Finset.sum_product' ] ; congr ; ext ; ring!;
    aesop;
  refine' Subtype.ext ( Matrix.inv_eq_right_inv h_inv )

/- Inverse of a reindexed HermitianMat. -/
theorem HermitianMat.inv_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂) :
    (A.reindex e)⁻¹ = A⁻¹.reindex e := by
  ext1
  simp

/- Kronecker of PosDef matrices is PosDef. -/
theorem HermitianMat.PosDef_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    (A ⊗ₖ B).mat.PosDef := by
  exact Matrix.PosDef.kron hA hB

/- Reindex of PosDef is PosDef. -/
theorem HermitianMat.PosDef_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂)
    (hA : A.mat.PosDef) :
    (A.reindex e).mat.PosDef := by
  convert hA.reindex e

/-- The intermediate operator inequality: ρ_AB ⊗ σ_C⁻¹ ≤ (ρ_A ⊗ σ_BC⁻¹).reindex(assoc⁻¹).
  This is derived from W_mat_sq_le_one by algebraic manipulation (conjugation and simplification). -/
theorem intermediate_ineq [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB ⊗ₖ (σBC.traceLeft)⁻¹ ≤
      (ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm := by
  sorry

open HermitianMat in
/-- **Operator extension of SSA** (Main result of Lin-Kim-Hsieh).
  For positive definite ρ_AB and σ_BC:
  `ρ_A⁻¹ ⊗ σ_BC ≤ ρ_AB⁻¹ ⊗ σ_C`
  where ρ_A = Tr_B(ρ_AB) and σ_C = Tr_B(σ_BC), and the RHS is reindexed
  via the associator `(dA × dB) × dC ≃ dA × (dB × dC)`. -/
theorem operator_ineq_SSA [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB.traceRight⁻¹ ⊗ₖ σBC ≤
      (ρAB⁻¹ ⊗ₖ σBC.traceLeft).reindex (Equiv.prodAssoc dA dB dC) := by
  have h_inv_symm : ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm)⁻¹ ≤ (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ := by
    apply HermitianMat.inv_antitone;
    · apply HermitianMat.PosDef_kronecker ρAB (σBC.traceLeft)⁻¹ hρ (PosDef_traceLeft σBC hσ).inv;
    · exact intermediate_ineq ρAB σBC hρ hσ;
  have h_inv_symm : ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm)⁻¹ = (ρAB.traceRight⁻¹ ⊗ₖ σBC).reindex (Equiv.prodAssoc dA dB dC).symm := by
    have h_inv_symm : (ρAB.traceRight ⊗ₖ σBC⁻¹)⁻¹ = ρAB.traceRight⁻¹ ⊗ₖ (σBC⁻¹)⁻¹ := by
      convert HermitianMat.inv_kronecker _ _ using 1;
      · infer_instance;
      · exact ⟨ ⟨ Classical.arbitrary dB, Classical.arbitrary dC ⟩ ⟩;
      · have h_trace_right_pos_def : (ρAB.traceRight).mat.PosDef := by
          exact PosDef_traceRight ρAB hρ
        exact ⟨by exact PosDef_traceRight ρAB hρ |>.isUnit⟩
      · have h_inv_symm : σBC⁻¹.NonSingular := by
          have h_inv_symm : σBC.NonSingular := by
            exact nonSingular_of_posDef hσ
          exact nonSingular_iff_inv.mpr h_inv_symm;
        exact h_inv_symm;
    convert congr_arg ( fun x : HermitianMat _ _ => x.reindex ( Equiv.prodAssoc dA dB dC ).symm ) h_inv_symm using 1;
    · apply HermitianMat.inv_reindex
    · convert rfl;
      apply HermitianMat.ext;
      convert Matrix.nonsing_inv_nonsing_inv _ _;
      exact isUnit_iff_ne_zero.mpr ( hσ.det_pos.ne' );
  have h_inv_symm : (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ = ρAB⁻¹ ⊗ₖ σBC.traceLeft := by
    have h_inv_symm : (ρAB ⊗ₖ σBC.traceLeft⁻¹)⁻¹ = ρAB⁻¹ ⊗ₖ (σBC.traceLeft⁻¹)⁻¹ := by
      convert HermitianMat.inv_kronecker ρAB ( σBC.traceLeft⁻¹ ) using 1;
      · exact nonSingular_of_posDef hρ;
      · have h_inv_symm : σBC.traceLeft.mat.PosDef := by
          exact PosDef_traceLeft σBC hσ;
        -- Since σBC.traceLeft is positive definite, its inverse is also positive definite, and hence non-singular.
        have h_inv_pos_def : (σBC.traceLeft⁻¹).mat.PosDef := by
          convert h_inv_symm.inv using 1;
        exact nonSingular_of_posDef h_inv_pos_def;
    convert h_inv_symm using 1;
    have h_inv_symm : (σBC.traceLeft⁻¹)⁻¹ = σBC.traceLeft := by
      have h_inv_symm : (σBC.traceLeft⁻¹).mat * σBC.traceLeft.mat = 1 := by
        have h_inv_symm : (σBC.traceLeft⁻¹).mat * σBC.traceLeft.mat = 1 := by
          have h_inv_symm : σBC.traceLeft.mat.PosDef := by
            exact PosDef_traceLeft σBC hσ
          convert Matrix.nonsing_inv_mul _ _;
          exact isUnit_iff_ne_zero.mpr h_inv_symm.det_pos.ne';
        exact h_inv_symm
      have h_inv_symm : (σBC.traceLeft⁻¹ : HermitianMat dC ℂ).mat⁻¹ = σBC.traceLeft.mat := by
        rw [ Matrix.inv_eq_right_inv h_inv_symm ];
      exact Eq.symm (HermitianMat.ext (id (Eq.symm h_inv_symm)));
    rw [h_inv_symm];
  have h_inv_symm : (ρAB.traceRight⁻¹ ⊗ₖ σBC).reindex (Equiv.prodAssoc dA dB dC).symm ≤ ρAB⁻¹ ⊗ₖ σBC.traceLeft := by
    aesop;
  convert HermitianMat.reindex_le_reindex_iff ( Equiv.prodAssoc dA dB dC ) _ _ |>.2 h_inv_symm using 1

open scoped InnerProductSpace RealInnerProductSpace

/-! ### Weak monotonicity and SSA proof infrastructure -/
section SSA_proof

set_option maxHeartbeats 800000

variable {d₁ d₂ d₃ : Type*}

variable [Fintype d₁] [Fintype d₂] [Fintype d₃]

variable [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

omit [DecidableEq d₁] in
open HermitianMat in
private lemma inner_kron_one_eq_inner_traceRight
    (A : HermitianMat d₁ ℂ) (M : HermitianMat (d₁ × d₂) ℂ) :
    ⟪A ⊗ₖ (1 : HermitianMat d₂ ℂ), M⟫ = ⟪A, M.traceRight⟫ := by
  rw [inner_comm];
  -- By definition of partial trace, we have that the trace of M multiplied by (A ⊗ I) is equal to the trace of A multiplied by the partial trace of M.
  have h_partial_trace : Matrix.trace (M.mat * (A.mat ⊗ₖ 1 : Matrix (d₁ × d₂) (d₁ × d₂) ℂ)) = Matrix.trace (A.mat * M.traceRight.mat) := by
    simp [ Matrix.trace, Matrix.mul_apply ];
    simp [ Matrix.traceRight, Matrix.one_apply, mul_comm ];
    simp only [Finset.sum_sigma', Finset.mul_sum _ _ _];
    rw [ ← Finset.sum_filter ];
    refine' Finset.sum_bij ( fun x _ => ⟨ x.snd.1, x.fst.1, x.fst.2 ⟩ ) _ _ _ _ <;> aesop_cat;
  exact congr_arg Complex.re h_partial_trace

omit [DecidableEq d₂] in
open HermitianMat in
private lemma inner_one_kron_eq_inner_traceLeft
    (B : HermitianMat d₂ ℂ) (M : HermitianMat (d₁ × d₂) ℂ) :
    ⟪(1 : HermitianMat d₁ ℂ) ⊗ₖ B, M⟫ = ⟪B, M.traceLeft⟫ := by
  convert inner_kron_one_eq_inner_traceRight B ( M.reindex ( Equiv.prodComm d₁ d₂ ) ) using 1;
  refine' congr_arg ( fun x : ℂ => x.re ) _;
  refine' Finset.sum_bij ( fun x y => ( x.2, x.1 ) ) _ _ _ _ <;> simp [ Matrix.mul_apply ];
  intro a b; rw [ ← Equiv.sum_comp ( Equiv.prodComm d₁ d₂ ) ]
  simp [ Matrix.one_apply, mul_comm ]

open HermitianMat in
private lemma hermitianMat_log_inv_eq_neg
    (A : HermitianMat d₁ ℂ) [A.NonSingular] : A⁻¹.log = -A.log := by
  -- By the property of continuous functional calculus, the logarithm of the inverse of a matrix is the negative of the logarithm of the matrix.
  have h_log_inv : A⁻¹.log = A.cfc (Real.log ∘ (·⁻¹)) := by
    have h_log_inv : A⁻¹ = A.cfc (·⁻¹) := by
      exact Eq.symm HermitianMat.cfc_inv;
    rw [ h_log_inv, HermitianMat.log ];
    exact Eq.symm (HermitianMat.cfc_comp A (fun x => x⁻¹) Real.log);
  simp [ HermitianMat.log ];
  convert congr_arg ( fun f => A.cfc f ) ( show Real.log ∘ ( fun x => x⁻¹ ) = -Real.log from funext fun x => ?_ ) using 1
  · exact Eq.symm (HermitianMat.cfc_neg A Real.log);
  · by_cases hx : x = 0 <;> simp [ hx, Real.log_inv ]

private lemma PosDef_assoc'_traceRight
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    ρ.assoc'.traceRight.M.mat.PosDef := by
  have _ := ρ.nonempty |> nonempty_prod.mp |>.right |> nonempty_prod.mp |>.right
  apply PosDef_traceRight
  convert hρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm

private lemma wm_inner_lhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪(-ρ.assoc'.traceRight.M.traceRight.log) ⊗ₖ (1 : HermitianMat (d₂ × d₃) ℂ) +
     (1 : HermitianMat d₁ ℂ) ⊗ₖ ρ.traceLeft.M.log, ρ.M⟫ =
    Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft := by
  convert congr_arg₂ ( · + · ) _ _ using 1;
  convert inner_add_left _ _ _ using 1;
  · rw [ Sᵥₙ_eq_neg_trace_log ];
    convert inner_kron_one_eq_inner_traceRight _ _ using 1;
    simp [ HermitianMat.traceRight ];
    congr! 2;
    congr! 1;
    ext i j; simp [ Matrix.traceRight ] ;
    exact Fintype.sum_prod_type fun x => ρ.m (i, x) (j, x)
  · rw [ Sᵥₙ_eq_neg_trace_log ];
    simp [ inner_one_kron_eq_inner_traceLeft ]

private lemma wm_inner_rhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪((-ρ.assoc'.traceRight.M.log) ⊗ₖ (1 : HermitianMat d₃ ℂ) +
     (1 : HermitianMat (d₁ × d₂) ℂ) ⊗ₖ ρ.traceLeft.M.traceLeft.log).reindex
      (Equiv.prodAssoc d₁ d₂ d₃), ρ.M⟫ =
    Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft := by
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, Sᵥₙ_eq_neg_trace_log ];
  simp [ inner_add_left, inner_one_kron_eq_inner_traceLeft, inner_kron_one_eq_inner_traceRight ];
  congr! 2;
  convert MState.traceLeft_assoc' ρ using 1;
  unfold MState.assoc' MState.traceLeft; aesop;

/-- Weak monotonicity (form 2) for positive definite states:
    S(ρ₁₂) + S(ρ₂₃) ≥ S(ρ₁) + S(ρ₃).
    Proved by applying operator_ineq_SSA, taking log, then inner product with ρ. -/
private lemma Sᵥₙ_wm_pd [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  -- Set up marginals and their PD properties
  have h₁₂ := PosDef_assoc'_traceRight ρ hρ
  have h₂₃ := PosDef_traceLeft ρ.M hρ
  haveI : ρ.assoc'.traceRight.M.NonSingular := nonSingular_of_posDef h₁₂
  haveI : ρ.traceLeft.M.NonSingular := nonSingular_of_posDef h₂₃
  haveI : ρ.assoc'.traceRight.M.traceRight.NonSingular :=
    nonSingular_of_posDef (PosDef_traceRight _ h₁₂)
  haveI : ρ.traceLeft.M.traceLeft.NonSingular :=
    nonSingular_of_posDef (PosDef_traceLeft _ h₂₃)
  -- Step 1: Operator inequality
  have h_op := operator_ineq_SSA ρ.assoc'.traceRight.M ρ.traceLeft.M h₁₂ h₂₃
  -- Step 2: Take log
  have h_lhs_pd : (ρ.assoc'.traceRight.M.traceRight⁻¹ ⊗ₖ ρ.traceLeft.M).mat.PosDef :=
    HermitianMat.PosDef_kronecker _ _ (PosDef_traceRight _ h₁₂).inv h₂₃
  have h_log := HermitianMat.log_mono h_lhs_pd h_op
  -- Step 3: Simplify logs
  rw [HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  rw [HermitianMat.reindex_log, HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  -- Step 4: Take inner product with ρ.M (≥ 0)
  have h_inner := HermitianMat.inner_mono ρ.nonneg h_log
  -- Step 5: Use commutativity to match wm_inner_lhs/rhs forms
  rw [HermitianMat.inner_comm, HermitianMat.inner_comm ρ.M] at h_inner
  rw [wm_inner_lhs ρ, wm_inner_rhs ρ] at h_inner
  linarith

private lemma MState.approx_by_pd
    (ρ : MState d₁) :
    ∃ (ρn : ℕ → MState d₁), (∀ n, (ρn n).M.mat.PosDef) ∧
      Filter.Tendsto ρn Filter.atTop (nhds ρ) := by
  have h_ne1 := ρ.nonempty
  -- Define the sequence of PD states ρn as the mixture of ρ with the uniform state at weight εn = 1/(n+2).
  set εn : ℕ → ℝ := fun n => 1 / (n + 2)
  set ρn : ℕ → MState d₁ := fun n => Mixable.mix ⟨εn n, by
    exact ⟨ by positivity, by rw [ div_le_iff₀ ] <;> linarith ⟩⟩ (MState.uniform) ρ
  refine' ⟨ ρn, _, _ ⟩;
  · intro n
    have h_pos_def : (ρn n).M = (1 - εn n) • ρ.M + εn n • (MState.uniform (d := d₁)).M := by
      refine' add_comm _ _ |> Eq.trans <| _;
      congr! 1
      aesop;
    have h_pos_def : ∀ (A : Matrix d₁ d₁ ℂ), A.PosSemidef → ∀ (B : Matrix d₁ d₁ ℂ), B.PosDef → ∀ (ε : ℝ), 0 < ε ∧ ε < 1 → (1 - ε) • A + ε • B ∈ {M : Matrix d₁ d₁ ℂ | M.PosDef} := by
      intro A hA B hB ε hε
      constructor <;> simp_all [ Matrix.PosSemidef, Matrix.PosDef ];
      · simp_all [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
      · intro x hx_ne_zero
        have h_pos : 0 < (1 - ε) * (star x ⬝ᵥ A *ᵥ x) + ε * (star x ⬝ᵥ B *ᵥ x) := by
          exact add_pos_of_nonneg_of_pos ( mul_nonneg ( sub_nonneg.2 <| mod_cast hε.2.le ) <| mod_cast hA.2 x ) <| mul_pos ( mod_cast hε.1 ) <| mod_cast hB.2 x hx_ne_zero;
        convert h_pos using 1 ; simp [ Matrix.add_mulVec ] ; ring_nf!
        simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, sub_mul, mul_sub ] ; ring!;
    convert h_pos_def _ _ _ _ _ ⟨ _, _ ⟩ <;> norm_num [ * ];
    congr! 1
    exact psd ρ
    · exact uniform_posDef;
    · exact one_div_pos.mpr ( by linarith );
    · exact div_lt_one ( by positivity ) |>.2 ( by linarith )
  · -- Show that the sequence ρn converges to ρ.
    have h_conv : Filter.Tendsto (fun n => εn n • (MState.uniform : MState d₁).M + (1 - εn n) • ρ.M) Filter.atTop (nhds ρ.M) := by
      exact le_trans ( Filter.Tendsto.add ( Filter.Tendsto.smul ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( Filter.Tendsto.smul ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ) ( by simp );
    rw [ tendsto_iff_dist_tendsto_zero ] at *;
    convert h_conv using 1;
    ext n; simp [ρn, Mixable.mix];
    congr! 1

@[fun_prop]
private lemma MState.traceLeft_continuous :
    Continuous (MState.traceLeft : MState (d₁ × d₂) → MState d₂) := by
  -- Since the matrix traceLeft is continuous, the function that maps a state to its partial trace is also continuous.
  have h_traceLeft_cont : Continuous (fun ρ : HermitianMat (d₁ × d₂) ℂ => ρ.traceLeft) := by
    have h_cont : Continuous (fun ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ => ρ.traceLeft) := by
      exact continuous_pi fun _ => continuous_pi fun _ => continuous_finset_sum _ fun _ _ => continuous_apply _ |> Continuous.comp <| continuous_apply _ |> Continuous.comp <| continuous_id';
    convert h_cont.comp ( show Continuous fun ρ : HermitianMat ( d₁ × d₂ ) ℂ => ρ.1 from ?_ ) using 1;
    · constructor <;> intro h <;> rw [ continuous_induced_rng ] at * <;> aesop;
    · fun_prop;
  exact continuous_induced_rng.mpr ( by continuity )

@[fun_prop]
private lemma MState.traceRight_continuous :
    Continuous (MState.traceRight : MState (d₁ × d₂) → MState d₁) := by
  rw [ continuous_iff_continuousAt ];
  intro ρ
  simp [ContinuousAt] at *;
  rw [ tendsto_nhds ] at *;
  intro s hs hρs;
  rcases hs with ⟨ t, ht, rfl ⟩;
  -- The traceRight map is continuous, so the preimage of an open set under traceRight is open.
  have h_traceRight_cont : Continuous (HermitianMat.traceRight : HermitianMat (d₁ × d₂) ℂ → HermitianMat d₁ ℂ) := by
    -- The traceRight map is a linear map, hence continuous.
    have h_traceRight_linear : ∃ (f : HermitianMat (d₁ × d₂) ℂ →ₗ[ℝ] HermitianMat d₁ ℂ), ∀ A, f A = A.traceRight := by
      refine' ⟨ _, _ ⟩;
      refine' { .. };
      exact fun A => A.traceRight;
      all_goals simp [ HermitianMat.traceRight ];
      · exact fun x y => rfl;
      · aesop
    obtain ⟨ f, hf ⟩ := h_traceRight_linear;
    convert f.continuous_of_finiteDimensional;
    exact funext fun A => hf A ▸ rfl;
  have := h_traceRight_cont.isOpen_preimage t ht;
  exact Filter.mem_of_superset ( this.preimage ( continuous_induced_dom ) |> IsOpen.mem_nhds <| by simpa using hρs ) fun x hx => hx

@[fun_prop]
private lemma MState.assoc'_continuous :
    Continuous (MState.assoc' : MState (d₁ × d₂ × d₃) → MState ((d₁ × d₂) × d₃)) := by
  apply continuous_induced_rng.mpr;
  -- The reindex function is continuous because it is a composition of continuous functions (permutations).
  have h_reindex_cont : Continuous (fun ρ : HermitianMat (d₁ × d₂ × d₃) ℂ => ρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm) := by
    apply continuous_induced_rng.mpr;
    fun_prop (disch := norm_num);
  convert h_reindex_cont.comp _ using 2;
  exact Continuous_HermitianMat

/-- Weak monotonicity, version with partial traces. -/
lemma Sᵥₙ_wm (ρ : MState (d₁ × d₂ × d₃)) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  have h_ne123 := ρ.nonempty
  obtain ⟨ ρn, hρn_pos, hρn ⟩ := MState.approx_by_pd ρ;
  -- Apply the inequality for each ρn and then take the limit.
  have h_lim : Filter.Tendsto (fun n => Sᵥₙ (ρn n).traceRight + Sᵥₙ (ρn n).traceLeft.traceLeft) Filter.atTop (nhds (Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft)) ∧ Filter.Tendsto (fun n => Sᵥₙ (ρn n).assoc'.traceRight + Sᵥₙ (ρn n).traceLeft) Filter.atTop (nhds (Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft)) := by
    constructor <;> refine' Filter.Tendsto.add _ _;
    · exact Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceRight_continuous.continuousAt.tendsto.comp hρn );
    · exact Sᵥₙ_continuous.comp ( MState.traceLeft_continuous.comp ( MState.traceLeft_continuous ) ) |> fun h => h.continuousAt.tendsto.comp hρn;
    · convert Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceRight_continuous.continuousAt.tendsto.comp ( MState.assoc'_continuous.continuousAt.tendsto.comp hρn ) ) using 1;
    · exact Sᵥₙ_continuous.continuousAt.tendsto.comp ( MState.traceLeft_continuous.continuousAt.tendsto.comp hρn );
  have ⟨_, hn23⟩ := nonempty_prod.mp h_ne123
  have ⟨_, _⟩ := nonempty_prod.mp hn23
  exact le_of_tendsto_of_tendsto' h_lim.1 h_lim.2 fun n => Sᵥₙ_wm_pd _ ( hρn_pos n )

/-- Permutation to relabel (A×B×C)×R as A×(B×C×R). -/
private def perm_A_BCR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ dA × (dB × dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (a, (b,c,r))
  invFun x := let (a, (b,c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The BCR state: trace out A from the purification of ρ_ABC. -/
private def ρBCR (ρ : MState (dA × dB × dC)) : MState (dB × dC × (dA × dB × dC)) :=
  ((MState.pure ρ.purify).relabel (perm_A_BCR' dA dB dC).symm).traceLeft

private lemma S_BC_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).assoc'.traceRight = Sᵥₙ ρ.traceLeft := by
  -- By definition of ρBCR, we know that its BC-marginal is equal to the BC-marginal of ρ.
  have h_marginal : (ρBCR ρ).assoc'.traceRight = ρ.traceLeft := by
    unfold ρBCR MState.traceLeft MState.traceRight MState.assoc';
    simp [ MState.assoc, MState.SWAP, MState.relabel, MState.pure, perm_A_BCR' ];
    unfold reindex HermitianMat.traceLeft HermitianMat.traceRight; ext
    simp
    simp [ Matrix.traceLeft, Matrix.traceRight, Matrix.submatrix ];
    have := ρ.purify_spec;
    replace this := congr_arg ( fun x => x.M.val ) this ; simp_all [ MState.traceRight, MState.pure ];
    simp [ ← this, Matrix.traceRight, Matrix.vecMulVec ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  rw [h_marginal]

/-- Equivalence to relabel the purification as (dA × dB) × (dC × R). -/
private def perm_AB_CR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dB) × (dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,b), (c,r))
  invFun x := let ((a,b), (c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-
PROBLEM
The CR-marginal of ρBCR equals the traceLeft of the AB|CR-relabeled purification.
PROVIDED SOLUTION
Both sides are MStates, so use MState.ext to reduce to equality of HermitianMat, then ext to reduce to matrix entries.
The LHS: (ρBCR ρ).traceLeft
= ((MState.pure ρ.purify).relabel (perm_A_BCR' dA dB dC).symm).traceLeft.traceLeft
(since ρBCR = the traceLeft of the relabeled pure state, and then traceLeft again traces out B)
The RHS: ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceLeft
Both trace out {A, B} from the pure state |ψ⟩⟨ψ|, just via different relabelings. The result is the same state on C × R.
Unfold ρBCR, MState.traceLeft, MState.relabel, perm_A_BCR', perm_AB_CR'. Then compare matrix entries using ext. The key is showing that summing over (dA, dB) gives the same result regardless of the order of the relabeling.
-/
private lemma BCR_traceLeft_eq_purify_traceLeft (ρ : MState (dA × dB × dC)) :
    (ρBCR ρ).traceLeft =
    ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceLeft := by
  convert MState.ext ?_;
  convert MState.ext ?_;
  any_goals exact ρ.traceLeft.traceLeft;
  · simp [ MState.traceLeft, MState.relabel, perm_AB_CR' ];
    simp [ MState.traceLeft, MState.relabel, ρBCR ];
    unfold HermitianMat.traceLeft
    simp only [mat_reindex, MState.mat_M, Matrix.reindex_apply, mat_mk, Equiv.coe_fn_symm_mk]
    unfold Matrix.traceLeft
    simp
    congr! 2
    ext i₁ j₁
    rw [ ← Finset.sum_product' ]
    simp [ perm_A_BCR' ]
    exact Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) ( by simp ) ( by simp ) ( by simp ) ( by simp );
  · rfl

/-
PROBLEM
The traceRight of the AB|CR-relabeled purification has same entropy as ρ.assoc'.traceRight.
PROVIDED SOLUTION
The traceRight of (MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm is a state on dA × dB. This traces out the C×R part from the relabeled pure state, which is the same as tracing out C and R from the original pure state.
Since (MState.pure ρ.purify).traceRight = ρ (by purify_spec), tracing C from ρ gives ρ.assoc'.traceRight. But the relabeled traceRight traces out {C, R}, not just {R}.
More precisely: the pure state is on (dA × dB × dC) × R. Relabeled by perm_AB_CR', it's on (dA × dB) × (dC × R). traceRight gives state on dA × dB, which is Tr_{C,R}(|ψ⟩⟨ψ|).
This equals Tr_C(Tr_R(|ψ⟩⟨ψ|)) = Tr_C(ρ) = ρ.assoc'.traceRight.
So they have equal Sᵥₙ. The entropy equality follows.
Show the matrices are equal by ext. Use purify_spec: (MState.pure ρ.purify).traceRight = ρ. Then tracing C from ρ: ρ.assoc'.traceRight.
Unfold definitions and show that Tr_{C×R}(|ψ⟩⟨ψ|_{relabeled}) = Tr_C(Tr_R(|ψ⟩⟨ψ|)) = Tr_C(ρ).
For the entropy, use Sᵥₙ_relabel or direct matrix equality + congr.
-/
private lemma purify_AB_traceRight_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight =
    Sᵥₙ ρ.assoc'.traceRight := by
  have h_traceRight : ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight = ρ.assoc'.traceRight := by
    have h_traceRight : (MState.pure ρ.purify).traceRight = ρ := by
      exact MState.purify_spec ρ;
    convert congr_arg ( fun m => m.assoc'.traceRight ) h_traceRight using 1;
    ext i j; simp [ MState.traceRight, MState.assoc' ] ;
    simp [ HermitianMat.traceRight, MState.SWAP, MState.assoc ];
    simp [ Matrix.traceRight, Matrix.submatrix ];
    congr! 2;
    ext i j; simp [ perm_AB_CR' ] ;
    exact Fintype.sum_prod_type _
  rw [h_traceRight]

/-- The CR-marginal of ρBCR has the same entropy as the AB-marginal of ρ. -/
private lemma S_CR_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft = Sᵥₙ ρ.assoc'.traceRight := by
  rw [BCR_traceLeft_eq_purify_traceLeft]
  rw [Sᵥₙ_pure_complement ρ.purify (perm_AB_CR' dA dB dC).symm]
  exact purify_AB_traceRight_eq ρ

private lemma S_B_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceRight = Sᵥₙ ρ.traceLeft.traceRight := by
  unfold ρBCR;
  unfold MState.traceLeft MState.traceRight MState.relabel MState.pure;
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, perm_A_BCR' ];
  unfold Matrix.traceLeft Matrix.traceRight; simp [Matrix.vecMulVec ] ;
  -- By definition of purification, we know that ρ.purify is a purification of ρ.m.
  have h_purify : ∀ (i j : dA × dB × dC), ρ.m i j = ∑ r : dA × dB × dC, ρ.purify (i, r) * (starRingEnd ℂ) (ρ.purify (j, r)) := by
    intro i j
    have := ρ.purify_spec;
    replace this := congr_arg ( fun m => m.M i j ) this
    simp_all [MState.traceRight]
    exact this.symm
  simp only [Finset.sum_sigma', h_purify];
  congr! 3;
  ext i₂ j₂
  simp
  ring_nf
  refine' Finset.sum_bij ( fun x _ => ⟨ x.fst.1, x.snd, x.fst.2 ⟩ ) _ _ _ _ <;> simp
  · grind
  · grind

private lemma S_R_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft.traceLeft = Sᵥₙ ρ := by
  have h_trace : (ρBCR ρ).traceLeft.traceLeft = (MState.pure ρ.purify).traceLeft := by
    unfold ρBCR MState.traceLeft;
    ext i j;
    simp [ HermitianMat.traceLeft];
    simp [ perm_A_BCR', Matrix.traceLeft ];
    simp [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ( x.snd.snd, x.snd.fst, x.fst ) ) _ _ _ _ <;> simp
    grind;
  convert Sᵥₙ_of_partial_eq ρ.purify using 1;
  · rw [h_trace];
  · rw [ ρ.purify_spec ]

end SSA_proof

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ := by
  -- Derive Nonempty instances from the existence of ρ₁₂₃
  haveI : Nonempty (d₁ × d₂ × d₃) := by
    by_contra h; rw [not_nonempty_iff] at h
    exact absurd ρ₁₂₃.tr (by simp [HermitianMat.trace, Matrix.trace])
  haveI : Nonempty d₁ := (nonempty_prod.mp ‹_›).1
  haveI : Nonempty (d₂ × d₃) := (nonempty_prod.mp ‹Nonempty (d₁ × d₂ × d₃)›).2
  haveI : Nonempty d₂ := (nonempty_prod.mp ‹_›).1
  haveI : Nonempty d₃ := (nonempty_prod.mp ‹Nonempty (d₂ × d₃)›).2
  -- Apply weak monotonicity to ρBCR, then substitute purification identities
  intro ρ₁₂ ρ₂₃ ρ₂
  have h_wm := Sᵥₙ_wm (ρBCR ρ₁₂₃)
  rw [S_BC_of_BCR_eq, S_CR_of_BCR_eq, S_B_of_BCR_eq, S_R_of_BCR_eq] at h_wm
  linarith

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem Sᵥₙ_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft := by
  have := Sᵥₙ_strong_subadditivity (ρ.relabel (d₂ := d₁ × Unit × d₂)
    ⟨fun x ↦ (x.1, x.2.2), fun x ↦ (x.1, ⟨(), x.2⟩), fun x ↦ by simp, fun x ↦ by simp⟩)
  simp [Sᵥₙ_relabel] at this
  convert this using 1
  congr 1
  · convert Sᵥₙ_relabel _ (Equiv.prodPUnit _).symm
    exact rfl
  · convert Sᵥₙ_relabel _ (Equiv.punitProd _).symm
    exact rfl

/-- Triangle inequality for pure tripartite states: S(A) ≤ S(B) + S(C). -/
theorem Sᵥₙ_pure_tripartite_triangle (ψ : Ket ((d₁ × d₂) × d₃)) :
    Sᵥₙ (MState.pure ψ).traceRight.traceRight ≤
    Sᵥₙ (MState.pure ψ).traceRight.traceLeft + Sᵥₙ (MState.pure ψ).traceLeft := by
  have h_subadd := Sᵥₙ_subadditivity (MState.pure ψ).assoc.traceLeft
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = _ :=
    MState.relabel_pure_exists ψ _
  grind [Sᵥₙ_of_partial_eq, MState.traceLeft_left_assoc,
    MState.traceLeft_right_assoc, MState.traceRight_assoc]

/-- One direction of the Araki-Lieb triangle inequality: S(A) ≤ S(B) + S(AB). -/
theorem Sᵥₙ_triangle_ineq_one_way (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceRight ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ := by
  have := Sᵥₙ_pure_tripartite_triangle ρ.purify
  have := Sᵥₙ_of_partial_eq ρ.purify
  aesop

/-- Araki-Lieb triangle inequality on von Neumann entropy -/
theorem Sᵥₙ_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft) ≤ Sᵥₙ ρ := by
  rw [abs_sub_le_iff]
  constructor
  · have := Sᵥₙ_triangle_ineq_one_way ρ
    grind only
  · have := Sᵥₙ_triangle_ineq_one_way ρ.SWAP
    grind only [Sᵥₙ_triangle_ineq_one_way, Sᵥₙ_of_SWAP_eq, MState.traceRight_SWAP,
      MState.traceLeft_SWAP]

/-- Weak monotonicity of quantum conditional entropy: S(A|B) + S(A|C) ≥ 0. -/
theorem Sᵥₙ_weak_monotonicity (ρ : MState (dA × dB × dC)) :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC := by
  simp only [qConditionalEnt, MState.traceRight_left_assoc', Sᵥₙ_of_SWAP_eq]
  rw [add_sub, sub_add_eq_add_sub, le_sub_iff_add_le, le_sub_iff_add_le, zero_add]
  nth_rw 2 [add_comm]
  simpa using Sᵥₙ_wm ρ.SWAP.assoc.SWAP.assoc

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem qConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ₁₂₃ ≤ qConditionalEnt ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qConditionalEnt, MState.traceRight_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem qMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qMutualInfo ρ₁₂₃ ≥ qMutualInfo ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qMutualInfo, MState.traceRight_left_assoc', MState.traceRight_right_assoc']
  linarith

/-- The quantum conditional mutual information `QCMI` is nonnegative. -/
theorem qcmi_nonneg (ρ : MState (dA × dB × dC)) :
    0 ≤ qcmi ρ := by
  simp [qcmi, qConditionalEnt]
  have := Sᵥₙ_strong_subadditivity ρ
  linarith

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dA. -/
theorem qcmi_le_2_log_dim (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dA) := by
  have := Sᵥₙ_subadditivity ρ.assoc'.traceRight
  have := abs_le.mp (Sᵥₙ_triangle_subaddivity ρ)
  grind [qcmi, qConditionalEnt, Sᵥₙ_nonneg, Sᵥₙ_le_log_d]

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dC. -/
theorem qcmi_le_2_log_dim' (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dC) := by
  have h_araki_lieb_assoc' : Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft ≤ Sᵥₙ ρ := by
    apply le_of_abs_le
    rw [← ρ.traceLeft_assoc', ← Sᵥₙ_of_assoc'_eq ρ]
    exact Sᵥₙ_triangle_subaddivity ρ.assoc'
  have := Sᵥₙ_subadditivity ρ.traceLeft
  grind [qcmi, qConditionalEnt, Sᵥₙ_le_log_d, MState.traceRight_left_assoc']

/- The chain rule for quantum conditional mutual information:
`I(A₁A₂ : C | B) = I(A₁:C|B) + I(A₂:C|BA₁)`.

It should be something like this, but it's hard to track the indices correctly:
theorem qcmi_chain_rule (ρ : MState ((dA₁ × dA₂) × dB × dC)) :
    let ρA₁BC := ρ.assoc.SWAP.assoc.traceLeft.SWAP;
    let ρA₂BA₁C : MState (dA₂ × (dA₁ × dB) × dC) :=
      ((CPTPMap.id ⊗ₖ CPTPMap.assoc').compose (CPTPMap.assoc.compose (CPTPMap.SWAP ⊗ₖ CPTPMap.id))) ρ;
    qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
     := by
  admit
-/
