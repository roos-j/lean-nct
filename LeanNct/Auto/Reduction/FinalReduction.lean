/- This file was machine generated -/

module
public import LeanNct.Auto.Reduction.TwistedAverages
public import LeanNct.Auto.Reduction.AToLambda
public import LeanNct.Auto.Reduction.WindowsAndPairs
public import LeanNct.Auto.Reduction.BumpFunctions
public import LeanNct.Auto.Reduction.SmoothingDecomposition
public import LeanNct.Auto.Reduction.Miscellany
public import LeanNct.Auto.Reduction.OnDiagonalOffDiagonal

/-!
# Final reduction

Formalization of the ``Final reduction: proof of main theorem'' subsection of
the reduction argument.  This module deliberately depends on the shared
reduction-level twisted averages rather than `Introduction`, so that the final
reduction remains on the acyclic side of the import graph.
-/

@[expose] public section
namespace Auto

open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform Real



noncomputable section
/-- The exponent $\alpha(n)=1-2^{-n+2}$ fixed in the final reduction. -/
noncomputable def variationExponent (n : ℕ) : ℝ :=
  1 - (2 : ℝ) ^ (-(n : ℝ) + 2)

/-- The indicator kernel used in the statement of the main twisted theorem. -/
noncomputable def unitIntervalIndicator : ℝ → ℝ :=
  (Set.Icc (0 : ℝ) 1).indicator fun _ ↦ (1 : ℝ)

/--
A normalized tuple of real Schwartz functions in the coordinate model used by the
reduction modules.
-/
abbrev ReductionNormalizedTuple (n : ℕ) :=
  {f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ //
    ∀ i, eLpNorm (f i) ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2)) volume = 1}

/-- A finite dyadic chain for the long-variation estimates. -/
abbrev aux_dyadicChain (J : ℕ) := TwistedDyadicChain J

/-- A finite positive chain for the full variation estimates. -/
abbrev aux_scaleChain (J : ℕ) := TwistedScaleChain J

/-- The squared jump-energy along an arbitrary positive scale chain. -/
noncomputable def aux_jumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (J : ℕ)
    (t : aux_scaleChain J) : ℝ≥0∞ :=
  twistedJumpEnergy chi (fun i x ↦ f i x) J t

/-- The squared jump-energy along a dyadic scale chain. -/
noncomputable def aux_dyadicJumpEnergy {n : ℕ} (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (J : ℕ)
    (k : aux_dyadicChain J) : ℝ≥0∞ :=
  twistedDyadicJumpEnergy chi (fun i x ↦ f i x) J k

/--
The Fourier support/derivative hypotheses common to `mainAuxOne` and `mainAuxTwo`.
This raw-function formulation also applies directly to the logarithmic derivative
in `shortLongFtcReduction`.
-/
def aux_mainAuxiliaryFourierHypotheses (psi : ℝ → ℝ) : Prop :=
  Function.support (FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) ∧
    ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m (FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))) xi‖ ≤ 1

/-- The Schwartz-function specialization of the main auxiliary hypotheses. -/
def aux_mainAuxiliaryHypotheses (psi : SchwartzMap ℝ ℝ) : Prop :=
  aux_mainAuxiliaryFourierHypotheses (fun x ↦ psi x)

/-- The additional $T\psi$ hypothesis in `mainAuxTwo`. -/
def aux_mainAuxiliaryTwoHypotheses (psi : SchwartzMap ℝ ℝ) : Prop :=
  aux_mainAuxiliaryHypotheses psi ∧
    ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m (FourierTransform.fourier
        (Auto.aux_T (fun x : ℝ ↦ (psi x : ℂ))) ) xi‖ ≤ 1

/-- The common finite-variation conclusion for a bump in the final reduction. -/
def aux_variationBound {n : ℕ} (C : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) : Prop :=
  ∀ J : ℕ, 0 < J → ∀ t : aux_scaleChain J,
    aux_jumpEnergy chi f J t ≤
      ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)

/-- The common dyadic finite-variation conclusion for a bump. -/
def aux_dyadicVariationBound {n : ℕ} (C : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) : Prop :=
  ∀ J : ℕ, 0 < J → ∀ k : aux_dyadicChain J,
    aux_dyadicJumpEnergy chi f J k ≤
      ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)

/-- The constant in Lemma `Auto.mainAuxOne`. -/
noncomputable def C_mainAuxOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitneyProduct n

/-- The first main-auxiliary constant is nonnegative. -/
theorem aux_C_mainAuxOne_nonneg (n : ℕ) : 0 ≤ C_mainAuxOne n := by
  have hdiagonal : 0 ≤ C_diagonalBandReduction := by
    unfold C_diagonalBandReduction
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) aux_CincreaseDataReduction_nonneg)
  have hnonWhitney : 0 ≤ C_inductPositiveTermsReductionNonWhitney := by
    unfold C_inductPositiveTermsReductionNonWhitney
    apply add_nonneg
    · norm_num [C_oneScaleEstimateWindow, C_uniPair]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) hdiagonal
  have hskip : 0 ≤ C_inductPositiveTermsReductionNonWhitneySkip n := by
    unfold C_inductPositiveTermsReductionNonWhitneySkip
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hnonWhitney
  have hgap : 0 ≤ C_inductPositiveTermsReductionWhitneyGap n := by
    unfold C_inductPositiveTermsReductionWhitneyGap
    exact add_nonneg (mul_nonneg (by norm_num) hskip)
      (mul_nonneg (mul_nonneg (by positivity) (add_nonneg (sq_nonneg _)
        (sq_nonneg _))) hdiagonal)
  have hWhitney : 0 ≤ C_inductPositiveTermsReductionWhitney n := by
    unfold C_inductPositiveTermsReductionWhitney
    exact mul_nonneg (by norm_num) hgap
  have hproduct : 0 ≤ C_inductPositiveTermsReductionWhitneyProduct n := by
    unfold C_inductPositiveTermsReductionWhitneyProduct
    exact mul_nonneg (by positivity) hWhitney
  unfold C_mainAuxOne
  exact mul_nonneg (by positivity) hproduct

theorem aux_mainAuxOne_windowRescale_fourier (t : ℝ) (ht : 0 < t)
    (phi : SchwartzMap ℝ ℝ) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (aux_windowRescale phi t x : ℂ)) xi =
      FourierTransform.fourier (fun x : ℝ => (phi x : ℂ)) (t * xi) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun q => (phi q : ℂ) *
    Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * (q : ℂ) * ((t * xi : ℝ) : ℂ)))
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) •
        (aux_windowRescale phi t x : ℂ)) = ∫ x : ℝ, (t⁻¹ : ℂ) * g (t⁻¹ * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [g, aux_windowRescale]
      have hphase : Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) =
          Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * ((t⁻¹ * x : ℝ) : ℂ) *
            ((t * xi : ℝ) : ℂ))) := by
        congr 1
        push_cast
        field_simp [ne_of_gt ht]
      rw [hphase]
      push_cast
      ring
    _ = (t⁻¹ : ℂ) * ∫ x : ℝ, g (t⁻¹ * x) := by rw [integral_const_mul]
    _ = (t⁻¹ : ℂ) * (|t| • ∫ y : ℝ, g y) := by
      rw [Measure.integral_comp_inv_mul_left]
    _ = ∫ y : ℝ, g y := by
      rw [abs_of_pos ht]
      field_simp [ne_of_gt ht]
      rw [Complex.real_smul]
    _ = ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * (t * xi)) * Complex.I) •
        (phi x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [g]
      push_cast
      ring_nf

theorem aux_mainAuxOne_fourier_real_const_mul (c : ℝ) (f : ℝ → ℝ) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => ((c * f x : ℝ) : ℂ)) xi =
      (c : ℂ) * FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) xi := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  push_cast
  ring

noncomputable def aux_mainAuxOne_windowSchwartz (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) : SchwartzMap ℝ ℝ :=
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 t⁻¹ (inv_ne_zero ht.ne'))
  t⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e psi

theorem aux_mainAuxOne_windowSchwartz_apply (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    aux_mainAuxOne_windowSchwartz psi t ht x = aux_windowRescale psi t x := by
  simp [aux_mainAuxOne_windowSchwartz, aux_windowRescale,
    ContinuousLinearEquiv.smulLeft_apply_apply]

noncomputable def aux_mainAuxOne_scaledWindowSchwartz (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) : SchwartzMap ℝ ℝ :=
  (2 : ℝ) ^ (-2 : ℤ) • aux_mainAuxOne_windowSchwartz psi t ht

theorem aux_mainAuxOne_scaledWindowSchwartz_apply (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    aux_mainAuxOne_scaledWindowSchwartz psi t ht x =
      (2 : ℝ) ^ (-2 : ℤ) * aux_windowRescale psi t x := by
  rw [aux_mainAuxOne_scaledWindowSchwartz, smul_apply,
    aux_mainAuxOne_windowSchwartz_apply]
  rfl

theorem aux_mainAuxOne_scaledWindowSchwartz_fourier (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (xi : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t ht x : ℂ)) xi =
      ((2 : ℝ) ^ (-2 : ℤ) : ℂ) *
        FourierTransform.fourier (fun x : ℝ => (psi x : ℂ)) (t * xi) := by
  rw [show (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t ht x : ℂ)) =
      fun x => (((2 : ℝ) ^ (-2 : ℤ) * aux_windowRescale psi t x : ℝ) : ℂ) by
        funext x
        norm_cast]
  rw [aux_mainAuxOne_fourier_real_const_mul,
    aux_mainAuxOne_windowRescale_fourier t ht psi xi]
  norm_cast

theorem aux_mainAuxOne_scaledWindowSchwartz_support (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryHypotheses psi) (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    Function.support
      (FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t
          (lt_of_lt_of_le zero_lt_one ht.1) x : ℂ))) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3) := by
  rcases hpsi with ⟨hsupp, hderiv⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  intro xi hxi
  have hne := Function.mem_support.mp hxi
  rw [aux_mainAuxOne_scaledWindowSchwartz_fourier psi t htpos xi] at hne
  have hbase : FourierTransform.fourier (fun x : ℝ => (psi x : ℂ)) (t * xi) ≠ 0 := by
    exact (mul_ne_zero_iff.mp hne).2
  have hmem := hsupp (Function.mem_support.mpr hbase)
  unfold Auto.aux_annulusOne at hmem ⊢
  change 1 / ((2 : ℝ) ^ 2) ≤ |t * xi| ∧ |t * xi| ≤ (2 : ℝ) ^ 2 * 1 at hmem
  change 1 / ((2 : ℝ) ^ 3) ≤ |xi| ∧ |xi| ≤ (2 : ℝ) ^ 3 * 1
  rw [abs_mul, abs_of_pos htpos] at hmem
  norm_num at hmem ⊢
  constructor
  · have hmul : t * |xi| ≤ 2 * |xi| :=
      mul_le_mul_of_nonneg_right ht.2 (abs_nonneg xi)
    linarith [hmem.1.trans hmul]
  · calc
      |xi| = 1 * |xi| := by ring
      _ ≤ t * |xi| := mul_le_mul_of_nonneg_right ht.1 (abs_nonneg xi)
      _ ≤ 4 := hmem.2
      _ ≤ 8 := by norm_num

theorem aux_mainAuxOne_scaledWindowSchwartz_deriv (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryHypotheses psi) (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m
        (FourierTransform.fourier
          (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t
            (lt_of_lt_of_le zero_lt_one ht.1) x : ℂ))) xi‖ ≤ 1 := by
  rcases hpsi with ⟨hsupp, hderiv⟩
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (psi x : ℂ))
  have hF : ContDiff ℝ 2 F := by
    let psiC : SchwartzMap ℝ ℂ :=
      SchwartzMap.postcompCLM Complex.ofRealCLM psi
    have hs : ContDiff ℝ 2 (FourierTransform.fourier psiC : ℝ → ℂ) :=
      (FourierTransform.fourier psiC).smooth 2
    have hpsiC : (psiC : ℝ → ℂ) = fun y : ℝ => (psi y : ℂ) := by
      funext y
      simp [psiC, SchwartzMap.postcompCLM_apply]
    rw [SchwartzMap.fourier_coe, hpsiC] at hs
    exact hs
  intro m hm xi
  have hFbound : ∀ q : ℕ, q < 3 → ∀ x : ℝ, ‖iteratedDeriv q F x‖ ≤ 1 := by
    intro q hq x
    exact hderiv q hq x
  have hformula :
      (fun z : ℝ => FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t htpos x : ℂ)) z) =
        fun z => ((2 : ℝ) ^ (-2 : ℤ) : ℂ) * F (t * z) := by
    funext z
    exact aux_mainAuxOne_scaledWindowSchwartz_fourier psi t htpos z
  change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier
        (fun x : ℝ => (aux_mainAuxOne_scaledWindowSchwartz psi t htpos x : ℂ)) z) xi‖ ≤ 1
  rw [hformula, iteratedDeriv_const_mul_field]
  rw [show iteratedDeriv m (fun z : ℝ => F (t * z)) xi =
      t ^ m • iteratedDeriv m F (t * xi) by
        exact congrFun (iteratedDeriv_comp_const_smul
          (hF.of_le (by norm_cast; omega)) t) xi]
  rw [norm_mul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg htpos.le _)]
  have hcoef : ‖((2 : ℝ) ^ (-2 : ℤ) : ℂ)‖ = (2 : ℝ) ^ (-2 : ℤ) := by
    norm_num
  rw [hcoef]
  have hpow : t ^ m ≤ 4 := by
    have hpow' : t ^ m ≤ (2 : ℝ) ^ m :=
      pow_le_pow_left₀ htpos.le ht.2 m
    have hm2 : m ≤ 2 := by omega
    calc
      t ^ m ≤ (2 : ℝ) ^ m := hpow'
      _ ≤ 4 := by interval_cases m <;> norm_num
  have hc : (0 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℤ) := by positivity
  calc
    (2 : ℝ) ^ (-2 : ℤ) * (t ^ m * ‖iteratedDeriv m F (t * xi)‖) ≤
        (2 : ℝ) ^ (-2 : ℤ) * (t ^ m * 1) := by
          gcongr
          exact hFbound m hm (t * xi)
    _ ≤ 1 := by
      have hscale : (2 : ℝ) ^ (-2 : ℤ) * t ^ m ≤ 1 := by
        calc
          (2 : ℝ) ^ (-2 : ℤ) * t ^ m ≤ (2 : ℝ) ^ (-2 : ℤ) * 4 := by
            gcongr
          _ = 1 := by norm_num
      nlinarith

/--
Extend the finite dyadic scales selected by a `TwistedDyadicChain` to a
multiplicatively spaced bi-infinite sequence.
-/
theorem aux_mainAuxOne_extend_dyadic_chain (J : ℕ) (hJ : 0 < J)
    (k : aux_dyadicChain J) :
    ∃ a : ℤ → ℝ, SpacedSequence a ∧
      ∀ j : Fin J, a (j : ℤ) = (2 : ℝ) ^ (k.1 j.castSucc) := by
  let b : ℤ → ℝ := fun z => if hz : 0 ≤ z ∧ z < (J : ℤ) then
    (2 : ℝ) ^ (k.1 (⟨z.toNat, by omega⟩ : Fin J).castSucc) else 1
  obtain ⟨a, ha, hrestrict, hlarge, hsmall⟩ :=
    (extensionOfSequences J hJ b (by
      intro z hz0 hzJ
      rw [show b z = (2 : ℝ) ^
          (k.1 (⟨z.toNat, by omega⟩ : Fin J).castSucc) by
        simp [b, hz0, hzJ]]
      exact zpow_pos (by norm_num) _)
      (by
        intro z hz0 hznext
        have hzJ : z < (J : ℤ) := by omega
        have hznextJ : z + 1 < (J : ℤ) := hznext
        let j : Fin J := ⟨z.toNat, by omega⟩
        have hsucc :
            (⟨(z + 1).toNat, by omega⟩ : Fin J).castSucc = j.succ := by
          apply Fin.ext
          dsimp [j]
          omega
        have hfin : j.castSucc < j.succ := Fin.castSucc_lt_succ
        have hstrict : k.1 j.castSucc < k.1 j.succ := k.2 hfin
        have hexp : k.1 j.castSucc + 1 ≤ k.1 j.succ :=
          Int.add_one_le_iff.mpr hstrict
        have hbz : b z = (2 : ℝ) ^ (k.1 j.castSucc) := by
          dsimp [b]
          rw [dif_pos ⟨hz0, hzJ⟩]
          congr 3
        have hbnext : b (z + 1) = (2 : ℝ) ^ (k.1 j.succ) := by
          dsimp [b]
          rw [dif_pos ⟨by omega, hznextJ⟩]
          simpa using congrArg (fun q : Fin (J + 1) =>
            (2 : ℝ) ^ (k.1 q)) hsucc
        rw [hbz, hbnext]
        calc
          2 * (2 : ℝ) ^ (k.1 j.castSucc) =
              (2 : ℝ) ^ (k.1 j.castSucc + 1) := by
                rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                norm_num
                ring
          _ ≤ (2 : ℝ) ^ (k.1 j.succ) := by
                exact (zpow_le_zpow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mpr hexp)).exists
  refine ⟨a, ha, ?_⟩
  intro j
  rw [hrestrict (j : ℤ) (by omega) (by omega)]
  dsimp [b]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 3

theorem aux_mainAuxOne_scaled_product_bound {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (t : ℝ) (ht : t ∈ Set.Icc 1 2) (a : ℤ → ℝ) (ha : SpacedSequence a) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_whitneyProductSequence
        (aux_mainAuxOne_scaledWindowSchwartz psi t
          (lt_of_lt_of_le zero_lt_one ht.1)) a) ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyProduct n) := by
  apply inductPositiveTermsReductionWhitneyProduct hn a ha
  · exact aux_mainAuxOne_scaledWindowSchwartz_support psi hpsi t ht
  · exact aux_mainAuxOne_scaledWindowSchwartz_deriv psi hpsi t ht

theorem aux_mainAuxOne_normalizer_mul_variation (n : ℕ) (hn : 2 ≤ n)
    (J : ℕ) (hJ : 0 < J) :
    ENNReal.ofReal (min 1
      (Real.rpow (J : ℝ) (-1 + (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1)))) *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n) = 1 := by
  have hJone : 1 ≤ (J : ℝ) := by
    exact_mod_cast (show 1 ≤ J by omega)
  have hJpos : 0 < (J : ℝ) := lt_of_lt_of_le zero_lt_one hJone
  have hpow : (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1) =
      (2 : ℝ) ^ (-(n : ℝ) + 2) := by
    rw [← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hvar : 0 ≤ variationExponent n := by
    unfold variationExponent
    rw [← hpow]
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnonpos : (-(n : ℝ) + 2) ≤ 0 := by linarith
    have hsmall : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hnonpos
    linarith
  have hweight : min 1
      (Real.rpow (J : ℝ) (-1 + (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1))) =
      (J : ℝ) ^ (-variationExponent n) := by
    rw [hpow]
    have hexp : -1 + (2 : ℝ) ^ (-(n : ℝ) + 2) = -variationExponent n := by
      unfold variationExponent
      ring
    rw [hexp]
    exact min_eq_right
      (Real.rpow_le_one_of_one_le_of_nonpos hJone (neg_nonpos.mpr hvar))
  rw [hweight, ← ENNReal.ofReal_mul (Real.rpow_nonneg hJpos.le _)]
  rw [← Real.rpow_add hJpos]
  ring_nf
  simp

theorem aux_mainAuxOne_prefix_from_seminorm {n : ℕ} (hn : 2 ≤ n)
    (M : KernelSequence 1) (C : ℝ)
    (hM : kernelSequenceSeminorm n 1 (by omega) (by omega) M ≤ ENNReal.ofReal C)
    (J : ℕ) (hJ : 0 < J) (F : NormalizedFunctionTuple n) :
    ENNReal.ofReal
      |prismForm n 1 (by omega) (by omega)
        (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
        (fun i => F.1 i)| ≤
      ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let w : ℝ := min 1
    (Real.rpow (J : ℝ) (-1 + (2 : ℝ) ^ ((1 : ℤ) - (n : ℤ) + 1)))
  have hterm : ENNReal.ofReal
      (w * |prismForm n 1 (by omega) (by omega)
        (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
        (fun i => F.1 i)|) ≤
      kernelSequenceSeminorm n 1 (by omega) (by omega) M := by
    unfold kernelSequenceSeminorm
    apply le_iSup_of_le ⟨J, hJ⟩
    apply le_iSup_of_le F
    rfl
  have hterm' : ENNReal.ofReal
      (w * |prismForm n 1 (by omega) (by omega)
        (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
        (fun i => F.1 i)|) ≤ ENNReal.ofReal C := hterm.trans hM
  have hwr : ENNReal.ofReal w * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) = 1 := by
    dsimp [w]
    exact aux_mainAuxOne_normalizer_mul_variation n hn J hJ
  rw [ENNReal.ofReal_mul (by
    dsimp [w]
    exact le_min zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))] at hterm'
  calc
    ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i => F.1 i)| =
        1 * ENNReal.ofReal
          |prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
            (fun i => F.1 i)| := by rw [one_mul]
    _ = (ENNReal.ofReal w * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) *
        ENNReal.ofReal
          |prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
            (fun i => F.1 i)| := by rw [hwr]
    _ = (ENNReal.ofReal w * ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i => F.1 i)|) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ac_rfl
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
      mul_le_mul_of_nonneg_right hterm' bot_le

theorem aux_mainAuxOne_product_rescale_identity (psi : SchwartzMap ℝ ℝ)
    (t : ℝ) (ht : 0 < t) (a : ℤ → ℝ) (ha : SpacedSequence a)
    (j : ℤ) (y : RealVector 1 × RealVector 1) :
    aux_liftPlaneKernel
      (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
        (mul_pos (ha j).1 ht))) y =
      (2 : ℝ) ^ 4 *
        aux_whitneyProductSequence (aux_mainAuxOne_scaledWindowSchwartz psi t ht) a j y := by
  simp only [aux_liftPlaneKernel, tensorSquare, aux_whitneyProductSequence,
    aux_windowRescale, aux_mainAuxOne_windowSchwartz_apply,
    aux_mainAuxOne_scaledWindowSchwartz_apply]
  have hapos : a j ≠ 0 := ne_of_gt (ha j).1
  field_simp [hapos, ht.ne']

theorem aux_mainAuxOne_twistedAverage_window {n : ℕ} (psi : SchwartzMap ℝ ℝ)
    (s : ℝ) (hs : 0 < s)
    (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    twistedAverage (aux_mainAuxOne_windowSchwartz psi s hs) f =
      twistedAverageAtScale s (fun x ↦ psi x) f := by
  unfold twistedAverage twistedAverageAtScale
  congr 1

theorem aux_mainAuxOne_rescaled_sequence_bound {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (t : ℝ) (ht : t ∈ Set.Icc 1 2) (a : ℤ → ℝ) (ha : SpacedSequence a) :
    kernelSequenceSeminorm n 1 (by omega) (by omega)
      (fun j y => aux_liftPlaneKernel
        (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
          (mul_pos (ha j).1 (lt_of_lt_of_le zero_lt_one ht.1)))) y) ≤
      ENNReal.ofReal (C_mainAuxOne n) := by
  let eta := aux_mainAuxOne_scaledWindowSchwartz psi t
    (lt_of_lt_of_le zero_lt_one ht.1)
  have hscaled : kernelSequenceSeminorm n 1 (by omega) (by omega)
      (aux_whitneyProductSequence eta a) ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyProduct n) := by
    dsimp [eta]
    exact aux_mainAuxOne_scaled_product_bound hn psi hpsi t ht a ha
  have hseq :
      (fun j y => aux_liftPlaneKernel
        (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
          (mul_pos (ha j).1 (lt_of_lt_of_le zero_lt_one ht.1)))) y) =
      fun j y => (2 : ℝ) ^ 4 * aux_whitneyProductSequence eta a j y := by
    funext j y
    dsimp [eta]
    exact aux_mainAuxOne_product_rescale_identity psi t
      (lt_of_lt_of_le zero_lt_one ht.1) a ha j y
  rw [hseq, aux_kernelSequenceSeminorm_const_mul (by omega) (by omega)
    ((2 : ℝ) ^ 4) (by positivity)]
  calc
    ENNReal.ofReal ((2 : ℝ) ^ 4) *
        kernelSequenceSeminorm n 1 (by omega) (by omega)
          (aux_whitneyProductSequence eta a) ≤
        ENNReal.ofReal ((2 : ℝ) ^ 4) *
          ENNReal.ofReal (C_inductPositiveTermsReductionWhitneyProduct n) :=
      mul_le_mul_of_nonneg_left hscaled bot_le
    _ = ENNReal.ofReal (C_mainAuxOne n) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      rfl

/--
**Lemma.**

Suppose that $\psi:\mathbb{R}\to\mathbb{R}$ is a Schwartz function with

$$
{\rm supp}(\widehat\psi)\subset\mathrm{Ann}_1(1,2^2),
$$

and

$$
|\widehat\psi^{(m)}(\xi)|\le1,
\qquad
m\in[3),
\quad
\xi\in\mathbb{R}.
$$

Then for every $t\in[1,2]$, $J\ge1$, and every strictly increasing sequence of integers
$(k_j)_{j\in[J)}$,

$$
\sum_{j\in[J)}\|A_{2^{k_j}t}(\psi)\|_2^2
\le C_{\text{lem:main\_aux1}}J^{\alpha(n)},
$$

where

$$
C_{\text{lem:main\_aux1}}
=2^4C_{\text{induct positive terms - reduction variant, Whitney, product-type}}.
$$

See also `Auto.mainAuxOne`,
`Auto.inductPositiveTermsReductionWhitneyProduct`.
-/
theorem mainAuxOne {n : ℕ} (hn : 2 ≤ n) (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryHypotheses psi)
    (f : ReductionNormalizedTuple n) (t : ℝ) (ht : t ∈ Set.Icc 1 2)
    (J : ℕ) (hJ : 0 < J) (k : aux_dyadicChain J) :
    ∑ j : Fin J,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc) * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ 2 ≤
      ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  obtain ⟨a, ha, ha_restrict⟩ := aux_mainAuxOne_extend_dyadic_chain J hJ k
  let phi : Fin J → SchwartzMap ℝ ℝ := fun j =>
    aux_mainAuxOne_windowSchwartz psi (a (j : ℤ) * t) (mul_pos (ha (j : ℤ)).1 htpos)
  obtain ⟨F, hFnorm, hsum⟩ := aToLambda_fin_sum (n := n) (J := J) (by omega) phi f.1
  let Fnorm : NormalizedFunctionTuple n := ⟨F, by
    intro i
    convert (hFnorm i ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2))).trans
      (f.2 i) using 1; norm_num⟩
  let M : KernelSequence 1 := fun j y => aux_liftPlaneKernel
    (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j * t)
      (mul_pos (ha j).1 htpos))) y
  have hMbound : kernelSequenceSeminorm n 1 (by omega) (by omega) M ≤
      ENNReal.ofReal (C_mainAuxOne n) := by
    dsimp [M]
    exact aux_mainAuxOne_rescaled_sequence_bound hn psi hpsi t ht a ha
  have hprefix := aux_mainAuxOne_prefix_from_seminorm hn M (C_mainAuxOne n) hMbound J hJ Fnorm
  have hleft :
      (∑ j : Fin J,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc) * t)
          (fun x ↦ psi x) (fun i x ↦ f.1 i x)) 2 volume ^ 2) =
      ∑ j : Fin J,
        eLpNorm (twistedAverage (phi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [phi]
    rw [aux_mainAuxOne_twistedAverage_window]
    rw [ha_restrict j]
  have hkernel :
      (fun y : RealVector 1 × RealVector 1 =>
        ∑ j : Fin J, phi j (y.1 0) * phi j (y.2 0)) =
      fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y := by
    funext y
    let g : ℕ → ℝ := fun r => if hr : r < J then M (r : ℤ) y else 0
    calc
      (∑ j : Fin J, phi j (y.1 0) * phi j (y.2 0)) =
          ∑ r ∈ Finset.range J, g r := by
            rw [← Fin.sum_univ_eq_sum_range g J]
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [g]
            rw [if_pos j.2]
            simp only [M, phi, aux_liftPlaneKernel, tensorSquare]
      _ = ∑ r ∈ Finset.range J, M (r : ℤ) y := by
            apply Finset.sum_congr rfl
            intro r hr
            dsimp [g]
            rw [if_pos (Finset.mem_range.mp hr)]
  have hsum' :
      (∑ j : Fin J,
        eLpNorm (twistedAverage (phi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2) =
      ENNReal.ofReal
        (prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i x ↦ F i x)) := by
    rw [hsum, hkernel]
  calc
    ∑ j : Fin J,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc) * t)
          (fun x ↦ psi x) (fun i x ↦ f.1 i x)) 2 volume ^ 2 =
        ENNReal.ofReal
          (prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
            (fun i x ↦ F i x)) := hleft.trans hsum'
    _ ≤ ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i x ↦ F i x)| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      simpa [Fnorm] using hprefix

/--
The sharp Whitney-product reduction estimate used for the first final-reduction
constant.
-/
theorem aux_constantWhitneyProductReduction_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionWhitneyProduct n <
      (1397 / 2048 : ℝ) * (2 : ℝ) ^ 569 := by
  unfold C_inductPositiveTermsReductionWhitneyProduct
    C_inductPositiveTermsReductionWhitney
  calc
    (2 : ℝ) ^ 12 * (11 * C_inductPositiveTermsReductionWhitneyGap n) <
        (2 : ℝ) ^ 12 * (11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553)) := by
      exact mul_lt_mul_of_pos_left
        (mul_lt_mul_of_pos_left (constantWhitneyGapReduction hn) (by norm_num))
        (by positivity)
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 569 := by
      calc
        (2 : ℝ) ^ 12 * (11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553)) =
            ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 16) * (2 : ℝ) ^ 553 := by
              rw [show (2 : ℝ) ^ 12 = 4096 by norm_num,
                show (2 : ℝ) ^ 16 = 65536 by norm_num]
              set_option exponentiation.threshold 1000 in
                ring
        _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 16 * (2 : ℝ) ^ 553) := by
          set_option exponentiation.threshold 1000 in
            ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 569 := by rw [← pow_add]

/--
The sharper form of the `mainAuxOne` constant estimate before its final
relaxation to a pure power of two.
-/
theorem aux_constantMainAuxOne_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxOne n < (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 := by
  unfold C_mainAuxOne
  calc
    (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitneyProduct n <
        (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 569) :=
      mul_lt_mul_of_pos_left (aux_constantWhitneyProductReduction_sharp hn) (by positivity)
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 := by
      calc
        (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 569) =
            (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 4 * (2 : ℝ) ^ 569) := by
              set_option exponentiation.threshold 1000 in
                ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 := by rw [← pow_add]

/--
**Lemma (constant $C_{\text{lem:main\_aux1}}$).**

$$
C_{\text{lem:main\_aux1}}<2^{573}.
$$

See also `Auto.mainAuxOne`.
-/
theorem constantMainAuxiliaryOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxOne n < (2 : ℝ) ^ 573 := by
  calc
    C_mainAuxOne n < (1397 / 2048 : ℝ) * (2 : ℝ) ^ 573 :=
      aux_constantMainAuxOne_sharp hn
    _ < (2 : ℝ) ^ 573 := by
      apply mul_lt_of_lt_one_left
      · positivity
      · norm_num

noncomputable def aux_shortLong_scaleKernel
    (phi : SchwartzMap ℝ ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s ↦ t⁻¹ * phi (t⁻¹ * s)

theorem aux_shortLong_scaleKernel_memLp (phi : SchwartzMap ℝ ℝ) (t : ℝ) :
    MemLp (aux_shortLong_scaleKernel phi t) 2 volume := by
  by_cases ht : t = 0
  · subst t
    have : aux_shortLong_scaleKernel phi 0 = 0 := by
      funext s
      simp [aux_shortLong_scaleKernel]
    rw [this]
    exact MemLp.zero
  · have hmeas : AEStronglyMeasurable (aux_shortLong_scaleKernel phi t) volume := by
      change AEStronglyMeasurable (fun s : ℝ ↦ t⁻¹ * phi (t⁻¹ * s)) (volume : Measure ℝ)
      exact (continuous_const.mul
        (phi.continuous.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hmeas).mpr
    have hsq : Integrable (fun s : ℝ ↦ phi s ^ 2) (volume : Measure ℝ) :=
        (phi.memLp 2).integrable_sq
    have hrescale : Integrable (fun s : ℝ ↦
        t⁻¹ ^ 2 * phi (t⁻¹ * s) ^ 2) (volume : Measure ℝ) :=
      (hsq.comp_mul_left' (inv_ne_zero ht)).const_mul (t⁻¹ ^ 2)
    have heq : (fun s : ℝ ↦ aux_shortLong_scaleKernel phi t s ^ 2) =
        fun s ↦ t⁻¹ ^ 2 * phi (t⁻¹ * s) ^ 2 := by
      funext s
      dsimp [aux_shortLong_scaleKernel]
      ring
    rw [heq]
    exact hrescale

noncomputable def aux_shortLong_averageLp {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (t : ℝ) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi t)
    (aux_shortLong_scaleKernel_memLp phi t)).toLp _

theorem aux_shortLong_twistedAverageAtScale_contDiffOn {n : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ContDiffOn ℝ 1
      (fun t ↦ twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x)
      (Set.Icc α β) := by
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x
  let b : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (aux_tBump phi) (fun i y ↦ f i y) x
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext u
    change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  have hdiff : DifferentiableOn ℝ a (Set.Icc α β) := by
    intro t ht
    exact (aux_twistedAverageAtScale_hasDerivAt phi f x t
      (lt_of_lt_of_le hα ht.1)).differentiableAt.differentiableWithinAt
  have hcontb : ContinuousOn b (Set.Icc α β) := by
    have hconttau : ContinuousOn
        (fun t ↦ twistedAverageAtScale t (fun u ↦ tau u) (fun i y ↦ f i y) x)
        (Set.Icc α β) := by
      intro t ht
      exact (aux_twistedAverageAtScale_hasDerivAt tau f x t
        (lt_of_lt_of_le hα ht.1)).continuousAt.continuousWithinAt
    refine hconttau.congr ?_
    intro t ht
    dsimp [b]
    rw [← htau]
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc α β) := by
    exact continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le hα ht.1))
  have hcontg : ContinuousOn (fun t : ℝ ↦ -t⁻¹ * b t) (Set.Icc α β) := by
    change ContinuousOn ((fun t : ℝ ↦ -(t⁻¹)) * b) (Set.Icc α β)
    exact hinv.neg.mul hcontb
  rw [show (1 : WithTop ℕ∞) = 1 by rfl,
    contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hαβ)]
  refine ⟨hdiff, hcontg.congr ?_⟩
  intro t ht
  exact (aux_twistedAverageAtScale_hasDerivAt phi f x t
    (lt_of_lt_of_le hα ht.1)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hαβ) t ht)

theorem aux_shortLong_averageLp_enorm_sub {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (s t : ℝ) :
    (‖aux_shortLong_averageLp hn phi f s -
        aux_shortLong_averageLp hn phi f t‖₊ : ℝ≥0∞) =
      eLpNorm
        (fun x ↦ twistedAverageAtScale s (fun u ↦ phi u) (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f.1 i y) x)
        2 volume := by
  let hs := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi s)
    (aux_shortLong_scaleKernel_memLp phi s)
  let ht := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi t)
    (aux_shortLong_scaleKernel_memLp phi t)
  change ‖hs.toLp _ - ht.toLp _‖ₑ = _
  rw [← hs.toLp_sub ht]
  rw [Lp.enorm_toLp]
  rfl

theorem aux_shortLong_ftcATphi_lintegral {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℤ) :
    (∫⁻ t,
      ‖t * deriv (fun s ↦
        twistedAverageAtScale s (fun u ↦ phi u) (fun i y ↦ f i y) x) t‖ₑ ^ (2 : ℝ)
        ∂aux_logarithmicMeasure ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let α : ℝ := (2 : ℝ) ^ k
  let β : ℝ := (2 : ℝ) ^ (k + 1)
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x
  let g : ℝ → ℝ := fun t ↦
    twistedAverageAtScale (α * t) (aux_tBump phi) (fun i y ↦ f i y) x
  have hα : 0 < α := by
    dsimp [α]
    exact zpow_pos (by norm_num) _
  have hβ : β = α * 2 := by
    dsimp [α, β]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hαβ : α < β := by rw [hβ]; nlinarith
  have hconta := aux_shortLong_twistedAverageAtScale_contDiffOn phi f x hα hαβ
  have hcontb : ContinuousOn
      (fun t ↦ twistedAverageAtScale t (aux_tBump phi) (fun i y ↦ f i y) x)
      (Set.Icc α β) := by
    let psi : SchwartzMap ℝ ℝ :=
      SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
    let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
    have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
      funext u
      change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
      simp only [SchwartzMap.derivCLM_apply, aux_tBump]
      congr 1
      funext z
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
      simp only [smul_eq_mul]
    have hconttau : ContinuousOn
        (fun t ↦ twistedAverageAtScale t (fun u ↦ tau u) (fun i y ↦ f i y) x)
        (Set.Icc α β) := by
      intro t ht
      exact (aux_twistedAverageAtScale_hasDerivAt tau f x t
        (lt_of_lt_of_le hα ht.1)).continuousAt.continuousWithinAt
    refine hconttau.congr ?_
    intro t ht
    rw [← htau]
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc α β) :
      t * deriv a t = -twistedAverageAtScale t (aux_tBump phi)
        (fun i y ↦ f i y) x := by
    have h := aux_twistedAverageAtScale_hasDerivAt phi f x t
      (lt_of_lt_of_le hα ht.1)
    rw [h.deriv]
    field_simp [ne_of_gt (lt_of_lt_of_le hα ht.1)]
  have hcontd : ContinuousOn (fun t ↦ t * deriv a t) (Set.Icc α β) := by
    refine hcontb.neg.congr ?_
    intro t ht
    exact hderiv t ht
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc α β) :=
    continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le hα ht.1))
  have hleftCont : ContinuousOn (fun t ↦ |t * deriv a t| ^ 2 * t⁻¹)
      (Set.Icc α β) := by
    change ContinuousOn ((fun t ↦ |t * deriv a t| ^ 2) * fun t ↦ t⁻¹)
      (Set.Icc α β)
    exact (hcontd.abs.pow 2).mul hinv
  have hleftInt : Integrable (fun t ↦ |t * deriv a t| ^ 2 * t⁻¹)
      (volume.restrict (Set.Icc α β)) := hleftCont.integrableOn_Icc
  have hcontg : ContinuousOn g (Set.Icc (1 : ℝ) 2) := by
    have hscale : ContinuousOn (fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2) :=
      (continuous_const.mul continuous_id).continuousOn
    have hmaps : MapsTo (fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2)
        (Set.Icc α β) := by
      intro t ht
      constructor
      · calc
          α = α * 1 := (mul_one _).symm
          _ ≤ α * t := mul_le_mul_of_nonneg_left ht.1 hα.le
      · calc
          α * t ≤ α * 2 := mul_le_mul_of_nonneg_left ht.2 hα.le
          _ = β := hβ.symm
    change ContinuousOn
      ((fun t ↦ twistedAverageAtScale t (aux_tBump phi) (fun i y ↦ f i y) x) ∘
        fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2)
    exact hcontb.comp hscale hmaps
  have hinvOne : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc (1 : ℝ) 2) :=
    continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hrightCont : ContinuousOn (fun t ↦ |g t| ^ 2 * t⁻¹)
      (Set.Icc (1 : ℝ) 2) := by
    change ContinuousOn ((fun t ↦ |g t| ^ 2) * fun t ↦ t⁻¹)
      (Set.Icc (1 : ℝ) 2)
    exact (hcontg.abs.pow 2).mul hinvOne
  have hrightInt : Integrable (fun t ↦ |g t| ^ 2 * t⁻¹)
      (volume.restrict (Set.Icc (1 : ℝ) 2)) := hrightCont.integrableOn_Icc
  have hFTC :
      (∫ t in Set.Icc α β, |t * deriv a t| ^ 2 * t⁻¹) =
        ∫ t in Set.Icc (1 : ℝ) 2, |g t| ^ 2 * t⁻¹ := by
    simpa only [α, β, a, g] using ftcATphi phi f x k
  have hleftNonneg : 0 ≤ᵐ[volume.restrict (Set.Icc α β)]
      fun t ↦ |t * deriv a t| ^ 2 * t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (lt_of_lt_of_le hα ht.1).le)
  have hrightNonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)]
      fun t ↦ |g t| ^ 2 * t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (lt_of_lt_of_le zero_lt_one ht.1).le)
  have hleftOfReal := ofReal_integral_eq_lintegral_ofReal hleftInt hleftNonneg
  have hrightOfReal := ofReal_integral_eq_lintegral_ofReal hrightInt hrightNonneg
  have hweightMeas : AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal t⁻¹)
      (volume.restrict (Set.Icc α β)) :=
    (measurable_inv.comp measurable_id).ennreal_ofReal.aemeasurable
  have hweightFinite : ∀ᵐ t : ℝ ∂volume.restrict (Set.Icc α β),
      ENNReal.ofReal t⁻¹ < ∞ :=
    ae_of_all _ fun _ ↦ lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
  have hleftDensity :
      (∫⁻ t,
        ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) =
        ∫⁻ t in Set.Icc α β,
          ENNReal.ofReal (|t * deriv a t| ^ 2 * t⁻¹) := by
    unfold aux_logarithmicMeasure
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hweightMeas hweightFinite]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le hα ht.1
    change ENNReal.ofReal t⁻¹ * ‖t * deriv a t‖ₑ ^ (2 : ℝ) = _
    rw [show ‖t * deriv a t‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (|t * deriv a t| ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two,
        Real.rpow_two]]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [ENNReal.ofReal_inv_of_pos htpos]
    ring
  have hrightEnorm :
      (∫⁻ t in Set.Icc (1 : ℝ) 2,
        ENNReal.ofReal (|g t| ^ 2 * t⁻¹)) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖g t‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [show ENNReal.ofReal (|g t| ^ 2) = ‖g t‖ₑ ^ (2 : ℝ) by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two,
        Real.rpow_two]]
  change (∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
      ∂aux_logarithmicMeasure α β) =
    ∫⁻ t in Set.Icc (1 : ℝ) 2, ‖g t‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  rw [hleftDensity, ← hleftOfReal, hFTC, hrightOfReal, hrightEnorm]

theorem aux_shortLong_pointwise_local_energy {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (J : ℕ) (k : ℤ)
    (u : Fin (J + 1) → aux_dyadicInterval k) (hu : Monotone u) :
    (∑ j : Fin J,
      ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f i y) x -
        twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f i y) x‖ₑ ^
          (2 : ℝ)) ≤
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let α : ℝ := (2 : ℝ) ^ k
  let β : ℝ := (2 : ℝ) ^ (k + 1)
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun q ↦ phi q) (fun i y ↦ f i y) x
  have hα : 0 < α := by
    dsimp [α]
    exact zpow_pos (by norm_num) _
  have hβ : β = α * 2 := by
    dsimp [α, β]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hαβ : α < β := by rw [hβ]; nlinarith
  have hcont : ContDiffOn ℝ 1 a (Set.Icc α β) := by
    exact aux_shortLong_twistedAverageAtScale_contDiffOn phi f x hα hαβ
  let U : {v : Fin (J + 1) → Set.Icc α β // Monotone v} :=
    ⟨fun j ↦ ⟨u j, by simpa only [α, β, aux_dyadicInterval] using (u j).2⟩,
      by
        intro i j hij
        exact hu hij⟩
  have hchain :
      (∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        finiteVariationSeminorm (fun s : Set.Icc α β ↦ a s) 2 J := by
    rw [finiteVariationSeminorm]
    exact le_iSup (fun v : {v : Fin (J + 1) → Set.Icc α β // Monotone v} ↦
      (∑ j : Fin J,
        (‖a (v.1 j.succ) - a (v.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^
          ((2 : ℝ)⁻¹)) U
  have hratio : (β - α) / α = 1 := by
    rw [hβ]
    field_simp [ne_of_gt hα]
    norm_num
  have hftc := (ftcCsR J hα hαβ a hcont).1
  have hroot :
      (∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
    calc
      (∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
          finiteVariationSeminorm (fun s : Set.Icc α β ↦ a s) 2 J := hchain
      _ ≤ (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
          aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := hftc
      _ = aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by rw [hratio]; norm_num
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hleft :
      ((∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) ^
          (2 : ℝ) =
        ∑ j : Fin J,
          ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hsquare
  have hlogSq : (aux_logarithmicL2 α β (fun t ↦ t * deriv a t)) ^ (2 : ℝ) =
      ∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
    unfold aux_logarithmicL2
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := aux_logarithmicMeasure α β)
      (f := fun t ↦ t * deriv a t) (p := (2 : NNReal))
      (by norm_num : (2 : NNReal) ≠ 0)
    simpa [ENNReal.rpow_two] using h
  calc
    (∑ j : Fin J,
      ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f i y) x -
        twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f i y) x‖ₑ ^
          (2 : ℝ)) =
        ∑ j : Fin J,
          ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ) := by
      congr 2 with j
    _ ≤ (aux_logarithmicL2 α β (fun t ↦ t * deriv a t)) ^ (2 : ℝ) := hsquare
    _ = ∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := hlogSq
    _ = ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ :=
      aux_shortLong_ftcATphi_lintegral phi f x k

theorem aux_shortLong_joint_measurable_twistedAverageAtScale {n : ℕ}
    (psi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (α : ℝ) :
    StronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      twistedAverageAtScale (α * tx.1) (fun u ↦ psi u) (fun i y ↦ f i y) tx.2) := by
  let F : ((ℝ × EuclideanSpace ℝ (Fin n)) × ℝ) → ℝ := fun z ↦
    (α * z.1.1)⁻¹ * psi ((α * z.1.1)⁻¹ * z.2) *
      ∏ i, f i (z.1.2 + z.2 • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  have hInt : StronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      ∫ s : ℝ, F (tx, s) ∂(volume : Measure ℝ)) :=
    hF.stronglyMeasurable.integral_prod_right' (ν := volume)
  simpa only [F, aux_twistedAverageAtScale, aux_twistedAverage] using hInt

theorem aux_shortLong_lp_chain_energy_eq_lintegral {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (k : ℤ)
    (u : Fin (J + 1) → aux_dyadicInterval k) (_hu : Monotone u) :
    (∑ j : Fin J,
      ‖aux_shortLong_averageLp hn phi f (u j.succ) -
        aux_shortLong_averageLp hn phi f (u j.castSucc)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x,
        ∑ j : Fin J,
          ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q)
              (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) := by
  let g : Fin J → EuclideanSpace ℝ (Fin n) → ℝ := fun j x ↦
    twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
      twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x
  have hmem (j : Fin J) : MemLp (g j) 2 volume := by
    let hs := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi (u j.succ))
      (aux_shortLong_scaleKernel_memLp phi (u j.succ))
    let ht := aux_twistedAverage_memLp hn f.1 (aux_shortLong_scaleKernel phi (u j.castSucc))
      (aux_shortLong_scaleKernel_memLp phi (u j.castSucc))
    change MemLp
      (twistedAverage (aux_shortLong_scaleKernel phi (u j.succ)) (fun i y ↦ f.1 i y) -
        twistedAverage (aux_shortLong_scaleKernel phi (u j.castSucc))
          (fun i y ↦ f.1 i y)) 2 volume
    exact hs.sub ht
  have hmeas (j : Fin J) : AEMeasurable (fun x ↦ ‖g j x‖ₑ ^ (2 : ℝ)) volume :=
    (hmem j).aestronglyMeasurable.enorm.pow_const _
  calc
    (∑ j : Fin J,
      ‖aux_shortLong_averageLp hn phi f (u j.succ) -
        aux_shortLong_averageLp hn phi f (u j.castSucc)‖ₑ ^ (2 : ℝ)) =
        ∑ j : Fin J, eLpNorm (g j) 2 volume ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℝ))
        (aux_shortLong_averageLp_enorm_sub hn phi f (u j.succ) (u j.castSucc))
    _ = ∑ j : Fin J, ∫⁻ x, ‖g j x‖ₑ ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := g j)
        (p := (2 : NNReal)) (by norm_num)
    _ = ∫⁻ x, ∑ j : Fin J, ‖g j x‖ₑ ^ (2 : ℝ) := by
      simpa using (lintegral_finsetSum' (μ := volume) Finset.univ
        (f := fun j x ↦ ‖g j x‖ₑ ^ (2 : ℝ)) (fun j _ ↦ hmeas j)).symm

theorem aux_shortLong_local_variation_sq_le {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (k : ℤ) :
    (finiteVariationSeminorm
      (fun s : aux_dyadicInterval k ↦
        aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext u
    change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  let R : ℝ≥0∞ := ∫⁻ t in Set.Icc (1 : ℝ) 2,
    eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
      (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  have hR : R = ∫⁻ t in Set.Icc (1 : ℝ) 2,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
        (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    dsimp [R]
    rw [htau]
  have hchain (u : {v : Fin (J + 1) → aux_dyadicInterval k // Monotone v}) :
      (∑ j : Fin J,
        ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
          aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ≤ R := by
    let H : EuclideanSpace ℝ (Fin n) → ℝ → ℝ≥0∞ := fun x t ↦
      ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
        (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        (∑ j : Fin J,
          ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
              (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t := by
      have h := aux_shortLong_pointwise_local_energy phi f.1 x J k u.1 u.2
      rw [← htau] at h
      exact h
    have hpointInt :
        (∫⁻ x,
          ∑ j : Fin J,
            ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
                (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ x, ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t := by
      apply lintegral_mono
      exact hpoint
    have hjoint : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
          twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) z.1)
        (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
      exact (aux_shortLong_joint_measurable_twistedAverageAtScale tau f.1 ((2 : ℝ) ^ k)
        |>.comp_measurable measurable_swap).aestronglyMeasurable
    have hHmeas : AEMeasurable (Function.uncurry H)
        (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
      have hweight : AEMeasurable
          (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦ ENNReal.ofReal z.2⁻¹)
          (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) :=
        ((measurable_inv.comp measurable_snd).ennreal_ofReal).aemeasurable
      change AEMeasurable
        ((fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
          ‖twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) z.1‖ₑ ^ (2 : ℝ)) *
          fun z ↦ ENNReal.ofReal z.2⁻¹) _
      exact (hjoint.enorm.pow_const _).mul hweight
    have hswap := lintegral_lintegral_swap hHmeas
    have htonelli :
        (∫⁻ x, ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t) = R := by
      rw [hswap]
      change (∫⁻ t in Set.Icc (1 : ℝ) 2,
        ∫⁻ x, ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
          (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) = R
      dsimp [R]
      apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      rw [lintegral_mul_const' (ENNReal.ofReal t⁻¹)
        (fun x ↦ ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
          (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ENNReal.ofReal_ne_top]
      have hnorm : eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) x) 2 volume ^ (2 : ℝ) =
          ∫⁻ x, ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) := by
        have h := eLpNorm_nnreal_pow_eq_lintegral (μ := volume)
          (f := fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y) x) (p := (2 : NNReal)) (by norm_num)
        simpa [ENNReal.rpow_two] using h
      rw [← hnorm]
    calc
      (∑ j : Fin J,
        ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
          aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
          ∫⁻ x,
            ∑ j : Fin J,
              ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q)
                  (fun i y ↦ f.1 i y) x -
                twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
                  (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) :=
          aux_shortLong_lp_chain_energy_eq_lintegral hn phi f J k u.1 u.2
      _ ≤ ∫⁻ x, ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t := hpointInt
      _ = R := htonelli
  have hroot : finiteVariationSeminorm
      (fun s : aux_dyadicInterval k ↦ aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J ≤
      R ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro u
    have h := ENNReal.rpow_le_rpow (hchain u) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    simpa only [← enorm_eq_nnnorm] using h
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hright : (R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = R := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hright] at hsquare
  rw [← hR]
  exact hsquare

noncomputable def aux_shortLong_intEnergy (d : ℤ → ℤ → ℝ≥0∞) {J : ℕ}
    (t : Fin (J + 1) → ℤ) : ℝ≥0∞ :=
  ∑ j : Fin J, d (t j.succ) (t j.castSucc)

theorem aux_shortLong_compress_mono_chain
    (d : ℤ → ℤ → ℝ≥0∞) (hdiag : ∀ z, d z z = 0) :
    ∀ (J : ℕ) (t : Fin (J + 1) → ℤ), Monotone t →
      ∃ M : ℕ, M ≤ J ∧ ∃ q : Fin (M + 1) → ℤ,
        StrictMono q ∧ q 0 = t 0 ∧ q (Fin.last M) = t (Fin.last J) ∧
          aux_shortLong_intEnergy d t = aux_shortLong_intEnergy d q := by
  intro J
  induction J with
  | zero =>
      intro t ht
      refine ⟨0, le_rfl, t, ?_, rfl, rfl, ?_⟩
      · intro i j hij
        omega
      · simp [aux_shortLong_intEnergy]
  | succ J ih =>
      intro t ht
      let u : Fin (J + 1) → ℤ := fun i => t i.succ
      have hu : Monotone u := by
        intro i j hij
        dsimp [u]
        apply ht
        exact Fin.succ_le_succ_iff.mpr hij
      obtain ⟨M, hMJ, q, hq, hq0, hqlast, henergy⟩ := ih u hu
      have hsplit : aux_shortLong_intEnergy d t =
          d (t 1) (t 0) + aux_shortLong_intEnergy d u := by
        unfold aux_shortLong_intEnergy
        rw [Fin.sum_univ_succ]
        rfl
      by_cases h01 : t 0 = t 1
      · refine ⟨M, le_trans hMJ (Nat.le_succ _), q, hq, ?_, ?_, ?_⟩
        · simpa [u, h01] using hq0
        · simpa [u, Fin.succ_last] using hqlast
        · rw [hsplit, h01, hdiag, zero_add, henergy]
      · have h01lt : t 0 < t 1 := lt_of_le_of_ne (ht (Fin.zero_le _)) h01
        let q' : Fin (M + 2) → ℤ := fun i => Fin.cases (t 0) q i
        have hq'strict : StrictMono q' := by
          intro i j hij
          by_cases hi : i = 0
          · subst i
            have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hij)
            obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero hj0
            subst j
            have hqle : q 0 ≤ q j' := hq.monotone (Fin.zero_le _)
            have hfirst : t 0 < q 0 := by
              calc
                t 0 < t 1 := h01lt
                _ = u 0 := rfl
                _ = q 0 := hq0.symm
            exact hfirst.trans_le hqle
          · obtain ⟨i', hi'⟩ := Fin.exists_succ_eq_of_ne_zero hi
            subst i
            have hj0 : j ≠ 0 := by
              intro hj
              subst j
              exact (Fin.not_lt_zero i'.succ hij).elim
            obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero hj0
            subst j
            exact hq (Fin.succ_lt_succ_iff.mp hij)
        refine ⟨M + 1, Nat.succ_le_succ hMJ, q', hq'strict, ?_, ?_, ?_⟩
        · rfl
        · simp only [q']
          exact hqlast
        · have hqsplit :
              aux_shortLong_intEnergy d q' =
                d (t 1) (t 0) + aux_shortLong_intEnergy d q := by
            unfold aux_shortLong_intEnergy
            rw [Fin.sum_univ_succ]
            have hqone : q' (Fin.succ 0) = t 1 := by
              change q 0 = t 1
              simpa [u] using hq0
            rw [hqone]
            rfl
          rw [hsplit, henergy, hqsplit]

theorem aux_shortLong_variationExponent_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ variationExponent n := by
  unfold variationExponent
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(n : ℝ) + 2 ≤ 0 := by linarith
  have hpow : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  linarith

theorem aux_shortLong_energy_of_root_le (E S V : ℝ≥0∞)
    (h : E ^ ((2 : ℝ)⁻¹) ≤ 2 * S ^ ((2 : ℝ)⁻¹) + V) :
    E ≤ 8 * S + 2 * V ^ (2 : ℝ) := by
  have hsquare := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  have hleft : (E ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = E := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hsquare
  calc
    E ≤ (2 * S ^ ((2 : ℝ)⁻¹) + V) ^ (2 : ℝ) := hsquare
    _ ≤ (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
        (((2 * S ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ)) + V ^ (2 : ℝ)) := by
      exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (p := (2 : ℝ)) (by norm_num)
    _ = 8 * S + 2 * V ^ (2 : ℝ) := by
      rw [show (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 by norm_num]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      have hterm : (S ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = S := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [hterm]
      norm_num [mul_add]
      congr 1
      · rw [← mul_assoc]
        norm_num

theorem aux_shortLong_long_variation_sq_le {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (_hJ : 0 < J)
    (A : ℝ) (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1) :
    (finiteVariationSeminorm
      (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦
        aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let R : ℝ≥0∞ := ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  have hexpNonneg : 0 ≤ variationExponent n := aux_shortLong_variationExponent_nonneg hn
  have hchain (u : {v : Fin (J + 1) → Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) //
      Monotone v}) :
      (∑ j : Fin J,
        ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
          aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ≤ R := by
    let z : Fin (J + 1) → ℤ := fun j ↦ (u.1 j).2.choose
    have hzval (j : Fin (J + 1)) : (2 : ℝ) ^ z j = u.1 j :=
      (u.1 j).2.choose_spec
    have hzmono : Monotone z := by
      intro i j hij
      apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      calc
        (2 : ℝ) ^ z i = u.1 i := hzval i
        _ ≤ u.1 j := u.2 hij
        _ = (2 : ℝ) ^ z j := (hzval j).symm
    let d : ℤ → ℤ → ℝ≥0∞ := fun p q ↦
      ‖aux_shortLong_averageLp hn phi f ((2 : ℝ) ^ p) -
        aux_shortLong_averageLp hn phi f ((2 : ℝ) ^ q)‖ₑ ^ (2 : ℕ)
    have hdiag (p : ℤ) : d p p = 0 := by
      simp [d]
    obtain ⟨M, hMJ, q, hq, hq0, hqlast, hcompress⟩ :=
      aux_shortLong_compress_mono_chain d hdiag J z hzmono
    have horig :
        (∑ j : Fin J,
          ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
            aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
          aux_shortLong_intEnergy d z := by
      unfold aux_shortLong_intEnergy d
      simp only [ENNReal.rpow_two]
      apply Finset.sum_congr rfl
      intro j _
      rw [hzval]
      rw [hzval]
    by_cases hM : M = 0
    · subst M
      have hzero : aux_shortLong_intEnergy d q = 0 := by simp [aux_shortLong_intEnergy]
      rw [horig, hcompress, hzero]
      exact bot_le
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
      let qc : aux_dyadicChain M := ⟨q, hq⟩
      have hqEnergy : aux_shortLong_intEnergy d q =
          aux_dyadicJumpEnergy (fun x ↦ phi x) f.1 M qc := by
        unfold aux_shortLong_intEnergy d aux_dyadicJumpEnergy
        apply Finset.sum_congr rfl
        intro j _
        dsimp [qc]
        simpa only [← enorm_eq_nnnorm] using congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
          (aux_shortLong_averageLp_enorm_sub hn phi f ((2 : ℝ) ^ (q j.succ))
            ((2 : ℝ) ^ (q j.castSucc)))
      have hq := hA M hMpos qc
      have hMJreal : (M : ℝ) ≤ J := by exact_mod_cast hMJ
      have hpow : (M : ℝ) ^ variationExponent n ≤
          (J : ℝ) ^ variationExponent n :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hMJreal hexpNonneg
      have hpowENN : ENNReal.ofReal ((M : ℝ) ^ variationExponent n) ≤
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
        ENNReal.ofReal_le_ofReal hpow
      calc
        (∑ j : Fin J,
          ‖aux_shortLong_averageLp hn phi f (u.1 j.succ) -
            aux_shortLong_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
            aux_shortLong_intEnergy d z := horig
        _ = aux_shortLong_intEnergy d q := hcompress
        _ = aux_dyadicJumpEnergy (fun x ↦ phi x) f.1 M qc := hqEnergy
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((M : ℝ) ^ variationExponent n) := hq
        _ ≤ R := by
          dsimp [R]
          exact mul_le_mul_of_nonneg_left hpowENN bot_le
  have hroot : finiteVariationSeminorm
      (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦
        aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J ≤ R ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro u
    have h := ENNReal.rpow_le_rpow (hchain u)
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    simpa only [← enorm_eq_nnnorm] using h
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hright : (R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = R := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hright] at hsquare
  exact hsquare

theorem aux_shortLong_dyadic_index_unique {x : ℝ} {k l : ℤ}
    (hk : (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1))
    (hl : (2 : ℝ) ^ l ≤ x ∧ x < (2 : ℝ) ^ (l + 1)) :
    k = l := by
  apply le_antisymm
  · by_contra hnot
    have hlt : l < k := lt_of_not_ge hnot
    have hstep : l + 1 ≤ k := Int.add_one_le_iff.mpr hlt
    have hp : (2 : ℝ) ^ (l + 1) ≤ (2 : ℝ) ^ k :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hstep
    exact (not_lt_of_ge (hp.trans hk.1)) hl.2
  · by_contra hnot
    have hlt : k < l := lt_of_not_ge hnot
    have hstep : k + 1 ≤ l := Int.add_one_le_iff.mpr hlt
    have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ l :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hstep
    exact (not_lt_of_ge (hp.trans hl.1)) hk.2

theorem aux_shortLong_kappa_card_le {J : ℕ}
    (t : Fin (J + 1) → ℝ) (_htpos : ∀ j, 0 < t j)
    (kappa : Finset ℤ)
    (hkappa : ∀ k, k ∈ kappa ↔ ∃ j,
      (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) :
    kappa.card ≤ J + 1 := by
  classical
  choose q hq using fun k : kappa => (hkappa k).mp k.property
  have hqin : Function.Injective q := by
    intro k l hkl
    apply Subtype.ext
    apply aux_shortLong_dyadic_index_unique (x := t (q k)) (k := (k : ℤ)) (l := (l : ℤ))
    · exact hq k
    · simpa [hkl] using hq l
  simpa using Fintype.card_le_of_injective q hqin

theorem aux_shortLong_finset_sum_as_dyadic_chain (kappa : Finset ℤ)
    (hkappa : kappa.Nonempty) :
    ∃ (K : ℕ) (_ : 0 < K) (_ : K = kappa.card) (q : aux_dyadicChain K),
      ∀ F : ℤ → ℝ≥0∞,
        (∑ k ∈ kappa, F k) = ∑ j : Fin K, F (q.1 j.castSucc) := by
  classical
  obtain ⟨M, hcard⟩ : ∃ M : ℕ, kappa.card = M + 1 := by
    have hpos : 0 < kappa.card := Finset.card_pos.mpr hkappa
    refine ⟨kappa.card - 1, ?_⟩
    omega
  let e : Fin (M + 1) ↪o ℤ := kappa.orderEmbOfFin hcard
  let qfun : Fin (M + 2) → ℤ :=
    Fin.lastCases (e (Fin.last M) + 1) e
  have hqfun : StrictMono qfun := by
    intro i j hij
    by_cases hj : j = Fin.last (M + 1)
    · subst j
      change i.1 < M + 1 at hij
      let i' : Fin (M + 1) := ⟨i.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      rw [hi]
      simp only [qfun, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hle : e i' ≤ e (Fin.last M) := e.monotone (Fin.le_last i')
      omega
    · have hjlt : j < Fin.last (M + 1) := Fin.lt_last_iff_ne_last.mpr hj
      change i.1 < j.1 at hij
      change j.1 < M + 1 at hjlt
      let i' : Fin (M + 1) := ⟨i.1, by omega⟩
      let j' : Fin (M + 1) := ⟨j.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      have hj' : j = j'.castSucc := by rfl
      rw [hi, hj']
      simp only [qfun, Fin.lastCases_castSucc]
      apply e.strictMono
      simpa [i', j'] using hij
  let q : aux_dyadicChain (M + 1) := ⟨qfun, hqfun⟩
  refine ⟨M + 1, Nat.zero_lt_succ _, hcard.symm, q, ?_⟩
  intro F
  let e' : Fin (M + 1) → kappa := fun i ↦
    ⟨e i, Finset.orderEmbOfFin_mem kappa hcard i⟩
  have he'inj : Function.Injective e' := by
    intro i j hij
    apply e.injective
    exact congrArg Subtype.val hij
  have he'bij : Function.Bijective e' := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨he'inj, ?_⟩
    simp [hcard]
  let equiv : Fin (M + 1) ≃ kappa := Equiv.ofBijective e' he'bij
  calc
    (∑ k ∈ kappa, F k) = ∑ k : kappa, F k := (Finset.sum_coe_sort kappa F).symm
    _ = ∑ j : Fin (M + 1), F (equiv j) := by
      exact (Equiv.sum_comp equiv (fun k : kappa ↦ F k)).symm
    _ = ∑ j : Fin (M + 1), F (q.1 j.castSucc) := by
      apply Finset.sum_congr rfl
      intro j _
      change F (e j) = F (qfun j.castSucc)
      simp [qfun]

theorem aux_shortLong_mainAuxOne_finset_pointwise {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (kappa : Finset ℤ) (hcard : kappa.card ≤ J + 1)
    (t : ℝ) (ht : t ∈ Set.Icc 1 2) :
    (∑ k ∈ kappa,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)) ≤
      2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  by_cases hkappa : kappa.Nonempty
  · obtain ⟨K, hK, hKcard, q, hsum⟩ :=
      aux_shortLong_finset_sum_as_dyadic_chain kappa hkappa
    let F : ℤ → ℝ≥0∞ := fun k ↦
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)
    have hmain : (∑ j : Fin K, F (q.1 j.castSucc)) ≤
        ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((K : ℝ) ^ variationExponent n) := by
      simpa [F] using mainAuxOne hn psi hpsi f t ht K hK q
    have hexpNonneg : 0 ≤ variationExponent n := by
      unfold variationExponent
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      linarith
    have hexpLeOne : variationExponent n ≤ 1 := by
      unfold variationExponent
      have hpow : 0 ≤ (2 : ℝ) ^ (-(n : ℝ) + 2) :=
        Real.rpow_nonneg (by norm_num) _
      linarith
    have hKle : K ≤ J + 1 := by simpa [hKcard] using hcard
    have hKreal : (K : ℝ) ≤ 2 * J := by
      have hKJ : (K : ℝ) ≤ J + 1 := by exact_mod_cast hKle
      have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      nlinarith
    have htwo : (2 : ℝ) ^ variationExponent n ≤ 2 := by
      calc
        (2 : ℝ) ^ variationExponent n ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpLeOne
        _ = 2 := by norm_num
    have hpow : (K : ℝ) ^ variationExponent n ≤
        2 * (J : ℝ) ^ variationExponent n := by
      calc
        (K : ℝ) ^ variationExponent n ≤ (2 * J : ℝ) ^ variationExponent n :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hKreal hexpNonneg
        _ = (2 : ℝ) ^ variationExponent n * (J : ℝ) ^ variationExponent n :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2 * (J : ℝ) ^ variationExponent n := by gcongr
    have hpowENN : ENNReal.ofReal ((K : ℝ) ^ variationExponent n) ≤
        2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      calc
        ENNReal.ofReal ((K : ℝ) ^ variationExponent n) ≤
            ENNReal.ofReal (2 * (J : ℝ) ^ variationExponent n) :=
          ENNReal.ofReal_le_ofReal hpow
        _ = 2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    calc
      (∑ k ∈ kappa,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
          (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)) =
          ∑ j : Fin K, F (q.1 j.castSucc) := hsum F
      _ ≤ ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((K : ℝ) ^ variationExponent n) := hmain
      _ ≤ ENNReal.ofReal (C_mainAuxOne n) *
          (2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
        gcongr
      _ = 2 * ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ring
  · have hempty : kappa = ∅ := Finset.not_nonempty_iff_eq_empty.mp hkappa
    simp [hempty]

theorem aux_shortLong_finish_of_local {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (B A : ℝ)
    (hBnonneg : 0 ≤ B) (hAnonneg : 0 ≤ A)
    (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1)
    (hlocal : ∀ (J : ℕ), 0 < J → ∀ κ : Finset ℤ, κ.card ≤ J + 1 →
      ∑ k ∈ κ,
        (finiteVariationSeminorm
          (fun s : aux_dyadicInterval k ↦
            aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
        ENNReal.ofReal B * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :
    aux_variationBound (8 * B + 2 * A) (fun x ↦ phi x) f.1 := by
  unfold aux_variationBound
  intro J hJ t
  let a : ℝ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aux_shortLong_averageLp hn phi f
  obtain ⟨κ, hκ, hsplit⟩ :=
    (shortlongJumps a J 2 (by norm_num : (1 : ℝ) ≤ 2)).1 t.1 t.2.1.monotone t.2.2
  let S : ℝ≥0∞ := ∑ k ∈ κ,
    (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) 2 J) ^ (2 : ℝ)
  let V : ℝ≥0∞ := finiteVariationSeminorm
    (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) 2 J
  have henergy :
      (∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ≤
        8 * S + 2 * V ^ (2 : ℝ) := by
    exact aux_shortLong_energy_of_root_le _ S V hsplit
  have hlocal' : S ≤ ENNReal.ofReal B *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    have hcard : κ.card ≤ J + 1 :=
      aux_shortLong_kappa_card_le t.1 t.2.2 κ hκ
    dsimp [S, a]
    exact hlocal J hJ κ hcard
  have hlong' : V ^ (2 : ℝ) ≤
      ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    dsimp [V, a]
    exact aux_shortLong_long_variation_sq_le hn phi f J hJ A hA
  have htarget :
      8 * S + 2 * V ^ (2 : ℝ) ≤
        ENNReal.ofReal (8 * B + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    calc
      8 * S + 2 * V ^ (2 : ℝ) ≤
          8 * (ENNReal.ofReal B * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) +
          2 * (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
            gcongr
      _ = (8 * ENNReal.ofReal B + 2 * ENNReal.ofReal A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ring
      _ = ENNReal.ofReal (8 * B + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
        rw [ENNReal.ofReal_add]
        · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        · exact mul_nonneg (by norm_num) hBnonneg
        · exact mul_nonneg (by norm_num) hAnonneg
  have hjump : aux_jumpEnergy (fun x ↦ phi x) f.1 J t =
      ∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ) := by
    unfold aux_jumpEnergy twistedJumpEnergy
    simp only [ENNReal.rpow_two]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [← enorm_eq_nnnorm, ENNReal.rpow_two] using
      (congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
        (aux_shortLong_averageLp_enorm_sub hn phi f (t.1 j.succ) (t.1 j.castSucc))).symm
  rw [hjump]
  exact henergy.trans htarget

theorem aux_shortLong_finish {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (A : ℝ)
    (hApos : 0 < A) (hCnonneg : 0 ≤ C_mainAuxOne n)
    (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1)
    (hlocal : ∀ (J : ℕ), 0 < J → ∀ κ : Finset ℤ, κ.card ≤ J + 1 →
      ∑ k ∈ κ,
        (finiteVariationSeminorm
          (fun s : aux_dyadicInterval k ↦
            aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
        2 * ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :
    aux_variationBound (16 * C_mainAuxOne n + 2 * A) (fun x ↦ phi x) f.1 := by
  unfold aux_variationBound
  intro J hJ t
  let a : ℝ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aux_shortLong_averageLp hn phi f
  obtain ⟨κ, hκ, hsplit⟩ :=
    (shortlongJumps a J 2 (by norm_num : (1 : ℝ) ≤ 2)).1 t.1 t.2.1.monotone t.2.2
  let S : ℝ≥0∞ := ∑ k ∈ κ,
    (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) 2 J) ^ (2 : ℝ)
  let V : ℝ≥0∞ := finiteVariationSeminorm
    (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) 2 J
  have henergy :
      (∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ≤
        8 * S + 2 * V ^ (2 : ℝ) := by
    exact aux_shortLong_energy_of_root_le _ S V hsplit
  have hlocal' : S ≤ 2 * ENNReal.ofReal (C_mainAuxOne n) *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    have hcard : κ.card ≤ J + 1 :=
      aux_shortLong_kappa_card_le t.1 t.2.2 κ hκ
    dsimp [S, a]
    exact hlocal J hJ κ hcard
  have hlong' : V ^ (2 : ℝ) ≤
      ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    dsimp [V, a]
    exact aux_shortLong_long_variation_sq_le hn phi f J hJ A hA
  have htarget :
      8 * S + 2 * V ^ (2 : ℝ) ≤
        ENNReal.ofReal (16 * C_mainAuxOne n + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    calc
      8 * S + 2 * V ^ (2 : ℝ) ≤
          8 * (2 * ENNReal.ofReal (C_mainAuxOne n) *
            ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) +
          2 * (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
            gcongr
      _ = (16 * ENNReal.ofReal (C_mainAuxOne n) + 2 * ENNReal.ofReal A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ring
      _ = ENNReal.ofReal (16 * C_mainAuxOne n + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
        rw [ENNReal.ofReal_add]
        · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        · exact mul_nonneg (by norm_num) hCnonneg
        · exact mul_nonneg (by norm_num) hApos.le
  have hjump : aux_jumpEnergy (fun x ↦ phi x) f.1 J t =
      ∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ) := by
    unfold aux_jumpEnergy twistedJumpEnergy
    simp only [ENNReal.rpow_two]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [← enorm_eq_nnnorm, ENNReal.rpow_two] using
      (congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
        (aux_shortLong_averageLp_enorm_sub hn phi f (t.1 j.succ) (t.1 j.castSucc))).symm
  rw [hjump]
  exact henergy.trans htarget

theorem aux_shortLong_T_eq_tBump (phi : SchwartzMap ℝ ℝ) :
    Auto.aux_T (fun x : ℝ ↦ phi x) = aux_tBump phi := by
  funext x
  unfold Auto.aux_T
    Auto.multiplicationOperatorX aux_tBump
  simp only [smul_eq_mul]

theorem aux_shortLong_tBump_auxHyp (phi : SchwartzMap ℝ ℝ)
    (hTphi : aux_mainAuxiliaryFourierHypotheses
      (Auto.aux_T (fun x : ℝ ↦ phi x))) :
    ∃ tau : SchwartzMap ℝ ℝ, (tau : ℝ → ℝ) = aux_tBump phi ∧
      aux_mainAuxiliaryHypotheses tau := by
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext u
    change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  refine ⟨tau, htau, ?_⟩
  · unfold aux_mainAuxiliaryHypotheses
    rw [show (fun x : ℝ ↦ tau x) =
      Auto.aux_T (fun x : ℝ ↦ phi x) by
        exact htau.trans (aux_shortLong_T_eq_tBump phi).symm]
    exact hTphi

theorem aux_shortLong_finset_log_integral_le
    (κ : Finset ℤ) (g : ℤ → ℝ → ℝ≥0∞)
    (hg : ∀ k ∈ κ, AEMeasurable (g k) (volume.restrict (Set.Icc (1 : ℝ) 2)))
    (B : ℝ≥0∞)
    (hpoint : ∀ᵐ t ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      ∑ k ∈ κ, g k t ≤ B) :
    (∑ k ∈ κ, ∫⁻ t in Set.Icc (1 : ℝ) 2,
      g k t * ENNReal.ofReal t⁻¹) ≤ B := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (1 : ℝ) 2)
  have hweight : AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal t⁻¹) μ :=
    (ENNReal.measurable_ofReal.comp measurable_inv).aemeasurable
  calc
    (∑ k ∈ κ, ∫⁻ t in Set.Icc (1 : ℝ) 2,
        g k t * ENNReal.ofReal t⁻¹) =
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          ∑ k ∈ κ, g k t * ENNReal.ofReal t⁻¹ := by
      rw [MeasureTheory.lintegral_finsetSum']
      intro k hk
      exact (hg k hk).mul hweight
    _ = ∫⁻ t in Set.Icc (1 : ℝ) 2,
          (∑ k ∈ κ, g k t) * ENNReal.ofReal t⁻¹ := by
      apply lintegral_congr_ae
      filter_upwards with t
      rw [Finset.sum_mul]
    _ ≤ ∫⁻ _t in Set.Icc (1 : ℝ) 2, B := by
      apply lintegral_mono_ae
      filter_upwards [hpoint, self_mem_ae_restrict measurableSet_Icc] with t ht hmem
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one hmem.1
      have htinv : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).mpr hmem.1
      calc
        (∑ k ∈ κ, g k t) * ENNReal.ofReal t⁻¹ ≤
            B * ENNReal.ofReal t⁻¹ := mul_le_mul_left ht _
        _ ≤ B * 1 := by
          simpa using mul_le_mul_right (ENNReal.ofReal_le_ofReal htinv) B
        _ = B := mul_one _
    _ = B := by
      rw [MeasureTheory.lintegral_const]
      simp [Real.volume_Icc]
      norm_num

theorem aux_shortLong_eLpNorm_sq_aemeasurable_of_joint {n : ℕ}
    (g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hjoint : AEStronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      g tx.1 tx.2) (volume.prod volume)) :
    AEMeasurable (fun t ↦ eLpNorm (g t) 2 volume ^ (2 : ℝ)) volume := by
  have hinner : AEMeasurable (fun t ↦ ∫⁻ x,
      ‖g t x‖ₑ ^ (2 : ℝ)) volume := by
    exact (hjoint.enorm.pow_const _).lintegral_prod_right
  refine hinner.congr ?_
  filter_upwards [] with t
  symm
  simpa [ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := g t)
      (p := (2 : NNReal)) (by norm_num))

theorem aux_shortLong_mainAuxOne_finset_log_lintegral {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryHypotheses psi)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (kappa : Finset ℤ) (hcard : kappa.card ≤ J + 1)
    (hmeas : ∀ k ∈ kappa,
      AEMeasurable (fun t ↦
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
          (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ))
        (volume.restrict (Set.Icc (1 : ℝ) 2))) :
    (∑ k ∈ kappa, ∫⁻ t in Set.Icc (1 : ℝ) 2,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
        (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ≤
      2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let F : ℤ → ℝ → ℝ≥0∞ := fun k t ↦
    eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun x ↦ psi x)
      (fun i x ↦ f.1 i x)) 2 volume ^ (2 : ℝ)
  refine aux_shortLong_finset_log_integral_le kappa F ?_
    (2 * ENNReal.ofReal (C_mainAuxOne n) *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) ?_
  · intro k hk
    simpa [F] using hmeas k hk
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    simpa [F] using aux_shortLong_mainAuxOne_finset_pointwise hn psi hpsi f J hJ kappa hcard t ht

theorem aux_shortLong_local_finset_bound {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (tau : SchwartzMap ℝ ℝ) (htau : (tau : ℝ → ℝ) = aux_tBump phi)
    (htauHyp : aux_mainAuxiliaryHypotheses tau)
    (J : ℕ) (hJ : 0 < J) (kappa : Finset ℤ) (hcard : kappa.card ≤ J + 1) :
    ∑ k ∈ kappa,
      (finiteVariationSeminorm
        (fun s : aux_dyadicInterval k ↦
          aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  have hterm (k : ℤ) :
      (finiteVariationSeminorm
        (fun s : aux_dyadicInterval k ↦
          aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
            (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    have h := aux_shortLong_local_variation_sq_le hn phi f J k
    rw [← htau] at h
    exact h
  calc
    (∑ k ∈ kappa,
      (finiteVariationSeminorm
        (fun s : aux_dyadicInterval k ↦
          aux_shortLong_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ)) ≤
        ∑ k ∈ kappa, ∫⁻ t in Set.Icc (1 : ℝ) 2,
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
            (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
          apply Finset.sum_le_sum
          intro k hk
          exact hterm k
    _ ≤ 2 * ENNReal.ofReal (C_mainAuxOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      apply aux_shortLong_mainAuxOne_finset_log_lintegral hn tau htauHyp f J hJ kappa hcard
      intro k hk
      let g : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x ↦
        twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ tau u)
          (fun i y ↦ f.1 i y) x
      have hjoint : AEStronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
          g tx.1 tx.2) (volume.prod volume) := by
        exact (aux_shortLong_joint_measurable_twistedAverageAtScale tau f.1 ((2 : ℝ) ^ k)
          |>.aestronglyMeasurable)
      have hsq := aux_shortLong_eLpNorm_sq_aemeasurable_of_joint g hjoint
      exact hsq.restrict


/--
**Lemma (Long and short variation).**

Let $J\ge 1$ and $\phi$ a Schwartz function.
Assume that the function $T\phi(s) = (s \phi(s))'$ satisfies (`main_aux1_supp`) and
(`auto:main-auxiliary-one-Fourier-derivative-assumption`).
Suppose that $A\in (0,\infty)$ is such that

$$
\|A_{t}(\phi)\|^2_{V_{2,J}(t\in 2^\mathbb{Z}; L^2)} \le A
$$

Then

$$
\|A_{t}(\phi)\|_{V_{2,J}(t\in (0,\infty); L^2)}^2 \le 2^4 C_{\text{lem:main\_aux1}} J^{\alpha(n)} +
2A.
$$

See also `Auto.mainAuxOne`.
-/
theorem shortLongFtcReduction {n : ℕ} (hn : 2 ≤ n) (phi : SchwartzMap ℝ ℝ)
    (hTphi : aux_mainAuxiliaryFourierHypotheses
      (Auto.aux_T (fun x : ℝ ↦ phi x)))
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J) (A : ℝ)
    (hApos : 0 < A) (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1) :
    aux_variationBound (16 * C_mainAuxOne n + 2 * A) (fun x ↦ phi x) f.1 := by
  have _ := hJ
  obtain ⟨tau, htau, htauHyp⟩ := aux_shortLong_tBump_auxHyp phi hTphi
  apply aux_shortLong_finish hn phi f A hApos (aux_C_mainAuxOne_nonneg n) hA
  intro J hJ kappa hcard
  exact aux_shortLong_local_finset_bound hn phi f tau htau htauHyp J hJ kappa hcard

/-- The constant in Lemma `Auto.mainBumpOneLongOne`. -/
noncomputable def C_mainBumpOneLongOne (n : ℕ) : ℝ :=
  (2 * C_uniPair) ^ 2 * C_mainAuxOne n

theorem aux_mainBumpOneLongOne_fourier_sub_of_integrable (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦ ((f x - g x : ℝ) : ℂ)) xi =
      FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ)) xi -
        FourierTransform.fourier (fun x : ℝ ↦ (g x : ℂ)) xi := by
  let e : ℝ → ℂ := fun x ↦ Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I)
  have he : Continuous e := by
    dsimp [e]
    fun_prop
  have he_bound : ∀ x, ‖e x‖ ≤ (1 : ℝ) := by
    intro x
    rw [show e x = Complex.exp (((-2 * Real.pi * x * xi : ℝ) : ℂ) * Complex.I) by rfl,
      Complex.norm_exp]
    norm_num
  have hf' : Integrable (fun x : ℝ ↦ e x * (f x : ℂ)) :=
    hf.ofReal.bdd_mul he.aestronglyMeasurable (ae_of_all _ he_bound)
  have hg' : Integrable (fun x : ℝ ↦ e x * (g x : ℂ)) :=
    hg.ofReal.bdd_mul he.aestronglyMeasurable (ae_of_all _ he_bound)
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ, e x * ((f x - g x : ℝ) : ℂ)) = _
  calc
    (∫ x : ℝ, e x * ((f x - g x : ℝ) : ℂ)) =
      ∫ x : ℝ, (e x * (f x : ℂ) - e x * (g x : ℂ)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        push_cast
        ring
    _ = (∫ x : ℝ, e x * (f x : ℂ)) - ∫ x : ℝ, e x * (g x : ℂ) :=
      integral_sub hf' hg'
    _ = _ := by rfl

theorem aux_mainBumpOneLongOne_window_profile_smooth (phi : SchwartzMap ℝ ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) := by
  let phiC : SchwartzMap ℝ ℂ :=
    phi.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hs : ContDiff ℝ (⊤ : ℕ∞) (FourierTransform.fourier phiC : ℝ → ℂ) :=
    (FourierTransform.fourier phiC).smooth (⊤ : ℕ∞)
  have hphiC : (phiC : ℝ → ℂ) = fun x : ℝ => (phi x : ℂ) := by
    funext x
    simp [phiC, SchwartzMap.postcompCLM_apply]
  rw [SchwartzMap.fourier_coe, hphiC] at hs
  exact hs

theorem aux_mainBumpOneLongOne_window_profile_deriv_bound (c : ℝ) (N : ℕ)
    (phi : SchwartzMap ℝ ℝ) (hwin : cnWindow c N phi)
    (m : ℕ) (hm : m ≤ N) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi‖ ≤ c := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))
  have hFsupp : Function.support F ⊆ Set.Icc (-1 : ℝ) 1 := by
    simpa [F] using hwin.2.2.1
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal hFsupp isClosed_Icc
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · change ‖iteratedDeriv m F xi‖ ≤ c
    exact hwin.2.2.2.2 xi hxi m hm
  · have hderivSupp : Function.support (iteratedDeriv m F) ⊆
        Set.Icc (-1 : ℝ) 1 :=
      (subset_tsupport _).trans
        ((Auto.aux_tsupport_iteratedDeriv_subset F m).trans
          hFtsupp)
    have hzero : iteratedDeriv m F xi = 0 := by
      apply Function.notMem_support.mp
      intro hsupp
      exact hxi (hderivSupp hsupp)
    rw [hzero, norm_zero]
    exact hwin.1.le

noncomputable def aux_mainBumpOneLongOne_psi
    (phi0 phi1 : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  (2 * C_uniPair)⁻¹ • (phi0 - phi1)

theorem aux_mainBumpOneLongOne_psi_fourier (phi0 phi1 : SchwartzMap ℝ ℝ)
    (xi : ℝ) :
    FourierTransform.fourier
      (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) xi =
      (((2 * C_uniPair)⁻¹ : ℝ) : ℂ) *
        (FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ)) xi -
          FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ)) xi) := by
  rw [show (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) =
      fun x => (((2 * C_uniPair)⁻¹ * (phi0 x - phi1 x) : ℝ) : ℂ) by
        funext x
        simp [aux_mainBumpOneLongOne_psi, smul_apply]
    ]
  rw [aux_mainAuxOne_fourier_real_const_mul,
    aux_mainBumpOneLongOne_fourier_sub_of_integrable _ _ phi0.integrable phi1.integrable]

theorem aux_mainBumpOneLongOne_psi_hypotheses (phi0 phi1 : SchwartzMap ℝ ℝ)
    (hpair : uniPair phi0 phi1) :
    aux_mainAuxiliaryHypotheses (aux_mainBumpOneLongOne_psi phi0 phi1) := by
  rcases hpair with ⟨h0, h1, hpair⟩
  constructor
  · intro xi hxi
    have hne := Function.mem_support.mp hxi
    rw [aux_mainBumpOneLongOne_psi_fourier] at hne
    have hdiff :
        FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ)) xi -
          FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ)) xi ≠ 0 :=
      (mul_ne_zero_iff.mp hne).2
    rw [Auto.aux_annulusOne]
    constructor
    · by_contra hnot
      push Not at hnot
      have hsmall : |xi| < 1 / 4 := by
        norm_num at hnot ⊢
        exact hnot
      have hmid : xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
        rw [mem_Icc]
        rw [abs_lt] at hsmall
        constructor <;> linarith [hsmall.1, hsmall.2]
      rw [h0.2.2.2.1 xi hmid, h1.2.2.2.1 xi hmid] at hdiff
      norm_num at hdiff
    · by_contra hnot
      push Not at hnot
      have hlarge : 4 < |xi| := by
        norm_num at hnot ⊢
        exact hnot
      have hout : xi ∉ Set.Icc (-1 : ℝ) 1 := by
        intro hmem
        have habs : |xi| ≤ 1 := abs_le.mpr hmem
        linarith
      have hzero0 : FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ)) xi = 0 := by
        apply Function.notMem_support.mp
        intro hsupp
        exact hout (h0.2.2.1 hsupp)
      have hzero1 : FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ)) xi = 0 := by
        apply Function.notMem_support.mp
        intro hsupp
        exact hout (h1.2.2.1 hsupp)
      rw [hzero0, hzero1] at hdiff
      exact hdiff (sub_self 0)
  · intro m hm xi
    let F0 : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi0 x : ℂ))
    let F1 : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi1 x : ℂ))
    have hF0 : ContDiff ℝ m F0 :=
      (aux_mainBumpOneLongOne_window_profile_smooth phi0).of_le
        (show (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr le_top)
    have hF1 : ContDiff ℝ m F1 :=
      (aux_mainBumpOneLongOne_window_profile_smooth phi1).of_le
        (show (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) by
          exact WithTop.coe_le_coe.mpr le_top)
    have h0bound : ‖iteratedDeriv m F0 xi‖ ≤ C_uniPair :=
      aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi0 h0 m
        (by simpa [N_uniPair] using Nat.le_of_lt hm) xi
    have h1bound : ‖iteratedDeriv m F1 xi‖ ≤ C_uniPair :=
      aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi1 h1 m
        (by simpa [N_uniPair] using Nat.le_of_lt hm) xi
    have hformula :
        (fun z : ℝ => FourierTransform.fourier
          (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) z) =
          fun z => (((2 * C_uniPair)⁻¹ : ℝ) : ℂ) * (F0 z - F1 z) := by
      funext z
      exact aux_mainBumpOneLongOne_psi_fourier phi0 phi1 z
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier
        (fun x : ℝ => (aux_mainBumpOneLongOne_psi phi0 phi1 x : ℂ)) z) xi‖ ≤ 1
    rw [hformula, iteratedDeriv_const_mul_field]
    change ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ) * iteratedDeriv m (F0 - F1) xi‖ ≤ 1
    rw [iteratedDeriv_sub hF0.contDiffAt hF1.contDiffAt]
    calc
      ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ) *
          (iteratedDeriv m F0 xi - iteratedDeriv m F1 xi)‖ ≤
          ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ)‖ *
            (‖iteratedDeriv m F0 xi‖ + ‖iteratedDeriv m F1 xi‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖(((2 * C_uniPair)⁻¹ : ℝ) : ℂ)‖ * (C_uniPair + C_uniPair) := by
        gcongr
      _ = 1 := by norm_num [C_uniPair]

theorem aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul {n : ℕ} (c : ℝ)
    (phi : ℝ → ℝ) (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (s : ℝ) :
    twistedAverageAtScale s (fun u => c * phi u) f =
      fun x => c * twistedAverageAtScale s phi f x := by
  funext x
  unfold twistedAverageAtScale
  unfold aux_twistedAverageAtScale aux_twistedAverage
  calc
    (∫ q : ℝ, s⁻¹ * (c * phi (s⁻¹ * q)) * ∏ i,
      f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))) =
        ∫ q : ℝ, c *
          (s⁻¹ * phi (s⁻¹ * q) * ∏ i,
            f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))) := by
          apply integral_congr_ae
          filter_upwards [] with q
          ring
    _ = _ := integral_const_mul _ _

theorem aux_mainBumpOneLongOne_twistedAverageAtScale_sub {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    twistedAverageAtScale s (fun u => phi0 u - phi1 u) (fun i x => f i x) =
      twistedAverageAtScale s (fun u => phi0 u) (fun i x => f i x) -
        twistedAverageAtScale s (fun u => phi1 u) (fun i x => f i x) := by
  funext x
  let P : ℝ → ℝ := fun q => ∏ i,
    f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  let B : ℝ := ∏ i, ‖(f i).toBoundedContinuousFunction‖
  have hPcont : Continuous P := by
    dsimp [P]
    fun_prop
  have hPbound : ∀ q : ℝ, ‖P q‖ ≤ B := by
    intro q
    rw [show ‖P q‖ = ∏ i, ‖f i (x + q • WithLp.toLp 2 (Pi.single i (1 : ℝ)))‖ by
      simp [P, norm_prod]]
    apply Finset.prod_le_prod
    · intro i hi
      exact norm_nonneg _
    · intro i hi
      exact BoundedContinuousFunction.norm_coe_le_norm
        (f i).toBoundedContinuousFunction _
  have hscaled0 : Integrable (fun q : ℝ => s⁻¹ * phi0 (s⁻¹ * q)) := by
    convert (phi0.integrable.comp_mul_left' (inv_ne_zero hs)).const_mul s⁻¹ using 1
  have hscaled1 : Integrable (fun q : ℝ => s⁻¹ * phi1 (s⁻¹ * q)) := by
    convert (phi1.integrable.comp_mul_left' (inv_ne_zero hs)).const_mul s⁻¹ using 1
  have hI0 : Integrable (fun q : ℝ =>
      (s⁻¹ * phi0 (s⁻¹ * q)) * P q) :=
    hscaled0.mul_bdd hPcont.aestronglyMeasurable (ae_of_all _ hPbound)
  have hI1 : Integrable (fun q : ℝ =>
      (s⁻¹ * phi1 (s⁻¹ * q)) * P q) :=
    hscaled1.mul_bdd hPcont.aestronglyMeasurable (ae_of_all _ hPbound)
  unfold twistedAverageAtScale
  unfold aux_twistedAverageAtScale aux_twistedAverage
  change (∫ q : ℝ, s⁻¹ * (phi0 (s⁻¹ * q) - phi1 (s⁻¹ * q)) * P q) = _
  calc
    (∫ q : ℝ, s⁻¹ * (phi0 (s⁻¹ * q) - phi1 (s⁻¹ * q)) * P q) =
      ∫ q : ℝ, ((s⁻¹ * phi0 (s⁻¹ * q)) * P q -
        (s⁻¹ * phi1 (s⁻¹ * q)) * P q) := by
        apply integral_congr_ae
        filter_upwards [] with q
        ring
    _ = _ := integral_sub hI0 hI1

theorem aux_mainBumpOneLongOne_psi_twistedAverageAtScale {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (s : ℝ) (hs : s ≠ 0) :
    twistedAverageAtScale s (fun u => aux_mainBumpOneLongOne_psi phi0 phi1 u)
        (fun i x => f i x) =
      fun x => (2 * C_uniPair)⁻¹ *
        (twistedAverageAtScale s (fun u => phi0 u) (fun i x => f i x) x -
          twistedAverageAtScale s (fun u => phi1 u) (fun i x => f i x) x) := by
  rw [show (fun u => aux_mainBumpOneLongOne_psi phi0 phi1 u) =
      fun u => (2 * C_uniPair)⁻¹ * (phi0 u - phi1 u) by
        funext u
        simp [aux_mainBumpOneLongOne_psi, smul_apply]
    ]
  rw [aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul,
    aux_mainBumpOneLongOne_twistedAverageAtScale_sub phi0 phi1 f s hs]
  rfl

theorem aux_mainBumpOneLongOne_eLpNorm_sq_const_mul {X : Type*} [MeasurableSpace X]
    (c : ℝ) (hc : 0 ≤ c) (g : X → ℝ) (mu : Measure X) :
    eLpNorm (fun x => c * g x) 2 mu ^ 2 =
      ENNReal.ofReal (c ^ 2) * eLpNorm g 2 mu ^ 2 := by
  change eLpNorm (c • g) 2 mu ^ 2 = _
  rw [eLpNorm_const_smul]
  have hnorm : ‖c‖ₑ = ENNReal.ofReal c := by
    change (↑‖c‖₊ : ℝ≥0∞) = ENNReal.ofReal c
    rw [ENNReal.ofReal]
    congr
    exact (Real.nnnorm_of_nonneg hc).trans (Real.toNNReal_of_nonneg hc).symm
  rw [hnorm, mul_pow, ← ENNReal.ofReal_pow hc]

/--
**Lemma.**

For every $J\ge1$ and every strictly increasing sequence of integers $(k_j)_{j\in[J)}$,

$$
\sum_{j\in[J)}\|A_{2^{k_j}}(\phi_0)-A_{2^{k_j}}(\phi_1)\|_2^2
\le C_{\text{lem:mainbump1\_long1}}J^{\alpha(n)},
$$

where

$$
C_{\text{lem:mainbump1\_long1}}
=(2C_{\text{Universal pair}})^2C_{\text{lem:main\_aux1}}.
$$

See also `Auto.mainBumpOneLongOne`,
`Auto.uniPair`,
`Auto.mainAuxOne`.
-/
theorem mainBumpOneLongOne {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (k : aux_dyadicChain J) :
    ∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_mainBumpOneLongOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  let c : ℝ := 2 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  let psi : SchwartzMap ℝ ℝ := aux_mainBumpOneLongOne_psi phi0 phi1
  have hpsi : aux_mainAuxiliaryHypotheses psi := by
    dsimp [psi]
    exact aux_mainBumpOneLongOne_psi_hypotheses phi0 phi1 hpair
  have hmain := mainAuxOne hn psi hpsi f 1 (by norm_num) J hJ k
  have hmain' :
      ∑ j : Fin J,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun x ↦ psi x) (fun i x ↦ f.1 i x)) 2 volume ^ 2 ≤
        ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    simpa using hmain
  have hpoint (j : Fin J) :
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x) =
        fun x ↦ c * twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y) x := by
    funext x
    have htw := congrFun (aux_mainBumpOneLongOne_psi_twistedAverageAtScale phi0 phi1 f
      ((2 : ℝ) ^ (k.1 j.castSucc)) (zpow_ne_zero _ (by norm_num))) x
    change twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
        (fun u ↦ psi u) (fun i y ↦ f.1 i y) x =
        c⁻¹ * (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
            (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x) at htw
    calc
      twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
        twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x =
          c * (c⁻¹ * (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
            (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
              (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)) := by
            field_simp [hc.ne']
      _ = c * twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y) x := by rw [← htw]
  have hterm (j : Fin J) :
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 =
      ENNReal.ofReal (c ^ 2) *
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y)) 2 volume ^ 2 := by
    rw [hpoint j]
    exact aux_mainBumpOneLongOne_eLpNorm_sq_const_mul c hc.le _ volume
  calc
    ∑ j : Fin J,
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
          2 volume ^ 2 =
        ∑ j : Fin J, ENNReal.ofReal (c ^ 2) *
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
            (fun u ↦ psi u) (fun i y ↦ f.1 i y)) 2 volume ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j
    _ = ENNReal.ofReal (c ^ 2) *
        ∑ j : Fin J, eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
          (fun u ↦ psi u) (fun i y ↦ f.1 i y)) 2 volume ^ 2 := by
          rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (c ^ 2) *
        (ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :=
      mul_le_mul_of_nonneg_left hmain' bot_le
    _ = ENNReal.ofReal (C_mainBumpOneLongOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [← mul_assoc]
      rw [← ENNReal.ofReal_mul (sq_nonneg c)]
      simp [C_mainBumpOneLongOne, c]

/--
**Lemma (constant $C_{\text{lem:mainbump1\_long1}}$).**

$$
C_{\text{lem:mainbump1\_long1}}<2^{605}.
$$

See also `Auto.mainBumpOneLongOne`.
-/
theorem constantMainBumpOneLongOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongOne n < (2 : ℝ) ^ 605 := by
  unfold C_mainBumpOneLongOne
  calc
    (2 * C_uniPair) ^ 2 * C_mainAuxOne n <
        (2 * C_uniPair) ^ 2 * (2 : ℝ) ^ 573 :=
      mul_lt_mul_of_pos_left (constantMainAuxiliaryOne hn) (by norm_num [C_uniPair])
    _ = (2 : ℝ) ^ 605 := by
      calc
        (2 * C_uniPair) ^ 2 * (2 : ℝ) ^ 573 =
            (2 : ℝ) ^ 32 * (2 : ℝ) ^ 573 := by norm_num [C_uniPair]
        _ = (2 : ℝ) ^ (32 + 573) := by rw [← pow_add]
        _ = (2 : ℝ) ^ 605 := by norm_num

/-- The constant in Lemma `Auto.mainBumpOneLongTwo`. -/
noncomputable def C_mainBumpOneLongTwo (n : ℕ) : ℝ :=
  2 * C_inductPositiveTermsReductionNonWhitneySkip n

/-- Extend all finite scales in a dyadic chain to a spaced sequence. -/
theorem aux_mainBumpOneLongTwo_extend_dyadic_chain (J : ℕ)
    (k : aux_dyadicChain J) :
    ∃ a : ℤ → ℝ, SpacedSequence a ∧
      ∀ j : Fin (J + 1), a (j : ℤ) = (2 : ℝ) ^ (k.1 j) := by
  let b : ℤ → ℝ := fun z => if hz : 0 ≤ z ∧ z < (J + 1 : ℕ) then
    (2 : ℝ) ^ (k.1 (⟨z.toNat, by omega⟩ : Fin (J + 1))) else 1
  obtain ⟨a, ha, hrestrict, hlarge, hsmall⟩ :=
    (extensionOfSequences (J + 1) (by omega) b (by
      intro z hz0 hzJ
      rw [show b z = (2 : ℝ) ^ (k.1 (⟨z.toNat, by omega⟩ : Fin (J + 1))) by
        dsimp [b]
        rw [dif_pos ⟨hz0, by omega⟩]]
      exact zpow_pos (by norm_num) _)
      (by
        intro z hz0 hznext
        have hzJ : z < (J + 1 : ℕ) := by omega
        have hznextJ : z + 1 < (J + 1 : ℕ) := hznext
        let j : Fin J := ⟨z.toNat, by omega⟩
        have hsucc :
            (⟨(z + 1).toNat, by omega⟩ : Fin (J + 1)) = j.succ := by
          apply Fin.ext
          dsimp [j]
          omega
        have hstrict : k.1 j.castSucc < k.1 j.succ := k.2 Fin.castSucc_lt_succ
        have hexp : k.1 j.castSucc + 1 ≤ k.1 j.succ :=
          Int.add_one_le_iff.mpr (by simpa using hstrict)
        have hbz : b z = (2 : ℝ) ^ (k.1 j.castSucc) := by
          dsimp [b]
          rw [dif_pos ⟨hz0, by omega⟩]
          congr 3
        have hbnext : b (z + 1) = (2 : ℝ) ^ (k.1 j.succ) := by
          dsimp [b]
          rw [dif_pos ⟨by omega, hznextJ⟩]
          rw [hsucc]
        rw [hbz, hbnext]
        calc
          2 * (2 : ℝ) ^ (k.1 j.castSucc) =
              (2 : ℝ) ^ (k.1 j.castSucc + 1) := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            norm_num
            ring
          _ ≤ (2 : ℝ) ^ (k.1 j.succ) :=
            (zpow_le_zpow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mpr hexp)).exists
  refine ⟨a, ha, ?_⟩
  intro j
  rw [hrestrict (j : ℤ) (by omega) (by omega)]
  dsimp [b]
  split
  · congr 3
  · rename_i h
    exfalso
    apply h
    omega

theorem aux_mainBumpOneLongTwo_sum_range_two_mul {M : Type*} [AddCommMonoid M]
    (q : ℕ → M) (K : ℕ) :
    (∑ j ∈ Finset.range (2 * K), q j) =
      (∑ j ∈ Finset.range K, q (2 * j)) +
        ∑ j ∈ Finset.range K, q (2 * j + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp only [Nat.mul_succ, Finset.sum_range_succ, ih]
      ac_rfl

theorem aux_mainBumpOneLongTwo_sum_range_two_mul_add_one
    {M : Type*} [AddCommMonoid M] (q : ℕ → M) (K : ℕ) :
    (∑ j ∈ Finset.range (2 * K + 1), q j) =
      (∑ j ∈ Finset.range (K + 1), q (2 * j)) +
        ∑ j ∈ Finset.range K, q (2 * j + 1) := by
  rw [Finset.sum_range_succ, aux_mainBumpOneLongTwo_sum_range_two_mul]
  rw [Finset.sum_range_succ]
  ac_rfl

theorem aux_mainBumpOneLongTwo_nonWhitneySkip_prefix {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (N : ℕ) (hN : 0 < N) :
    ∑ j : Fin N,
      eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
        ENNReal.ofReal ((N : ℝ) ^ variationExponent n) := by
  classical
  let psi : Fin N → SchwartzMap ℝ ℝ := fun j =>
    aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ))) (ha (2 * (j : ℤ))).1 -
      aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
        (ha (2 * (j : ℤ) + 1)).1
  obtain ⟨F, hFnorm, hsum⟩ := aToLambda_fin_sum (n := n) (J := N) (by omega) psi f.1
  let Fnorm : NormalizedFunctionTuple n := ⟨F, by
    intro i
    convert (hFnorm i ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2))).trans
      (f.2 i) using 1; norm_num⟩
  let M : KernelSequence 1 := aux_nonWhitneySkipSequence phi0 phi1 a
  have hMbound : kernelSequenceSeminorm n 1 (by omega) (by omega) M ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) := by
    dsimp [M]
    exact inductPositiveTermsReductionNonWhitneySkip hn a ha phi0 phi1 hpair
  have hprefix := aux_mainAuxOne_prefix_from_seminorm hn M
    (C_inductPositiveTermsReductionNonWhitneySkip n) hMbound N hN Fnorm
  have hleft :
      (∑ j : Fin N,
        eLpNorm
          (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
                (fun i y ↦ f.1 i y) x)
          2 volume ^ 2) =
      ∑ j : Fin N,
        eLpNorm (twistedAverage (psi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [psi]
    change eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 =
      eLpNorm
        (twistedAverage
          ((fun x ↦ aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ)))
              (ha (2 * (j : ℤ))).1 x) -
            (fun x ↦ aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
              (ha (2 * (j : ℤ) + 1)).1 x))
          (fun i x ↦ f.1 i x)) 2 volume ^ 2
    rw [aux_twistedAverage_sub_of_memLp hn f.1
      (aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ))) (ha (2 * (j : ℤ))).1)
      (aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
        (ha (2 * (j : ℤ) + 1)).1)
      ((aux_mainAuxOne_windowSchwartz phi0 (a (2 * (j : ℤ)))
        (ha (2 * (j : ℤ))).1).memLp 2)
      ((aux_mainAuxOne_windowSchwartz phi1 (a (2 * (j : ℤ) + 1))
        (ha (2 * (j : ℤ) + 1)).1).memLp 2)]
    rw [aux_mainAuxOne_twistedAverage_window, aux_mainAuxOne_twistedAverage_window]
    rfl
  have hkernel :
      (fun y : RealVector 1 × RealVector 1 =>
        ∑ j : Fin N, psi j (y.1 0) * psi j (y.2 0)) =
      fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y := by
    funext y
    let g : ℕ → ℝ := fun r => if hr : r < N then M (r : ℤ) y else 0
    calc
      (∑ j : Fin N, psi j (y.1 0) * psi j (y.2 0)) =
          ∑ r ∈ Finset.range N, g r := by
            rw [← Fin.sum_univ_eq_sum_range g N]
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [g]
            rw [if_pos j.2]
            simp only [M, psi, aux_nonWhitneySkipSequence, aux_liftPlaneKernel,
              tensorSquare, sub_apply]
            have h0 (x : ℝ) := aux_mainAuxOne_windowSchwartz_apply phi0
              (a (2 * (j : ℤ))) (ha (2 * (j : ℤ))).1 x
            have h1 (x : ℝ) := aux_mainAuxOne_windowSchwartz_apply phi1
              (a (2 * (j : ℤ) + 1)) (ha (2 * (j : ℤ) + 1)).1 x
            rw [h0 (y.1 0), h1 (y.1 0), h0 (y.2 0), h1 (y.2 0)]
      _ = ∑ r ∈ Finset.range N, M (r : ℤ) y := by
            apply Finset.sum_congr rfl
            intro r hr
            dsimp [g]
            rw [if_pos (Finset.mem_range.mp hr)]
  have hsum' :
      (∑ j : Fin N,
        eLpNorm (twistedAverage (psi j) (fun i x ↦ f.1 i x)) 2 volume ^ 2) =
      ENNReal.ofReal
        (prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y)
          (fun i x ↦ F i x)) := by
    rw [hsum, hkernel]
  calc
    ∑ j : Fin N,
        eLpNorm
          (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
                (fun i y ↦ f.1 i y) x)
          2 volume ^ 2 =
        ENNReal.ofReal
          (prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y)
            (fun i x ↦ F i x)) := hleft.trans hsum'
    _ ≤ ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range N, M (j : ℤ) y)
          (fun i x ↦ F i x)| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
        ENNReal.ofReal ((N : ℝ) ^ variationExponent n) := by
      simpa [Fnorm] using hprefix

theorem aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (N J : ℕ) (hNJ : N ≤ J) :
    ∑ j : Fin N,
      eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (j : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (j : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  by_cases hN : N = 0
  · subst N
    simp
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hprefix := aux_mainBumpOneLongTwo_nonWhitneySkip_prefix hn a ha phi0 phi1 hpair f N hNpos
    have hpow : (N : ℝ) ^ variationExponent n ≤ (J : ℝ) ^ variationExponent n :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hNJ)
        (aux_shortLong_variationExponent_nonneg hn)
    have hpowENN : ENNReal.ofReal ((N : ℝ) ^ variationExponent n) ≤
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := ENNReal.ofReal_le_ofReal hpow
    exact hprefix.trans (mul_le_mul_of_nonneg_left hpowENN bot_le)

theorem aux_mainBumpOneLongTwo_chain_pair_eq {n : ℕ} (a : ℤ → ℝ) (J : ℕ)
    (k : aux_dyadicChain J)
    (ha : ∀ j : Fin (J + 1), a (j : ℤ) = (2 : ℝ) ^ (k.1 j))
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (j : Fin J) :
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume ^ 2 =
    eLpNorm
      (fun x ↦ twistedAverageAtScale (a (j : ℤ)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale (a ((j : ℤ) + 1)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume ^ 2 := by
  rw [← ha j.castSucc, ← ha j.succ]
  congr 5

noncomputable def aux_mainBumpOneLongTwo_pairEnergy {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (a : ℤ → ℝ) (m : ℕ) : ℝ≥0∞ :=
  eLpNorm
    (fun x ↦ twistedAverageAtScale (a (m : ℤ)) (fun u ↦ phi0 u)
          (fun i y ↦ f.1 i y) x -
        twistedAverageAtScale (a ((m : ℤ) + 1)) (fun u ↦ phi1 u)
          (fun i y ↦ f.1 i y) x)
    2 volume ^ 2

theorem aux_mainBumpOneLongTwo_pairEnergy_even {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (a : ℤ → ℝ) (r : ℕ) :
    aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r) =
      eLpNorm
        (fun x ↦ twistedAverageAtScale (a (2 * (r : ℤ))) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (a (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 := by
  unfold aux_mainBumpOneLongTwo_pairEnergy
  congr 5

theorem aux_mainBumpOneLongTwo_pairEnergy_odd {n : ℕ}
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (a : ℤ → ℝ) (r : ℕ) :
    aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) =
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((fun z => a (z + 1)) (2 * (r : ℤ)))
              (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((fun z => a (z + 1)) (2 * (r : ℤ) + 1))
              (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 := by
  unfold aux_mainBumpOneLongTwo_pairEnergy
  congr 5

theorem aux_mainBumpOneLongTwo_chain_pairEnergy_eq {n : ℕ} (a : ℤ → ℝ) (J : ℕ)
    (k : aux_dyadicChain J)
    (ha : ∀ j : Fin (J + 1), a (j : ℤ) = (2 : ℝ) ^ (k.1 j))
    (phi0 phi1 : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n)
    (j : Fin J) :
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume ^ 2 = aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a j := by
  exact aux_mainBumpOneLongTwo_chain_pair_eq a J k ha phi0 phi1 f j

/--
**Lemma.**

For every $J\ge 1$ and every strictly increasing sequence of integers $(m_j)_{j\in[J+1)}$,

$$
\sum_{j\in[J)} \|
A_{2^{m_{j}}}(\phi_0)-A_{2^{m_{j+1}}}(\phi_1) \|_{2}^2  \le C_{\text{lem:mainbump1\_long2}}
J^{\alpha(n)},
$$

where $C_{\text{lem:mainbump1\_long2}}=2 C_{\text{induct positive terms - reduction variant,
non-Whitney, skip terms}}$.

See also `Auto.mainBumpOneLongTwo`,
`Auto.inductPositiveTermsReductionNonWhitneySkip`.
-/
theorem mainBumpOneLongTwo {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J)
    (k : aux_dyadicChain J) :
    ∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
              (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
              (fun i y ↦ f.1 i y) x)
        2 volume ^ 2 ≤
      ENNReal.ofReal (C_mainBumpOneLongTwo n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  obtain ⟨a, ha, hrestrict⟩ := aux_mainBumpOneLongTwo_extend_dyadic_chain J k
  have hleft :
      (∑ j : Fin J,
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ))
                (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
          2 volume ^ 2) =
        ∑ m ∈ Finset.range J, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a m := by
    calc
      (∑ j : Fin J,
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc))
                (fun u ↦ phi0 u) (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ))
                (fun u ↦ phi1 u) (fun i y ↦ f.1 i y) x)
          2 volume ^ 2) =
          ∑ j : Fin J, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact aux_mainBumpOneLongTwo_chain_pairEnergy_eq a J k hrestrict phi0 phi1 f j
      _ = ∑ m ∈ Finset.range J, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a m := by
            rw [← Fin.sum_univ_eq_sum_range (aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a) J]
  rw [hleft]
  rcases Nat.even_or_odd' J with ⟨K, rfl | rfl⟩
  · rw [aux_mainBumpOneLongTwo_sum_range_two_mul]
    have hevenEq :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
          ∑ r : Fin K,
            eLpNorm
              (fun x ↦ twistedAverageAtScale (a (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (a (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
            ∑ r : Fin K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) K]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_even phi0 phi1 f a r
    have heven :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hevenEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn a ha phi0 phi1 hpair f K
        (2 * K) (by omega)
    let b : ℤ → ℝ := fun z => a (z + 1)
    have hb : SpacedSequence b := by
      dsimp [b]
      exact shift_mem_A ha 1
    have hoddEq :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
          ∑ r : Fin K,
            eLpNorm
              (fun x ↦ twistedAverageAtScale (b (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (b (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
            ∑ r : Fin K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) K]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_odd phi0 phi1 f a r
    have hodd :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hoddEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn b hb phi0 phi1 hpair f K
        (2 * K) (by omega)
    calc
      (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) +
          ∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) ≤
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n)) +
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n)) := add_le_add heven hodd
      _ = ENNReal.ofReal (C_mainBumpOneLongTwo n) *
          ENNReal.ofReal (((2 * K : ℕ) : ℝ) ^ variationExponent n) := by
            rw [C_mainBumpOneLongTwo, ENNReal.ofReal_mul (by norm_num)]
            norm_num
            ring
  · rw [aux_mainBumpOneLongTwo_sum_range_two_mul_add_one]
    have hevenEq :
        (∑ r ∈ Finset.range (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
          ∑ r : Fin (K + 1),
            eLpNorm
              (fun x ↦ twistedAverageAtScale (a (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (a (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) =
            ∑ r : Fin (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) (K + 1)]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_even phi0 phi1 f a r
    have heven :
        (∑ r ∈ Finset.range (K + 1),
          aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hevenEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn a ha phi0 phi1 hpair f (K + 1)
        (2 * K + 1) (by omega)
    let b : ℤ → ℝ := fun z => a (z + 1)
    have hb : SpacedSequence b := by
      dsimp [b]
      exact shift_mem_A ha 1
    have hoddEq :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
          ∑ r : Fin K,
            eLpNorm
              (fun x ↦ twistedAverageAtScale (b (2 * (r : ℤ))) (fun u ↦ phi0 u)
                    (fun i y ↦ f.1 i y) x -
                  twistedAverageAtScale (b (2 * (r : ℤ) + 1)) (fun u ↦ phi1 u)
                    (fun i y ↦ f.1 i y) x)
              2 volume ^ 2 := by
      calc
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) =
            ∑ r : Fin K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun r => aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) K]
        _ = _ := by
              apply Finset.sum_congr rfl
              intro r hr
              exact aux_mainBumpOneLongTwo_pairEnergy_odd phi0 phi1 f a r
    have hodd :
        (∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1)) ≤
          ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n) := by
      rw [hoddEq]
      exact aux_mainBumpOneLongTwo_nonWhitneySkip_prefix_le hn b hb phi0 phi1 hpair f K
        (2 * K + 1) (by omega)
    calc
      (∑ r ∈ Finset.range (K + 1), aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r)) +
          ∑ r ∈ Finset.range K, aux_mainBumpOneLongTwo_pairEnergy phi0 phi1 f a (2 * r + 1) ≤
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n)) +
          (ENNReal.ofReal (C_inductPositiveTermsReductionNonWhitneySkip n) *
            ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n)) :=
              add_le_add heven hodd
      _ = ENNReal.ofReal (C_mainBumpOneLongTwo n) *
          ENNReal.ofReal (((2 * K + 1 : ℕ) : ℝ) ^ variationExponent n) := by
            rw [C_mainBumpOneLongTwo, ENNReal.ofReal_mul (by norm_num)]
            norm_num
            ring

/--
**Lemma (constant $C_{\text{lem:mainbump1\_long2}}$).**

$$
C_{\text{lem:mainbump1\_long2}}<\tfrac89 2^{543}<2^{543}.
$$

See also `Auto.mainBumpOneLongTwo`.
-/
theorem constantMainBumpOneLongTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongTwo n < (8 / 9 : ℝ) * (2 : ℝ) ^ 543 := by
  unfold C_mainBumpOneLongTwo
  calc
    2 * C_inductPositiveTermsReductionNonWhitneySkip n <
        2 * ((8 / 9 : ℝ) * (2 : ℝ) ^ 542) :=
      mul_lt_mul_of_pos_left (constantNonWhitneySkipReduction hn) (by norm_num)
    _ = (8 / 9 : ℝ) * (2 : ℝ) ^ 543 := by
      calc
        2 * ((8 / 9 : ℝ) * (2 : ℝ) ^ 542) =
            (8 / 9 : ℝ) * ((2 : ℝ) ^ 1 * (2 : ℝ) ^ 542) := by
              set_option exponentiation.threshold 1000 in
                ring
        _ = (8 / 9 : ℝ) * (2 : ℝ) ^ (1 + 542) := by rw [← pow_add]
        _ = (8 / 9 : ℝ) * (2 : ℝ) ^ 543 := by norm_num

/-- The constant in Lemma `Auto.mainBumpOneLong`. -/
noncomputable def C_mainBumpOneLong (n : ℕ) : ℝ :=
  2 * (C_mainBumpOneLongOne n + C_mainBumpOneLongTwo n)

theorem aux_mainBumpOneLong_average_aestronglyMeasurable {n : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (t : ℝ) :
    AEStronglyMeasurable
      (twistedAverageAtScale t (fun s ↦ phi s) (fun i x ↦ f i x)) volume := by
  let E := EuclideanSpace ℝ (Fin n)
  let K : E × ℝ → ℝ := fun z ↦
    t⁻¹ * phi (t⁻¹ * z.2) * ∏ i,
      f i (z.1 + z.2 • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  have hKcont : Continuous K := by
    dsimp [K]
    fun_prop
  have hKmeas : AEStronglyMeasurable K ((volume : Measure E).prod volume) :=
    hKcont.aestronglyMeasurable
  have hI : AEStronglyMeasurable (fun x : E ↦ ∫ s : ℝ, K (x, s)) volume := by
    simpa only [Measure.volume_eq_prod] using hKmeas.integral_prod_right'
  apply hI.congr
  filter_upwards [] with x
  rfl

theorem aux_mainBumpOneLong_ennreal_add_sq_le (u v : ℝ≥0∞) :
    (u + v) ^ (2 : ℝ) ≤ 2 * (u ^ (2 : ℝ) + v ^ (2 : ℝ)) := by
  simp only [ENNReal.rpow_two]
  by_cases hu : u = ∞
  · simp [hu]
  by_cases hv : v = ∞
  · simp [hv]
  have hu2 : u ^ (2 : ℕ) ≠ ∞ := ENNReal.pow_ne_top hu
  have hv2 : v ^ (2 : ℕ) ≠ ∞ := ENNReal.pow_ne_top hv
  have hsum : u ^ (2 : ℕ) + v ^ (2 : ℕ) ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hu2, hv2⟩
  have hrhs : 2 * (u ^ (2 : ℕ) + v ^ (2 : ℕ)) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hsum
  rw [← ENNReal.toReal_le_toReal (by simp [hu, hv]) hrhs,
    ENNReal.toReal_pow, ENNReal.toReal_add hu hv,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add hu2 hv2, ENNReal.toReal_pow,
    ENNReal.toReal_pow]
  nlinarith [sq_nonneg (u.toReal - v.toReal)]

theorem aux_mainBumpOneLong_one_nonneg (n : ℕ) :
    0 ≤ C_mainBumpOneLongOne n := by
  unfold C_mainBumpOneLongOne
  exact mul_nonneg (sq_nonneg _) (aux_C_mainAuxOne_nonneg n)

theorem aux_mainBumpOneLong_two_nonneg (n : ℕ) :
    0 ≤ C_mainBumpOneLongTwo n := by
  have hdiagonal : 0 ≤ C_diagonalBandReduction := by
    unfold C_diagonalBandReduction
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) aux_CincreaseDataReduction_nonneg)
  have hnonWhitney : 0 ≤ C_inductPositiveTermsReductionNonWhitney := by
    unfold C_inductPositiveTermsReductionNonWhitney
    apply add_nonneg
    · norm_num [C_oneScaleEstimateWindow, C_uniPair]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) hdiagonal
  have hskip : 0 ≤ C_inductPositiveTermsReductionNonWhitneySkip n := by
    unfold C_inductPositiveTermsReductionNonWhitneySkip
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hnonWhitney
  unfold C_mainBumpOneLongTwo
  exact mul_nonneg (by norm_num) hskip

theorem aux_mainBumpOneLong_shifted_dyadic_chain {J : ℕ}
    (k : aux_dyadicChain J) :
    ∃ q : aux_dyadicChain J, ∀ j : Fin J, q.1 j.castSucc = k.1 j.succ := by
  let qfun : Fin (J + 1) → ℤ :=
    Fin.lastCases (k.1 (Fin.last J) + 1) (fun j : Fin J ↦ k.1 j.succ)
  have hqfun : StrictMono qfun := by
    intro i j hij
    by_cases hj : j = Fin.last J
    · subst j
      change i.1 < J at hij
      let i' : Fin J := ⟨i.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      rw [hi]
      simp only [qfun, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hle : k.1 i'.succ ≤ k.1 (Fin.last J) :=
        k.2.monotone (Fin.le_last i'.succ)
      omega
    · have hjlt : j < Fin.last J := Fin.lt_last_iff_ne_last.mpr hj
      change i.1 < j.1 at hij
      change j.1 < J at hjlt
      let i' : Fin J := ⟨i.1, by omega⟩
      let j' : Fin J := ⟨j.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      have hj' : j = j'.castSucc := by rfl
      rw [hi, hj']
      simp only [qfun, Fin.lastCases_castSucc]
      apply k.2
      exact Fin.succ_lt_succ_iff.mpr (by simpa [i', j'] using hij)
  refine ⟨⟨qfun, hqfun⟩, ?_⟩
  intro j
  simp [qfun]

/--
**Lemma.**

Let $J\ge 1$. Then

$$
\|A_{t}(\phi_0)\|^2_{V_{2,J}(t\in 2^\mathbb{Z}; L^2)}  \le C_{\text{lem:mainbump1\_long}}
J^{\alpha(n)},
$$

where $C_{\text{lem:mainbump1\_long}}=2(C_{\text{lem:mainbump1\_long2}} +
C_{\text{lem:mainbump1\_long1}})$.

See also `Auto.mainBumpOneLong`,
`Auto.mainBumpOneLongTwo`,
`Auto.mainBumpOneLongOne`.
-/
theorem mainBumpOneLong {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) :
    aux_dyadicVariationBound (C_mainBumpOneLong n) (fun x ↦ phi0 x) f.1 := by
  unfold aux_dyadicVariationBound aux_dyadicJumpEnergy twistedDyadicJumpEnergy
  intro J hJ k
  let P : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  let a : Fin J → ℝ≥0∞ := fun j ↦
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume
  let b : Fin J → ℝ≥0∞ := fun j ↦
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
            (fun i y ↦ f.1 i y) x)
      2 volume
  let d : Fin J → ℝ≥0∞ := fun j ↦
    eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
            (fun i y ↦ f.1 i y) x)
      2 volume
  have htri (j : Fin J) : d j ≤ a j + b j := by
    dsimp [a, b, d]
    calc
      eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
                (fun i y ↦ f.1 i y) x)
          2 volume =
          eLpNorm
            ((fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi0 u)
                  (fun i y ↦ f.1 i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
                  (fun i y ↦ f.1 i y) x) -
              (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u ↦ phi0 u)
                  (fun i y ↦ f.1 i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u ↦ phi1 u)
                  (fun i y ↦ f.1 i y) x))
            2 volume := by
              congr 1
              funext x
              simp only [Pi.sub_apply]
              ring
      _ ≤ _ := eLpNorm_sub_le
        ((aux_mainBumpOneLong_average_aestronglyMeasurable phi0 f.1
          ((2 : ℝ) ^ (k.1 j.succ))).sub
          (aux_mainBumpOneLong_average_aestronglyMeasurable phi1 f.1
            ((2 : ℝ) ^ (k.1 j.succ))))
        ((aux_mainBumpOneLong_average_aestronglyMeasurable phi0 f.1
          ((2 : ℝ) ^ (k.1 j.castSucc))).sub
          (aux_mainBumpOneLong_average_aestronglyMeasurable phi1 f.1
            ((2 : ℝ) ^ (k.1 j.succ))))
        (by norm_num)
  have hpoint (j : Fin J) : d j ^ 2 ≤
      2 * (a j ^ 2 + b j ^ 2) := by
    calc
      d j ^ 2 ≤ (a j + b j) ^ 2 :=
        pow_le_pow_left₀ bot_le (htri j) 2
      _ ≤ 2 * (a j ^ 2 + b j ^ 2) := by
        simpa [ENNReal.rpow_two] using aux_mainBumpOneLong_ennreal_add_sq_le (a j) (b j)
  have hsum : (∑ j : Fin J, d j ^ 2) ≤
      2 * (∑ j : Fin J, a j ^ 2) +
        2 * (∑ j : Fin J, b j ^ 2) := by
    calc
      (∑ j : Fin J, d j ^ 2) ≤
          ∑ j : Fin J, 2 * (a j ^ 2 + b j ^ 2) := by
            exact Finset.sum_le_sum fun j _ ↦ hpoint j
      _ = 2 * (∑ j : Fin J, a j ^ 2) +
          2 * (∑ j : Fin J, b j ^ 2) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  obtain ⟨q, hq⟩ := aux_mainBumpOneLong_shifted_dyadic_chain k
  have hOne : (∑ j : Fin J, a j ^ 2) ≤
      ENNReal.ofReal (C_mainBumpOneLongOne n) * P := by
    dsimp [a, P]
    simpa [hq] using mainBumpOneLongOne hn phi0 phi1 hpair f J hJ q
  have hTwo : (∑ j : Fin J, b j ^ 2) ≤
      ENNReal.ofReal (C_mainBumpOneLongTwo n) * P := by
    dsimp [b, P]
    simpa using mainBumpOneLongTwo hn phi0 phi1 hpair f J hJ k
  have hC1 : 0 ≤ C_mainBumpOneLongOne n := aux_mainBumpOneLong_one_nonneg n
  have hC2 : 0 ≤ C_mainBumpOneLongTwo n := aux_mainBumpOneLong_two_nonneg n
  change (∑ j : Fin J, d j ^ 2) ≤
    ENNReal.ofReal (C_mainBumpOneLong n) * P
  calc
    (∑ j : Fin J, d j ^ 2) ≤
        2 * (∑ j : Fin J, a j ^ 2) +
          2 * (∑ j : Fin J, b j ^ 2) := hsum
    _ ≤ 2 * (ENNReal.ofReal (C_mainBumpOneLongOne n) * P) +
          2 * (ENNReal.ofReal (C_mainBumpOneLongTwo n) * P) := by
            gcongr
    _ = (2 * ENNReal.ofReal (C_mainBumpOneLongOne n) +
          2 * ENNReal.ofReal (C_mainBumpOneLongTwo n)) * P := by ring
    _ = ENNReal.ofReal (C_mainBumpOneLong n) * P := by
      unfold C_mainBumpOneLong
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.ofReal_add]
      · norm_num
        ring
      · exact hC1
      · exact hC2

theorem aux_mainBumpOneLong_one_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLongOne n < (1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 := by
  unfold C_mainBumpOneLongOne
  calc
    (2 * C_uniPair) ^ 2 * C_mainAuxOne n <
        (2 * C_uniPair) ^ 2 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) :=
      mul_lt_mul_of_pos_left (aux_constantMainAuxOne_sharp hn)
        (by norm_num [C_uniPair])
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 := by
      calc
        (2 * C_uniPair) ^ 2 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) =
            (2 : ℝ) ^ 32 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) := by
              norm_num [C_uniPair]
        _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 32 * (2 : ℝ) ^ 573) := by
              set_option exponentiation.threshold 1000 in
                ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 := by
          rw [← pow_add]

/--
**Lemma (constant $C_{\text{lem:mainbump1\_long}}$).**

$$
C_{\text{lem:mainbump1\_long}}<\tfrac{11}{16}2^{606}<2^{606}.
$$

See also `Auto.mainBumpOneLong`.
-/
theorem constantMainBumpOneLong {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOneLong n < (11 / 16 : ℝ) * (2 : ℝ) ^ 606 := by
  have h1 := aux_mainBumpOneLong_one_sharp hn
  have h2 := constantMainBumpOneLongTwo hn
  have h605 : (2 : ℝ) ^ 605 = (2 : ℝ) ^ 62 * (2 : ℝ) ^ 543 := by
    rw [← pow_add]
  have h606 : (2 : ℝ) ^ 606 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 543 := by
    rw [← pow_add]
  have h63 : (2 : ℝ) ^ 63 = 2 * (2 : ℝ) ^ 62 := by
    rw [show 63 = 1 + 62 by norm_num, pow_add]
    norm_num
  have hcore : (1397 / 2048 : ℝ) * (2 : ℝ) ^ 63 + 16 / 9 <
      (11 / 16 : ℝ) * (2 : ℝ) ^ 63 := by
    set_option exponentiation.threshold 1000 in
      norm_num
  unfold C_mainBumpOneLong
  calc
    2 * (C_mainBumpOneLongOne n + C_mainBumpOneLongTwo n) <
        2 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 605 +
          (8 / 9 : ℝ) * (2 : ℝ) ^ 543) :=
      mul_lt_mul_of_pos_left (add_lt_add h1 h2) (by norm_num)
    _ = ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 63 + 16 / 9) * (2 : ℝ) ^ 543 := by
      rw [h605, h63]
      set_option exponentiation.threshold 1000 in
        ring
    _ < ((11 / 16 : ℝ) * (2 : ℝ) ^ 63) * (2 : ℝ) ^ 543 :=
      mul_lt_mul_of_pos_right hcore (by positivity)
    _ = (11 / 16 : ℝ) * (2 : ℝ) ^ 606 := by
      rw [h606]
      set_option exponentiation.threshold 1000 in
        ring

/-- The constant in Lemma `Auto.mainBumpOne`. -/
noncomputable def C_mainBumpOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 4 * (3 * C_uniPair) ^ 2 * C_mainAuxOne n +
    2 * C_mainBumpOneLong n

/-! Private Fourier and scalar-normalization infrastructure for `mainBumpOne`. -/

theorem aux_mainBumpOne_T_cast_eq (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    (fun x : ℝ ↦ (Auto.aux_sd_T f x : ℂ)) =
      Auto.aux_T (fun x : ℝ ↦ (f x : ℂ)) := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => y * f y) x := by
    exact ((contDiff_id.mul hf).contDiffAt).differentiableAt (by norm_num)
  have hcast :
      deriv (fun y : ℝ => ((y * f y : ℝ) : ℂ)) x =
        ((deriv (fun y : ℝ => y * f y) x : ℝ) : ℂ) := by
    simpa using ((hasDerivAt_const x Complex.ofRealCLM).clm_apply hdiff.hasDerivAt).deriv
  have hfun : (fun y : ℝ => ((y * f y : ℝ) : ℂ)) =
      Auto.multiplicationOperatorX
        (fun y : ℝ => (f y : ℂ)) := by
    funext y
    simp [Auto.multiplicationOperatorX]
  unfold Auto.aux_sd_T
    Auto.aux_T
  rw [← hfun, hcast]

theorem aux_mainBumpOne_T_fourier_formula (phi : SchwartzMap ℝ ℝ)
    (m : ℕ) (xi : ℝ) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ))) xi =
      - ((m : ℂ) * iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ ↦ (phi x : ℂ))) xi +
          (xi : ℂ) * iteratedDeriv (m + 1)
            (FourierTransform.fourier (fun x : ℝ ↦ (phi x : ℂ))) xi) := by
  let phiC : SchwartzMap ℝ ℂ :=
    phi.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hphiC : (phiC : ℝ → ℂ) = fun x : ℝ => (phi x : ℂ) := by
    funext x
    simp [phiC, SchwartzMap.postcompCLM_apply]
  have hsmooth : ContDiff ℝ 1 (fun x : ℝ => phi x) := by
    exact phi.smooth 1
  rw [aux_mainBumpOne_T_cast_eq _ hsmooth, ← hphiC]
  simpa using Auto.fourierDerivativeMul phiC m xi

theorem aux_mainBumpOne_deriv_eq_zero_of_eq_one_on_Icc
    (F : ℝ → ℂ) (x : ℝ) (hx : |x| < 1 / 2)
    (hF : ∀ y ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), F y = 1) :
    deriv F x = 0 := by
  have hxIoo : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [mem_Ioo]
    rw [abs_lt] at hx
    exact hx
  have hnhds : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ nhds x :=
    IsOpen.mem_nhds isOpen_Ioo hxIoo
  have heq : F =ᶠ[nhds x] (fun _ : ℝ => (1 : ℂ)) := by
    filter_upwards [hnhds] with y hy
    exact hF y (Set.Ioo_subset_Icc_self hy)
  calc
    deriv F x = deriv (fun _ : ℝ => (1 : ℂ)) x := Filter.EventuallyEq.deriv_eq heq
    _ = 0 := deriv_const _ _

theorem aux_mainBumpOne_T_fourier_support_window (phi : SchwartzMap ℝ ℝ)
    (hwin : cnWindow C_uniPair N_uniPair phi) :
    Function.support
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ))) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
  intro xi hxi
  have hne : FourierTransform.fourier
      (fun x : ℝ ↦
        (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ)) xi ≠ 0 :=
    Function.mem_support.mp hxi
  rw [Auto.aux_annulusOne]
  constructor
  · by_contra hnot
    push Not at hnot
    have hsmall : |xi| < 1 / 2 := by
      norm_num at hnot
      linarith
    have hderiv : deriv
        (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
      apply aux_mainBumpOne_deriv_eq_zero_of_eq_one_on_Icc _ xi hsmall
      intro y hy
      exact hwin.2.2.2.1 y hy
    have hformula := aux_mainBumpOne_T_fourier_formula phi 0 xi
    apply hne
    simpa [iteratedDeriv_zero, hderiv] using hformula
  · by_contra hnot
    push Not at hnot
    have hlarge : 4 < |xi| := by norm_num at hnot ⊢; exact hnot
    have hout : xi ∉ Set.Icc (-1 : ℝ) 1 := by
      intro hmem
      have habs : |xi| ≤ 1 := abs_le.mpr hmem
      linarith
    have hderivSupp : Function.support
        (iteratedDeriv 1 (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ)))) ⊆
        Set.Icc (-1 : ℝ) 1 := by
      have htsupp : tsupport
          (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) ⊆ Set.Icc (-1 : ℝ) 1 :=
        closure_minimal hwin.2.2.1 isClosed_Icc
      exact (subset_tsupport _).trans
        ((Auto.aux_tsupport_iteratedDeriv_subset _ 1).trans
          htsupp)
    have hderiv' : iteratedDeriv 1
        (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
      apply Function.notMem_support.mp
      intro hsupp
      exact hout (hderivSupp hsupp)
    have hderiv : deriv
        (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
      simpa only [iteratedDeriv_one] using hderiv'
    have hformula := aux_mainBumpOne_T_fourier_formula phi 0 xi
    apply hne
    simpa [iteratedDeriv_zero, hderiv] using hformula

theorem aux_mainBumpOne_T_const_mul (c : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) :
    Auto.aux_sd_T (fun x ↦ c * f x) =
      fun x ↦ c * Auto.aux_sd_T f x := by
  funext x
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => y * f y) x := by
    exact ((contDiff_id.mul hf).contDiffAt).differentiableAt (by norm_num)
  unfold Auto.aux_sd_T
  rw [show (fun y : ℝ => y * (c * f y)) = fun y => c * (y * f y) by
      funext y
      ring]
  rw [deriv_const_mul c hdiff]

theorem aux_mainBumpOne_window_profile_deriv_zero_outside
    (phi : SchwartzMap ℝ ℝ) (hwin : cnWindow C_uniPair N_uniPair phi)
    (m : ℕ) (xi : ℝ) (hxi : xi ∉ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))) xi = 0 := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal (by simpa [F] using hwin.2.2.1) isClosed_Icc
  have hderivSupp : Function.support (iteratedDeriv m F) ⊆ Set.Icc (-1 : ℝ) 1 :=
    (subset_tsupport _).trans
      ((Auto.aux_tsupport_iteratedDeriv_subset F m).trans
        hFtsupp)
  change iteratedDeriv m F xi = 0
  apply Function.notMem_support.mp
  intro hsupp
  exact hxi (hderivSupp hsupp)

theorem aux_mainBumpOne_T_fourier_deriv_bound_window
    (phi : SchwartzMap ℝ ℝ) (hwin : cnWindow C_uniPair N_uniPair phi)
    (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ))) xi‖ ≤
      3 * C_uniPair := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ => (phi x : ℂ))
  have hmle : m ≤ 2 := by omega
  have hmN : m ≤ N_uniPair := by simpa [N_uniPair] using Nat.le_of_lt hm
  have hm1N : m + 1 ≤ N_uniPair := by
    simpa [N_uniPair] using Nat.succ_le_of_lt hm
  have h0 : ‖iteratedDeriv m F xi‖ ≤ C_uniPair :=
    aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi hwin m hmN xi
  have h1 : ‖iteratedDeriv (m + 1) F xi‖ ≤ C_uniPair :=
    aux_mainBumpOneLongOne_window_profile_deriv_bound C_uniPair N_uniPair phi hwin
      (m + 1) hm1N xi
  rw [aux_mainBumpOne_T_fourier_formula phi m xi]
  rw [norm_neg]
  change ‖(m : ℂ) * iteratedDeriv m F xi +
      (xi : ℂ) * iteratedDeriv (m + 1) F xi‖ ≤ 3 * C_uniPair
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have habs : |xi| ≤ 1 := abs_le.mpr hxi
    calc
      ‖(m : ℂ) * iteratedDeriv m F xi +
          (xi : ℂ) * iteratedDeriv (m + 1) F xi‖ ≤
          ‖(m : ℂ) * iteratedDeriv m F xi‖ +
            ‖(xi : ℂ) * iteratedDeriv (m + 1) F xi‖ := norm_add_le _ _
      _ = (m : ℝ) * ‖iteratedDeriv m F xi‖ +
          |xi| * ‖iteratedDeriv (m + 1) F xi‖ := by
            rw [norm_mul, norm_mul, norm_natCast, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (m : ℝ) * C_uniPair + 1 * C_uniPair := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left h0 (by positivity)
            · calc
                |xi| * ‖iteratedDeriv (m + 1) F xi‖ ≤
                    1 * ‖iteratedDeriv (m + 1) F xi‖ := by gcongr
                _ ≤ 1 * C_uniPair := by gcongr
      _ ≤ 3 * C_uniPair := by
            have hC : 0 ≤ C_uniPair := by norm_num [C_uniPair]
            have hmreal : (m : ℝ) ≤ 2 := by exact_mod_cast hmle
            nlinarith
  · have hz0 : iteratedDeriv m F xi = 0 :=
      aux_mainBumpOne_window_profile_deriv_zero_outside phi hwin m xi hxi
    have hz1 : iteratedDeriv (m + 1) F xi = 0 :=
      aux_mainBumpOne_window_profile_deriv_zero_outside phi hwin (m + 1) xi hxi
    simpa [hz0, hz1] using
      (show (0 : ℝ) ≤ 3 * C_uniPair by norm_num [C_uniPair])

noncomputable def aux_mainBumpOne_psi
    (phi : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  (3 * C_uniPair)⁻¹ • phi

theorem aux_mainBumpOne_psi_apply (phi : SchwartzMap ℝ ℝ) (x : ℝ) :
    aux_mainBumpOne_psi phi x = (3 * C_uniPair)⁻¹ * phi x := by
  simp [aux_mainBumpOne_psi, smul_apply]

theorem aux_mainBumpOne_psi_T_fourier (phi : SchwartzMap ℝ ℝ)
    (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦
      (Auto.aux_sd_T
        (fun y ↦ aux_mainBumpOne_psi phi y) x : ℂ)) xi =
      (((3 * C_uniPair)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier (fun x : ℝ ↦
          (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ)) xi := by
  have hsmooth : ContDiff ℝ 1 (fun x : ℝ => phi x) := phi.smooth 1
  have hT := aux_mainBumpOne_T_const_mul (3 * C_uniPair)⁻¹ (fun x : ℝ => phi x)
    hsmooth
  rw [show (fun y : ℝ => aux_mainBumpOne_psi phi y) =
      fun y => (3 * C_uniPair)⁻¹ * phi y by
        funext y
        exact aux_mainBumpOne_psi_apply phi y,
    hT, aux_mainAuxOne_fourier_real_const_mul]

theorem aux_mainBumpOne_psi_T_hypotheses (phi : SchwartzMap ℝ ℝ)
    (hwin : cnWindow C_uniPair N_uniPair phi) :
    aux_mainAuxiliaryFourierHypotheses
      (Auto.aux_sd_T
        (fun x ↦ aux_mainBumpOne_psi phi x)) := by
  let c : ℝ := 3 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  constructor
  · intro xi hxi
    have hne := Function.mem_support.mp hxi
    rw [aux_mainBumpOne_psi_T_fourier] at hne
    have hrawne : FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ)) xi ≠ 0 :=
      (mul_ne_zero_iff.mp hne).2
    exact aux_mainBumpOne_T_fourier_support_window phi hwin
      (Function.mem_support.mpr hrawne)
  · intro m hm xi
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T
          (fun y ↦ aux_mainBumpOne_psi phi y) x : ℂ)) z) xi‖ ≤ 1
    have hformula :
        (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
          (Auto.aux_sd_T
            (fun y ↦ aux_mainBumpOne_psi phi y) x : ℂ)) z) =
          fun z => (((3 * C_uniPair)⁻¹ : ℝ) : ℂ) *
            FourierTransform.fourier (fun x : ℝ ↦
              (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ)) z := by
      funext z
      exact aux_mainBumpOne_psi_T_fourier phi z
    rw [hformula, iteratedDeriv_const_mul_field]
    have hraw := aux_mainBumpOne_T_fourier_deriv_bound_window phi hwin m hm xi
    change ‖(((3 * C_uniPair)⁻¹ : ℝ) : ℂ) * iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ))) xi‖ ≤ 1
    calc
      ‖(((3 * C_uniPair)⁻¹ : ℝ) : ℂ) * iteratedDeriv m
          (FourierTransform.fourier (fun x : ℝ ↦
            (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ))) xi‖ =
          (3 * C_uniPair)⁻¹ * ‖iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ ↦
              (Auto.aux_sd_T (fun y ↦ phi y) x : ℂ))) xi‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      _ ≤ (3 * C_uniPair)⁻¹ * (3 * C_uniPair) := by
            exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
      _ = 1 := by norm_num [C_uniPair]

theorem aux_mainBumpOne_jumpEnergy_const_mul {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (J : ℕ) (t : aux_scaleChain J) :
    aux_jumpEnergy (fun x => c * chi x) f J t =
      ENNReal.ofReal (c ^ 2) * aux_jumpEnergy chi f J t := by
  unfold aux_jumpEnergy twistedJumpEnergy
  calc
    (∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale (t.1 j.succ) (fun u => c * chi u)
              (fun i y ↦ f i y) x -
            twistedAverageAtScale (t.1 j.castSucc) (fun u => c * chi u)
              (fun i y ↦ f i y) x)
        2 volume ^ 2) =
      ∑ j : Fin J, ENNReal.ofReal (c ^ 2) *
        eLpNorm
          (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi
                (fun i y ↦ f i y) x -
              twistedAverageAtScale (t.1 j.castSucc) chi
                (fun i y ↦ f i y) x)
          2 volume ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hpoint :
            (fun x ↦ twistedAverageAtScale (t.1 j.succ) (fun u => c * chi u)
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale (t.1 j.castSucc) (fun u => c * chi u)
                  (fun i y ↦ f i y) x) =
              fun x ↦ c * (twistedAverageAtScale (t.1 j.succ) chi
                    (fun i y ↦ f i y) x -
                  twistedAverageAtScale (t.1 j.castSucc) chi
                    (fun i y ↦ f i y) x) := by
              funext x
              rw [aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul,
                aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul]
              ring
        rw [hpoint]
        exact aux_mainBumpOneLongOne_eLpNorm_sq_const_mul c hc _ volume
    _ = ENNReal.ofReal (c ^ 2) *
        (∑ j : Fin J,
          eLpNorm
            (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale (t.1 j.castSucc) chi
                  (fun i y ↦ f i y) x)
            2 volume ^ 2) := by
          rw [Finset.mul_sum]

theorem aux_mainBumpOne_dyadicJumpEnergy_const_mul {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (J : ℕ) (k : aux_dyadicChain J) :
    aux_dyadicJumpEnergy (fun x => c * chi x) f J k =
      ENNReal.ofReal (c ^ 2) * aux_dyadicJumpEnergy chi f J k := by
  unfold aux_dyadicJumpEnergy twistedDyadicJumpEnergy
  calc
    (∑ j : Fin J,
      eLpNorm
        (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u => c * chi u)
              (fun i y ↦ f i y) x -
            twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u => c * chi u)
              (fun i y ↦ f i y) x)
        2 volume ^ 2) =
      ∑ j : Fin J, ENNReal.ofReal (c ^ 2) *
        eLpNorm
          (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi
                (fun i y ↦ f i y) x -
              twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi
                (fun i y ↦ f i y) x)
          2 volume ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hpoint :
            (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) (fun u => c * chi u)
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) (fun u => c * chi u)
                  (fun i y ↦ f i y) x) =
              fun x ↦ c * (twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi
                    (fun i y ↦ f i y) x -
                  twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi
                    (fun i y ↦ f i y) x) := by
              funext x
              rw [aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul,
                aux_mainBumpOneLongOne_twistedAverageAtScale_const_mul]
              ring
        rw [hpoint]
        exact aux_mainBumpOneLongOne_eLpNorm_sq_const_mul c hc _ volume
    _ = ENNReal.ofReal (c ^ 2) *
        (∑ j : Fin J,
          eLpNorm
            (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.succ)) chi
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale ((2 : ℝ) ^ (k.1 j.castSucc)) chi
                  (fun i y ↦ f i y) x)
            2 volume ^ 2) := by
          rw [Finset.mul_sum]

theorem aux_mainBumpOne_variationBound_const_mul {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (A : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_variationBound A chi f) :
    aux_variationBound (c ^ 2 * A) (fun x => c * chi x) f := by
  intro J hJ t
  calc
    aux_jumpEnergy (fun x => c * chi x) f J t =
        ENNReal.ofReal (c ^ 2) * aux_jumpEnergy chi f J t :=
      aux_mainBumpOne_jumpEnergy_const_mul c hc chi f J t
    _ ≤ ENNReal.ofReal (c ^ 2) *
        (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :=
      mul_le_mul_of_nonneg_left (hA J hJ t) bot_le
    _ = ENNReal.ofReal (c ^ 2 * A) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (sq_nonneg c)]
      ring

theorem aux_mainBumpOne_dyadicVariationBound_const_mul {n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (A : ℝ) (chi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_dyadicVariationBound A chi f) :
    aux_dyadicVariationBound (c ^ 2 * A) (fun x => c * chi x) f := by
  intro J hJ k
  calc
    aux_dyadicJumpEnergy (fun x => c * chi x) f J k =
        ENNReal.ofReal (c ^ 2) * aux_dyadicJumpEnergy chi f J k :=
      aux_mainBumpOne_dyadicJumpEnergy_const_mul c hc chi f J k
    _ ≤ ENNReal.ofReal (c ^ 2) *
        (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :=
      mul_le_mul_of_nonneg_left (hA J hJ k) bot_le
    _ = ENNReal.ofReal (c ^ 2 * A) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (sq_nonneg c)]
      ring

theorem aux_mainBumpOne_C_mainAuxOne_pos (n : ℕ) : 0 < C_mainAuxOne n := by
  have hdiagonal : 0 ≤ C_diagonalBandReduction := by
    unfold C_diagonalBandReduction
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) aux_CincreaseDataReduction_nonneg)
  have hnonWhitney : 0 < C_inductPositiveTermsReductionNonWhitney := by
    unfold C_inductPositiveTermsReductionNonWhitney
    apply add_pos_of_pos_of_nonneg
    · norm_num [C_oneScaleEstimateWindow, C_uniPair]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) hdiagonal
  have hskip : 0 < C_inductPositiveTermsReductionNonWhitneySkip n := by
    unfold C_inductPositiveTermsReductionNonWhitneySkip
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hnonWhitney
  have hgap : 0 < C_inductPositiveTermsReductionWhitneyGap n := by
    unfold C_inductPositiveTermsReductionWhitneyGap
    apply add_pos_of_pos_of_nonneg
    · exact mul_pos (by norm_num) hskip
    · exact mul_nonneg (mul_nonneg (by positivity) (add_nonneg (sq_nonneg _)
        (sq_nonneg _))) hdiagonal
  have hWhitney : 0 < C_inductPositiveTermsReductionWhitney n := by
    unfold C_inductPositiveTermsReductionWhitney
    exact mul_pos (by norm_num) hgap
  have hproduct : 0 < C_inductPositiveTermsReductionWhitneyProduct n := by
    unfold C_inductPositiveTermsReductionWhitneyProduct
    exact mul_pos (by positivity) hWhitney
  unfold C_mainAuxOne
  exact mul_pos (by positivity) hproduct

theorem aux_mainBumpOne_C_long_pos (n : ℕ) :
    0 < C_mainBumpOneLong n := by
  have hOne : 0 < C_mainBumpOneLongOne n := by
    unfold C_mainBumpOneLongOne
    exact mul_pos (sq_pos_of_pos (by norm_num [C_uniPair]))
      (aux_mainBumpOne_C_mainAuxOne_pos n)
  unfold C_mainBumpOneLong
  exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hOne
    (aux_mainBumpOneLong_two_nonneg n))

/--
**Lemma.**

Let $J\ge1$. Then

$$
\|A_t(\phi_0)\|_{V_{2,J}(t\in(0,\infty);L^2)}^2
\le C_{\text{lem:mainbump1}}J^{\alpha(n)},
$$

where

$$
C_{\text{lem:mainbump1}}
=2^4(3C_{\text{Universal pair}})^2C_{\text{lem:main\_aux1}}
+2C_{\text{lem:mainbump1\_long}}.
$$

See also `Auto.mainBumpOne`,
`Auto.uniPair`,
`Auto.mainAuxOne`,
`Auto.mainBumpOneLong`.
-/
theorem mainBumpOne {n : ℕ} (hn : 2 ≤ n)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (f : ReductionNormalizedTuple n) :
    aux_variationBound (C_mainBumpOne n) (fun x ↦ phi0 x) f.1 := by
  let c : ℝ := 3 * C_uniPair
  let psi : SchwartzMap ℝ ℝ := c⁻¹ • phi0
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  have hpsi_eq : psi = aux_mainBumpOne_psi phi0 := by
    rfl
  have hTpsi : aux_mainAuxiliaryFourierHypotheses
      (Auto.aux_sd_T (fun x ↦ psi x)) := by
    rw [hpsi_eq]
    exact aux_mainBumpOne_psi_T_hypotheses phi0 hpair.1
  have hTpsiBump : aux_mainAuxiliaryFourierHypotheses
      (Auto.aux_T (fun x ↦ psi x)) := by
    have hreal : Auto.aux_T (fun x ↦ psi x) =
        Auto.aux_sd_T (fun x ↦ psi x) := by
      funext x
      unfold Auto.aux_T
        Auto.aux_sd_T
      rfl
    rw [hreal]
    exact hTpsi
  have hlong : aux_dyadicVariationBound (C_mainBumpOneLong n)
      (fun x ↦ phi0 x) f.1 :=
    mainBumpOneLong hn phi0 phi1 hpair f
  have hdyadic : aux_dyadicVariationBound
      ((c⁻¹) ^ 2 * C_mainBumpOneLong n) (fun x ↦ psi x) f.1 := by
    have h := aux_mainBumpOne_dyadicVariationBound_const_mul c⁻¹
      (inv_nonneg.mpr hc.le) (C_mainBumpOneLong n) (fun x ↦ phi0 x) f.1 hlong
    simpa [psi, smul_apply] using h
  have hApos : 0 < (c⁻¹) ^ 2 * C_mainBumpOneLong n := by
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr hc)) (aux_mainBumpOne_C_long_pos n)
  have hshort : aux_variationBound
      (16 * C_mainAuxOne n + 2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n))
      (fun x ↦ psi x) f.1 :=
    shortLongFtcReduction hn psi hTpsiBump f 1 (by norm_num)
      ((c⁻¹) ^ 2 * C_mainBumpOneLong n) hApos hdyadic
  have hrescaled := aux_mainBumpOne_variationBound_const_mul c hc.le
    (16 * C_mainAuxOne n + 2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n))
    (fun x ↦ psi x) f.1 hshort
  have hC : c ^ 2 *
      (16 * C_mainAuxOne n + 2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n)) =
      C_mainBumpOne n := by
    calc
      c ^ 2 * (16 * C_mainAuxOne n +
          2 * ((c⁻¹) ^ 2 * C_mainBumpOneLong n)) =
          16 * c ^ 2 * C_mainAuxOne n + 2 * C_mainBumpOneLong n := by
            field_simp [hc.ne']
      _ = C_mainBumpOne n := by
            dsimp [c]
            simp only [C_mainBumpOne]
            ring
  have hfun : (fun x ↦ c * psi x) = fun x ↦ phi0 x := by
    funext x
    dsimp [psi]
    change c * (c⁻¹ * phi0 x) = phi0 x
    field_simp [hc.ne']
  rw [hC, hfun] at hrescaled
  exact hrescaled

/--
**Lemma (constant $C_{\text{lem:mainbump1}}$).**

$$
C_{\text{lem:mainbump1}}<\tfrac78 2^{610}<2^{610}.
$$

See also `Auto.mainBumpOne`.
-/
theorem constantMainBumpOne {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpOne n < (7 / 8 : ℝ) * (2 : ℝ) ^ 610 := by
  unfold C_mainBumpOne
  calc
    (2 : ℝ) ^ 4 * (3 * C_uniPair) ^ 2 * C_mainAuxOne n +
        2 * C_mainBumpOneLong n <
        (2 : ℝ) ^ 4 * (3 * C_uniPair) ^ 2 *
          ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) +
          2 * ((11 / 16 : ℝ) * (2 : ℝ) ^ 606) := by
          exact add_lt_add
            (mul_lt_mul_of_pos_left (aux_constantMainAuxOne_sharp hn)
              (by norm_num [C_uniPair]))
            (mul_lt_mul_of_pos_left (constantMainBumpOneLong hn) (by norm_num))
    _ < (7 / 8 : ℝ) * (2 : ℝ) ^ 610 := by
      set_option exponentiation.threshold 1000 in
        norm_num [C_uniPair]

/-- The constant in Lemma `Auto.mainAuxTwo`. -/
noncomputable def C_mainAuxTwo (n : ℕ) : ℝ :=
  24 * C_mainAuxOne n

/-- Pad a finite strictly increasing sequence by one terminal exponent. -/
theorem aux_mainAuxTwo_chain_to_dyadicChain (J : ℕ) (hJ : 0 < J)
    (ks : {u : Fin J → ℤ // StrictMono u}) :
    ∃ q : aux_dyadicChain J, ∀ j : Fin J, q.1 j.castSucc = ks.1 j := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ.ne'
  let qfun : Fin (K + 1 + 1) → ℤ :=
    Fin.lastCases (ks.1 (Fin.last K) + 1) ks.1
  have hqfun : StrictMono qfun := by
    intro i j hij
    by_cases hj : j = Fin.last (K + 1)
    · subst j
      have hilast : i < Fin.last (K + 1) := by simpa using hij
      let i' : Fin (K + 1) := ⟨i.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      rw [hi]
      simp only [qfun, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hle : ks.1 i' ≤ ks.1 (Fin.last K) := ks.2.monotone (Fin.le_last i')
      omega
    · have hjlast : j < Fin.last (K + 1) := Fin.lt_last_iff_ne_last.mpr hj
      let i' : Fin (K + 1) := ⟨i.1, by omega⟩
      let j' : Fin (K + 1) := ⟨j.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      have hj' : j = j'.castSucc := by rfl
      rw [hi, hj']
      simp only [qfun, Fin.lastCases_castSucc]
      apply ks.2
      simpa [i', j'] using hij
  refine ⟨⟨qfun, hqfun⟩, ?_⟩
  intro j
  simp only [qfun, Fin.lastCases_castSucc]

/--
The first auxiliary estimate, together with `bootstrap`, gives the dyadic
variation estimate required by the short-long reduction.
-/
theorem aux_mainAuxTwo_dyadic {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (hpsi : aux_mainAuxiliaryTwoHypotheses psi)
    (f : ReductionNormalizedTuple n) :
    aux_dyadicVariationBound (4 * C_mainAuxOne n) (fun x ↦ psi x) f.1 := by
  intro J hJ k
  have hsup :
      (⨆ ks : {u : Fin J → ℤ // StrictMono u},
        ∑ j, eLpNorm
          (twistedAverageAtScale ((2 : ℝ) ^ (ks.1 j)) (fun x ↦ psi x)
            (fun i x ↦ f.1 i x)) 2 volume ^ 2) ≤
        ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    apply iSup_le
    intro ks
    obtain ⟨q, hq⟩ := aux_mainAuxTwo_chain_to_dyadicChain J hJ ks
    simpa only [mul_one, hq] using
      (mainAuxOne hn psi hpsi.1 f 1 (by norm_num) J hJ q)
  calc
    aux_dyadicJumpEnergy (fun x ↦ psi x) f.1 J k ≤
        twistedDyadicVariationEnergy (fun x ↦ psi x) (fun i x ↦ f.1 i x) J := by
      change twistedDyadicJumpEnergy (fun x ↦ psi x) (fun i x ↦ f.1 i x) J k ≤ _
      rw [twistedDyadicVariationEnergy]
      exact le_iSup (fun q : aux_dyadicChain J =>
        twistedDyadicJumpEnergy (fun x ↦ psi x) (fun i x ↦ f.1 i x) J q) k
    _ ≤ 4 * ⨆ ks : {u : Fin J → ℤ // StrictMono u},
        ∑ j, eLpNorm
          (twistedAverageAtScale ((2 : ℝ) ^ (ks.1 j)) (fun x ↦ psi x)
            (fun i x ↦ f.1 i x)) 2 volume ^ 2 :=
      bootstrap hn psi f.1 J
    _ ≤ 4 * (ENNReal.ofReal (C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
      simpa [mul_comm] using mul_le_mul_left hsup 4
    _ = ENNReal.ofReal (4 * C_mainAuxOne n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring

/-- Complexification commutes with the logarithmic-derivative operator. -/
theorem aux_mainAuxTwo_T_cast_eq (f : SchwartzMap ℝ ℝ) :
    (fun x : ℝ ↦
      ((Auto.aux_T
        (fun y : ℝ ↦ (f y : ℝ)) : ℝ → ℝ) x : ℂ)) =
      Auto.aux_T (fun x : ℝ ↦ (f x : ℂ)) := by
  funext x
  have hf : ContDiff ℝ 1 (fun y : ℝ ↦ f y) := by
    simpa using f.smooth 1
  have hdiff : DifferentiableAt ℝ (fun y : ℝ ↦ y * f y) x := by
    exact ((contDiff_id.mul hf).contDiffAt).differentiableAt (by norm_num)
  have hcast :
      deriv (fun y : ℝ ↦ ((y * f y : ℝ) : ℂ)) x =
        ((deriv (fun y : ℝ ↦ y * f y) x : ℝ) : ℂ) := by
    simpa using ((hasDerivAt_const x Complex.ofRealCLM).clm_apply hdiff.hasDerivAt).deriv
  have hfun : (fun y : ℝ ↦ ((y * f y : ℝ) : ℂ)) =
      Auto.multiplicationOperatorX
        (fun y : ℝ ↦ (f y : ℂ)) := by
    funext y
    simp [Auto.multiplicationOperatorX]
  have hfunreal :
      Auto.multiplicationOperatorX
        (fun y : ℝ ↦ (f y : ℝ)) = fun y : ℝ ↦ y * f y := by
    funext y
    simp [Auto.multiplicationOperatorX]
  unfold Auto.aux_T
  rw [hfunreal, ← hfun, hcast]

/--
The Fourier support assumption for `psi` is stable under the logarithmic
derivative.
-/
theorem aux_mainAuxTwo_T_hyp (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryTwoHypotheses psi) :
    aux_mainAuxiliaryFourierHypotheses
      (Auto.aux_T (fun x : ℝ ↦ psi x)) := by
  have hTderiv : ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m (FourierTransform.fourier
        (fun x : ℝ ↦
          ((Auto.aux_T
            (fun y : ℝ ↦ (psi y : ℝ)) : ℝ → ℝ) x : ℂ))) xi‖ ≤ 1 := by
    intro m hm xi
    rw [aux_mainAuxTwo_T_cast_eq psi]
    exact hpsi.2 m hm xi
  refine ⟨?_, hTderiv⟩
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))
  have hFsupp : Function.support F ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
    simpa [F, aux_mainAuxiliaryTwoHypotheses, aux_mainAuxiliaryHypotheses,
      aux_mainAuxiliaryFourierHypotheses] using hpsi.1.1
  have hannulus_closed : IsClosed
      (Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2)) := by
    unfold Auto.aux_annulusOne
    exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  have hFtsupp : tsupport F ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) :=
    closure_minimal hFsupp hannulus_closed
  have hderivSupp : Function.support (iteratedDeriv 1 F) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) :=
    (subset_tsupport _).trans
      ((Auto.aux_tsupport_iteratedDeriv_subset F 1).trans
        hFtsupp)
  intro xi hxi
  apply hderivSupp
  apply Function.mem_support.mpr
  intro hzero
  apply hxi
  let psiC : SchwartzMap ℝ ℂ :=
    psi.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hpsiC : (psiC : ℝ → ℂ) = fun x : ℝ ↦ (psi x : ℂ) := by
    funext x
    simp [psiC, SchwartzMap.postcompCLM_apply]
  have hformula :
      FourierTransform.fourier
        (Auto.aux_T (fun x : ℝ ↦ (psi x : ℂ))) xi =
        -((xi : ℂ) * iteratedDeriv 1 F xi) := by
    unfold F
    rw [← hpsiC]
    change FourierTransform.fourier
      (Auto.aux_T (fun x : ℝ ↦ psiC x)) xi = _
    simpa [F] using
      (Auto.fourierDerivativeMul psiC 0 xi)
  rw [aux_mainAuxTwo_T_cast_eq psi, hformula, hzero]
  simp

/--
**Lemma.**

Let $\psi$ satisfy (`main_aux1_supp`) and (`auto:main-auxiliary-one-Fourier-derivative-assumption`).
Assume also that

$$
|\widehat{T\psi}^{(m)}(\xi)|\le1,
\qquad
m\in[3),
\quad
\xi\in\mathbb{R}.
$$

Then

$$
\|A_t(\psi)\|_{V_{2,J}(t\in(0,\infty);L^2)}^2
\le C_{\text{lem:main\_aux2}}J^{\alpha(n)},
$$

where $C_{\text{lem:main\_aux2}}=24C_{\text{lem:main\_aux1}}$.

See also `Auto.mainAuxTwo`,
`Auto.mainAuxOne`.
-/
theorem mainAuxTwo {n : ℕ} (hn : 2 ≤ n) (psi : SchwartzMap ℝ ℝ)
    (hpsi : aux_mainAuxiliaryTwoHypotheses psi)
    (f : ReductionNormalizedTuple n) :
    aux_variationBound (C_mainAuxTwo n) (fun x ↦ psi x) f.1 := by
  have hdyadic := aux_mainAuxTwo_dyadic hn psi hpsi f
  have hT := aux_mainAuxTwo_T_hyp psi hpsi
  rw [C_mainAuxTwo]
  convert shortLongFtcReduction hn psi hT f 1 (by norm_num)
    (4 * C_mainAuxOne n)
    (mul_pos (by norm_num) (aux_mainBumpOne_C_mainAuxOne_pos n)) hdyadic using 1;
    ring

/--
**Lemma (constant $C_{\text{lem:main\_aux2}}$).**

$$
C_{\text{lem:main\_aux2}}<2^{578}.
$$

See also `Auto.mainAuxTwo`.
-/
theorem constantMainAuxiliaryTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxTwo n < (2 : ℝ) ^ 578 := by
  unfold C_mainAuxTwo
  calc
    24 * C_mainAuxOne n < 24 * (2 : ℝ) ^ 573 :=
      mul_lt_mul_of_pos_left (constantMainAuxiliaryOne hn) (by norm_num)
    _ = 3 * (2 : ℝ) ^ 576 := by
      calc
        24 * (2 : ℝ) ^ 573 = 3 * ((2 : ℝ) ^ 3 * (2 : ℝ) ^ 573) := by
          norm_num
          set_option exponentiation.threshold 1000 in
            ring
        _ = 3 * (2 : ℝ) ^ 576 := by rw [← pow_add]
    _ < 4 * (2 : ℝ) ^ 576 := by
      exact mul_lt_mul_of_pos_right (by norm_num) (by positivity)
    _ = (2 : ℝ) ^ 578 := by
      calc
        4 * (2 : ℝ) ^ 576 = (2 : ℝ) ^ 2 * (2 : ℝ) ^ 576 := by norm_num
        _ = (2 : ℝ) ^ (2 + 576) := by rw [← pow_add]
        _ = (2 : ℝ) ^ 578 := by norm_num

/-- The constant in Lemma `Auto.mainBumpTwo`. -/
noncomputable def C_mainBumpTwo (n : ℕ) : ℝ :=
  C_mainAuxTwo n * C_absDerivFourierTPhiThreeLe 2 ^ 2

/-! Private Fourier, normalization, and scale-transport infrastructure for `mainBumpTwo`. -/

theorem aux_mainBumpTwo_phiThree_eq_rescaled (b : windowBasedBumpFunctions)
    (k : ℤ) :
    windowBasedBumpFunctions.phiThree b k =
      fun x ↦ (2 : ℝ) ^ k * aux_oneRescaled ((2 : ℝ) ^ (-k))
        (windowBasedBumpFunctions.phiZero b k) x := by
  funext x
  rfl

theorem aux_mainBumpTwo_phiThree_fourier_support_small
    (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) ⊆
      aux_frequencyAnnulus := by
  intro xi hxi
  have hne := Function.mem_support.mp hxi
  have htheta : FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.theta b x : ℂ)) xi ≠ 0 := by
    intro hzero
    rw [fourierPhiThreeEq] at hne
    simp [hzero] at hne
  exact (bumpBasic b).1 (Function.mem_support.mpr htheta)

theorem aux_mainBumpTwo_frequencyAnnulus_subset_Icc :
    aux_frequencyAnnulus ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  rcases hx with hx | hx <;> exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem aux_mainBumpTwo_phiThree_fourier_support (b : windowBasedBumpFunctions)
    (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
  intro xi hxi
  have hmem := aux_mainBumpTwo_phiThree_fourier_support_small b k hxi
  unfold Auto.aux_annulusOne
  rcases hmem with hmem | hmem
  · constructor
    · rw [abs_of_nonpos (by linarith [hmem.2])]
      norm_num
      linarith [hmem.2]
    · rw [abs_of_nonpos (by linarith [hmem.2])]
      norm_num
      linarith [hmem.1]
  · constructor
    · rw [abs_of_nonneg (by linarith [hmem.1])]
      norm_num
      linarith [hmem.1]
    · rw [abs_of_nonneg (by linarith [hmem.1])]
      norm_num
      linarith [hmem.2]

theorem aux_mainBumpTwo_phiThree_deriv_zero_outside
    (b : windowBasedBumpFunctions) (k : ℤ) (m : ℕ) (xi : ℝ)
    (hxi : xi ∉ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi = 0 := by
  let F : ℝ → ℂ := FourierTransform.fourier
    (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal
      ((aux_mainBumpTwo_phiThree_fourier_support_small b k).trans
        aux_mainBumpTwo_frequencyAnnulus_subset_Icc)
      isClosed_Icc
  have hderivSupp : Function.support (iteratedDeriv m F) ⊆ Set.Icc (-1 : ℝ) 1 :=
    (subset_tsupport _).trans
      ((Auto.aux_tsupport_iteratedDeriv_subset F m).trans
        hFtsupp)
  change iteratedDeriv m F xi = 0
  apply Function.notMem_support.mp
  intro hsupp
  exact hxi (hderivSupp hsupp)

theorem aux_mainBumpTwo_phiThree_deriv_bound (b : windowBasedBumpFunctions)
    (k : ℤ) (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ ≤
      C_absDerivFourierTPhiThreeLe 2 := by
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have habs : |xi| ≤ 1 := abs_le.mpr hxi
    calc
      ‖iteratedDeriv m
          (FourierTransform.fourier
            (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ ≤
          C_absDerivFourierPhiThreeLe m :=
        absDerivFourierPhiThreeLe b m (by omega) k xi habs
      _ ≤ C_absDerivFourierTPhiThreeLe 2 := by
        interval_cases m <;>
          norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
            C_uniPair]
  · rw [aux_mainBumpTwo_phiThree_deriv_zero_outside b k m xi hxi]
    norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
      C_uniPair]

theorem aux_mainBumpTwo_frequencyAnnulus_closed : IsClosed aux_frequencyAnnulus := by
  exact isClosed_Icc.union isClosed_Icc

theorem aux_mainBumpTwo_phiThree_T_fourier_formula
    (b : windowBasedBumpFunctions) (k : ℤ) (m : ℕ) (xi : ℝ) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi =
      - ((m : ℂ) * iteratedDeriv m
            (FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi +
          (xi : ℂ) * iteratedDeriv (m + 1)
            (FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi) := by
  simpa only [phiThreeSchwartz_apply] using
    aux_mainBumpOne_T_fourier_formula (phiThreeSchwartz b k) m xi

theorem aux_mainBumpTwo_phiThree_T_fourier_support_small
    (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier (fun x : ℝ ↦
      (Auto.aux_sd_T
        (windowBasedBumpFunctions.phiThree b k) x : ℂ))) ⊆ aux_frequencyAnnulus := by
  intro xi hxi
  have hne := Function.mem_support.mp hxi
  have hformula := aux_mainBumpTwo_phiThree_T_fourier_formula b k 0 xi
  simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul] at hformula
  rw [hformula] at hne
  have hderiv : iteratedDeriv 1
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi ≠ 0 := by
    intro hzero
    simp [hzero] at hne
  let F : ℝ → ℂ := FourierTransform.fourier
    (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))
  have hFtsupp : tsupport F ⊆ aux_frequencyAnnulus :=
    closure_minimal (aux_mainBumpTwo_phiThree_fourier_support_small b k)
      aux_mainBumpTwo_frequencyAnnulus_closed
  have hderivSupp : Function.support (iteratedDeriv 1 F) ⊆ aux_frequencyAnnulus :=
    (subset_tsupport _).trans
      ((Auto.aux_tsupport_iteratedDeriv_subset F 1).trans
        hFtsupp)
  apply hderivSupp
  exact Function.mem_support.mpr hderiv

theorem aux_mainBumpTwo_phiThree_T_deriv_zero_outside
    (b : windowBasedBumpFunctions) (k : ℤ) (m : ℕ) (xi : ℝ)
    (hxi : xi ∉ Set.Icc (-1 : ℝ) 1) :
    iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi = 0 := by
  let F : ℝ → ℂ := FourierTransform.fourier (fun x : ℝ ↦
    (Auto.aux_sd_T
      (windowBasedBumpFunctions.phiThree b k) x : ℂ))
  have hFtsupp : tsupport F ⊆ Set.Icc (-1 : ℝ) 1 :=
    closure_minimal
      ((aux_mainBumpTwo_phiThree_T_fourier_support_small b k).trans
        aux_mainBumpTwo_frequencyAnnulus_subset_Icc)
      isClosed_Icc
  have hderivSupp : Function.support (iteratedDeriv m F) ⊆ Set.Icc (-1 : ℝ) 1 :=
    (subset_tsupport _).trans
      ((Auto.aux_tsupport_iteratedDeriv_subset F m).trans
        hFtsupp)
  change iteratedDeriv m F xi = 0
  apply Function.notMem_support.mp
  intro hsupp
  exact hxi (hderivSupp hsupp)

theorem aux_mainBumpTwo_phiThree_T_deriv_bound (b : windowBasedBumpFunctions)
    (k : ℤ) (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ ≤
      C_absDerivFourierTPhiThreeLe 2 := by
  by_cases hxi : xi ∈ Set.Icc (-1 : ℝ) 1
  · have habs : |xi| ≤ 1 := abs_le.mpr hxi
    exact (absDerivFourierTPhiThreeLe b m hm k xi habs).trans
      (by interval_cases m <;>
        norm_num [C_absDerivFourierTPhiThreeLe,
          C_absDerivFourierPhiThreeLe, C_uniPair])
  · rw [aux_mainBumpTwo_phiThree_T_deriv_zero_outside b k m xi hxi]
    norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
      C_uniPair]

theorem aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos :
    0 < C_absDerivFourierTPhiThreeLe 2 := by
  norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
    C_uniPair]

noncomputable def aux_mainBumpTwo_psi (b : windowBasedBumpFunctions)
    (k : ℤ) : SchwartzMap ℝ ℝ :=
  (C_absDerivFourierTPhiThreeLe 2)⁻¹ • phiThreeSchwartz b k

theorem aux_mainBumpTwo_psi_apply (b : windowBasedBumpFunctions) (k : ℤ)
    (x : ℝ) :
    aux_mainBumpTwo_psi b k x = (C_absDerivFourierTPhiThreeLe 2)⁻¹ *
      windowBasedBumpFunctions.phiThree b k x := by
  simp [aux_mainBumpTwo_psi, smul_apply, phiThreeSchwartz_apply]

theorem aux_mainBumpTwo_psi_fourier (b : windowBasedBumpFunctions) (k : ℤ)
    (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) xi =
      (((C_absDerivFourierTPhiThreeLe 2)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) xi := by
  rw [show (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) =
      fun x ↦ (((C_absDerivFourierTPhiThreeLe 2)⁻¹ *
        windowBasedBumpFunctions.phiThree b k x : ℝ) : ℂ) by
        funext x
        norm_cast
        exact aux_mainBumpTwo_psi_apply b k x,
    aux_mainAuxOne_fourier_real_const_mul]

theorem aux_mainBumpTwo_phiThree_smooth (b : windowBasedBumpFunctions)
    (k : ℤ) : ContDiff ℝ 1 (windowBasedBumpFunctions.phiThree b k) := by
  have hfun : windowBasedBumpFunctions.phiThree b k =
      fun x : ℝ ↦ phiThreeSchwartz b k x := by
    funext x
    exact (phiThreeSchwartz_apply b k x).symm
  rw [hfun]
  exact (phiThreeSchwartz b k).smooth 1

theorem aux_mainBumpTwo_psi_T_fourier (b : windowBasedBumpFunctions) (k : ℤ)
    (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦
      (Auto.aux_sd_T
        (fun y ↦ aux_mainBumpTwo_psi b k y) x : ℂ)) xi =
      (((C_absDerivFourierTPhiThreeLe 2)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier (fun x : ℝ ↦
          (Auto.aux_sd_T
            (windowBasedBumpFunctions.phiThree b k) x : ℂ)) xi := by
  rw [show (fun y : ℝ ↦ aux_mainBumpTwo_psi b k y) =
      fun y ↦ (C_absDerivFourierTPhiThreeLe 2)⁻¹ *
        windowBasedBumpFunctions.phiThree b k y by
        funext y
        exact aux_mainBumpTwo_psi_apply b k y,
    aux_mainBumpOne_T_const_mul _ _ (aux_mainBumpTwo_phiThree_smooth b k),
    aux_mainAuxOne_fourier_real_const_mul]

theorem aux_mainBumpTwo_psi_hypotheses (b : windowBasedBumpFunctions)
    (k : ℤ) : aux_mainAuxiliaryTwoHypotheses (aux_mainBumpTwo_psi b k) := by
  let c : ℝ := C_absDerivFourierTPhiThreeLe 2
  have hc : 0 < c := by
    exact aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos
  constructor
  · constructor
    · intro xi hxi
      have hne := Function.mem_support.mp hxi
      rw [aux_mainBumpTwo_psi_fourier] at hne
      have hrawne : FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) xi ≠ 0 :=
        (mul_ne_zero_iff.mp hne).2
      exact aux_mainBumpTwo_phiThree_fourier_support b k
        (Function.mem_support.mpr hrawne)
    · intro m hm xi
      change ‖iteratedDeriv m
        (fun z : ℝ => FourierTransform.fourier
          (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) z) xi‖ ≤ 1
      have hformula :
          (fun z : ℝ => FourierTransform.fourier
            (fun x : ℝ ↦ (aux_mainBumpTwo_psi b k x : ℂ)) z) =
            fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) z := by
        funext z
        simpa [c] using aux_mainBumpTwo_psi_fourier b k z
      rw [hformula, iteratedDeriv_const_mul_field]
      have hraw := aux_mainBumpTwo_phiThree_deriv_bound b k m hm xi
      change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
        (FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ ≤ 1
      calc
        ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
            (FourierTransform.fourier
              (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ =
            c⁻¹ * ‖iteratedDeriv m
              (FourierTransform.fourier
                (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) xi‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hc)]
        _ ≤ c⁻¹ * c := by
              exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
        _ = 1 := by field_simp [hc.ne']
  · intro m hm xi
    have hsmooth : ContDiff ℝ 1 (fun y : ℝ => aux_mainBumpTwo_psi b k y) :=
      (aux_mainBumpTwo_psi b k).smooth 1
    rw [← aux_mainBumpOne_T_cast_eq _ hsmooth]
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T
          (fun y ↦ aux_mainBumpTwo_psi b k y) x : ℂ)) z) xi‖ ≤ 1
    have hformula :
        (fun z : ℝ => FourierTransform.fourier (fun x : ℝ ↦
          (Auto.aux_sd_T
            (fun y ↦ aux_mainBumpTwo_psi b k y) x : ℂ)) z) =
          fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier (fun x : ℝ ↦
            (Auto.aux_sd_T
              (windowBasedBumpFunctions.phiThree b k) x : ℂ)) z := by
      funext z
      simpa [c] using aux_mainBumpTwo_psi_T_fourier b k z
    rw [hformula, iteratedDeriv_const_mul_field]
    have hraw := aux_mainBumpTwo_phiThree_T_deriv_bound b k m hm xi
    change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ ↦
        (Auto.aux_sd_T
          (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ ≤ 1
    calc
      ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
          (FourierTransform.fourier (fun x : ℝ ↦
            (Auto.aux_sd_T
              (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ =
          c⁻¹ * ‖iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ ↦
              (Auto.aux_sd_T
                (windowBasedBumpFunctions.phiThree b k) x : ℂ))) xi‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hc)]
      _ ≤ c⁻¹ * c := by
            exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
      _ = 1 := by field_simp [hc.ne']

theorem aux_mainBumpTwo_twistedAverageAtScale_oneRescaled {n : ℕ}
    (phi : ℝ → ℝ) (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (t lambda : ℝ) (ht : 0 < t) (hlambda : 0 < lambda) :
    twistedAverageAtScale t (aux_oneRescaled lambda phi) f =
      twistedAverageAtScale (t * lambda) phi f := by
  unfold twistedAverageAtScale
  unfold aux_twistedAverageAtScale aux_twistedAverage aux_oneRescaled
  funext x
  congr 1
  funext s
  congr 1
  field_simp [ht.ne', hlambda.ne']

def aux_mainBumpTwo_scaleMul (lambda : ℝ) (hlambda : 0 < lambda)
    {J : ℕ} (t : aux_scaleChain J) : aux_scaleChain J :=
  ⟨fun j ↦ lambda * t.1 j,
    ⟨by
      intro i j hij
      exact mul_lt_mul_of_pos_left (t.2.1 hij) hlambda,
    by
      intro j
      exact mul_pos hlambda (t.2.2 j)⟩⟩

theorem aux_mainBumpTwo_variationBound_of_oneRescaled {n : ℕ} (lambda : ℝ)
    (hlambda : 0 < lambda) (A : ℝ) (phi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_variationBound A (aux_oneRescaled lambda phi) f) :
    aux_variationBound A phi f := by
  intro J hJ t
  let t' : aux_scaleChain J := aux_mainBumpTwo_scaleMul lambda⁻¹ (inv_pos.mpr hlambda) t
  have hscale (j : Fin (J + 1)) : t'.1 j * lambda = t.1 j := by
    dsimp [t', aux_mainBumpTwo_scaleMul]
    field_simp [hlambda.ne']
  have hEq : aux_jumpEnergy (aux_oneRescaled lambda phi) f J t' =
      aux_jumpEnergy phi f J t := by
    unfold aux_jumpEnergy twistedJumpEnergy
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    funext x
    rw [aux_mainBumpTwo_twistedAverageAtScale_oneRescaled phi (fun i y ↦ f i y)
      (t'.1 j.succ) lambda (t'.2.2 j.succ) hlambda,
      aux_mainBumpTwo_twistedAverageAtScale_oneRescaled phi (fun i y ↦ f i y)
        (t'.1 j.castSucc) lambda (t'.2.2 j.castSucc) hlambda,
      hscale j.succ, hscale j.castSucc]
  calc
    aux_jumpEnergy phi f J t = aux_jumpEnergy (aux_oneRescaled lambda phi) f J t' :=
      hEq.symm
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
      hA J hJ t'

/--
**Lemma.**

For all $k\ge-2$,

$$
\|A_t(\varphi_{0,k})\|_{V_{2,J}(t\in(0,\infty);L^2)}^2
\le C_{\text{lem:mainbump2}}2^{-2k}J^{\alpha(n)},
$$

where

$$
C_{\text{lem:mainbump2}}
=C_{\text{lem:main\_aux2}}C_{\text{lem:abs\_deriv\_ft\_Tphi3\_le},2}^2.
$$

See also `Auto.mainBumpTwo`,
`Auto.mainAuxTwo`,
`Auto.absDerivFourierTPhiThreeLe`.
-/
theorem mainBumpTwo {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : -2 ≤ k) :
    aux_variationBound (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * k))
      (windowBasedBumpFunctions.phiZero b k) f.1 := by
  have _ := hk
  let c : ℝ := C_absDerivFourierTPhiThreeLe 2
  have hc : 0 < c := aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos
  have hmain : aux_variationBound (C_mainAuxTwo n)
      (fun x ↦ aux_mainBumpTwo_psi b k x) f.1 :=
    mainAuxTwo hn (aux_mainBumpTwo_psi b k)
      (aux_mainBumpTwo_psi_hypotheses b k) f
  have hphiThree' := aux_mainBumpOne_variationBound_const_mul c hc.le
    (C_mainAuxTwo n) (fun x ↦ aux_mainBumpTwo_psi b k x) f.1 hmain
  have hC : c ^ 2 * C_mainAuxTwo n = C_mainBumpTwo n := by
    dsimp [c]
    rw [C_mainBumpTwo]
    ring
  have hfun : (fun x ↦ c * aux_mainBumpTwo_psi b k x) =
      windowBasedBumpFunctions.phiThree b k := by
    funext x
    rw [aux_mainBumpTwo_psi_apply]
    change c * (c⁻¹ * windowBasedBumpFunctions.phiThree b k x) =
      windowBasedBumpFunctions.phiThree b k x
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hC, hfun] at hphiThree'
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hrescaled' := aux_mainBumpOne_variationBound_const_mul a⁻¹
    (inv_nonneg.mpr ha.le) (C_mainBumpTwo n)
    (windowBasedBumpFunctions.phiThree b k) f.1 hphiThree'
  have hfunrescaled : (fun x ↦ a⁻¹ * windowBasedBumpFunctions.phiThree b k x) =
      aux_oneRescaled ((2 : ℝ) ^ (-k)) (windowBasedBumpFunctions.phiZero b k) := by
    funext x
    rw [aux_mainBumpTwo_phiThree_eq_rescaled]
    dsimp [a]
    field_simp [show (2 : ℝ) ^ k ≠ 0 by positivity]
  rw [hfunrescaled] at hrescaled'
  have hrescaled := aux_mainBumpTwo_variationBound_of_oneRescaled ((2 : ℝ) ^ (-k))
    (by positivity) ((a⁻¹) ^ 2 * C_mainBumpTwo n)
    (windowBasedBumpFunctions.phiZero b k) f.1 hrescaled'
  have hCscale : (a⁻¹) ^ 2 * C_mainBumpTwo n =
      C_mainBumpTwo n * (2 : ℝ) ^ (-2 * k) := by
    dsimp [a]
    rw [← zpow_neg]
    rw [show (-2 * k : ℤ) = (-k) * 2 by ring, zpow_mul]
    exact mul_comm _ _
  rw [hCscale] at hrescaled
  exact hrescaled

theorem aux_mainBumpTwo_C_mainAuxTwo_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_mainAuxTwo n < (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 := by
  unfold C_mainAuxTwo
  calc
    24 * C_mainAuxOne n < 24 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) :=
      mul_lt_mul_of_pos_left (aux_constantMainAuxOne_sharp hn) (by norm_num)
    _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 := by
      calc
        24 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 573) =
            ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 5) * (2 : ℝ) ^ 573 := by
              norm_num
              set_option exponentiation.threshold 1000 in
                ring
        _ = (4191 / 8192 : ℝ) * ((2 : ℝ) ^ 5 * (2 : ℝ) ^ 573) := by
          set_option exponentiation.threshold 1000 in
            ring
        _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 := by rw [← pow_add]

theorem aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_sharp :
    C_absDerivFourierTPhiThreeLe 2 <
      (41 / 64 : ℝ) * (2 : ℝ) ^ 41 := by
  set_option exponentiation.threshold 1000 in
    norm_num [C_absDerivFourierTPhiThreeLe, C_absDerivFourierPhiThreeLe,
      C_uniPair]

/--
**Lemma (constant $C_{\text{lem:mainbump2}}$).**

$$
C_{\text{lem:mainbump2}}<\tfrac{27}{32}2^{658}<2^{658}.
$$

See also `Auto.mainBumpTwo`.
-/
theorem constantMainBumpTwo {n : ℕ} (hn : 2 ≤ n) :
    C_mainBumpTwo n < (27 / 32 : ℝ) * (2 : ℝ) ^ 658 := by
  let c : ℝ := C_absDerivFourierTPhiThreeLe 2
  let d : ℝ := (41 / 64 : ℝ) * (2 : ℝ) ^ 41
  have hc : 0 < c := aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_pos
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hcd : c < d := by
    simpa [c, d] using aux_mainBumpTwo_C_absDerivFourierTPhiThreeLe_two_sharp
  have hsq : c ^ 2 < d ^ 2 :=
    (sq_lt_sq₀ hc.le hd.le).2 hcd
  have haux := aux_mainBumpTwo_C_mainAuxTwo_sharp hn
  unfold C_mainBumpTwo
  calc
    C_mainAuxTwo n * C_absDerivFourierTPhiThreeLe 2 ^ 2 <
        ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) *
          C_absDerivFourierTPhiThreeLe 2 ^ 2 := by
      exact mul_lt_mul_of_pos_right haux (sq_pos_of_pos hc)
    _ < ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) * d ^ 2 := by
      exact mul_lt_mul_of_pos_left (by simpa [c] using hsq) (by positivity)
    _ = ((4191 / 8192 : ℝ) * (41 / 64 : ℝ) ^ 2) * (2 : ℝ) ^ 660 := by
      dsimp [d]
      rw [mul_pow, ← pow_mul]
      calc
        (4191 / 8192 : ℝ) * (2 : ℝ) ^ 578 *
            ((41 / 64 : ℝ) ^ 2 * (2 : ℝ) ^ (41 * 2)) =
            ((4191 / 8192 : ℝ) * (41 / 64 : ℝ) ^ 2) *
              ((2 : ℝ) ^ 578 * (2 : ℝ) ^ (41 * 2)) := by
                set_option exponentiation.threshold 1000 in
                  ring
        _ = ((4191 / 8192 : ℝ) * (41 / 64 : ℝ) ^ 2) * (2 : ℝ) ^ 660 := by
          rw [← pow_add]
    _ < (27 / 128 : ℝ) * (2 : ℝ) ^ 660 := by
      apply mul_lt_mul_of_pos_right
      · norm_num
      · positivity
    _ = (27 / 32 : ℝ) * (2 : ℝ) ^ 658 := by
      rw [show (660 : ℕ) = 2 + 658 by norm_num, pow_add]
      norm_num
      set_option exponentiation.threshold 1000 in
        ring

/-- The constant in Lemma `Auto.leftBump`. -/
noncomputable def C_leftBump (n : ℕ) : ℝ :=
  C_mainAuxTwo n * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2

noncomputable def aux_leftBump_psi (b : windowBasedBumpFunctions) :
    SchwartzMap ℝ ℝ :=
  ((2 : ℝ) ^ 14 * C_uniPair)⁻¹ • thetaTildeSchwartz b

theorem aux_leftBump_psi_apply (b : windowBasedBumpFunctions) (x : ℝ) :
    aux_leftBump_psi b x = ((2 : ℝ) ^ 14 * C_uniPair)⁻¹ *
      windowBasedBumpFunctions.thetaTilde b x := by
  simp [aux_leftBump_psi, smul_apply, thetaTildeSchwartz_apply]

theorem aux_leftBump_psi_fourier (b : windowBasedBumpFunctions) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) xi =
      ((((2 : ℝ) ^ 14 * C_uniPair)⁻¹ : ℝ) : ℂ) *
        FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) xi := by
  rw [show (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) =
      fun x => ((((2 : ℝ) ^ 14 * C_uniPair)⁻¹ *
        windowBasedBumpFunctions.thetaTilde b x : ℝ) : ℂ) by
        funext x
        rw [aux_leftBump_psi_apply],
    aux_mainAuxOne_fourier_real_const_mul]

theorem aux_leftBump_psi_hypotheses (b : windowBasedBumpFunctions) :
    aux_mainAuxiliaryTwoHypotheses (aux_leftBump_psi b) := by
  let c : ℝ := (2 : ℝ) ^ 14 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  constructor
  · constructor
    · intro xi hxi
      have hne := Function.mem_support.mp hxi
      rw [aux_leftBump_psi_fourier] at hne
      have hrawne : FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) xi ≠ 0 :=
        (mul_ne_zero_iff.mp hne).2
      have hprim := thetaPrimitive b 2 (by norm_num) (by norm_num [N_uniPair])
      exact hprim.1.2 (hprim.1.1 (Function.mem_support.mpr hrawne))
    · intro m hm xi
      change ‖iteratedDeriv m
        (fun z : ℝ => FourierTransform.fourier
          (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) z) xi‖ ≤ 1
      have hformula :
          (fun z : ℝ => FourierTransform.fourier
            (fun x : ℝ => (aux_leftBump_psi b x : ℂ)) z) =
            fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier
              (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) z := by
        funext z
        simpa [c] using aux_leftBump_psi_fourier b z
      rw [hformula, iteratedDeriv_const_mul_field]
      have hraw := thetaTildeFourier_deriv_bound b m (Nat.le_of_lt hm) xi
      change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
        (FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))) xi‖ ≤ 1
      calc
        ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
            (FourierTransform.fourier
              (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))) xi‖ =
            c⁻¹ * ‖iteratedDeriv m
              (FourierTransform.fourier
                (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))) xi‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hc)]
        _ ≤ c⁻¹ * c :=
          mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
        _ = 1 := by field_simp [hc.ne']
  · intro m hm xi
    have hsmooth : ContDiff ℝ 1 (fun y : ℝ => aux_leftBump_psi b y) :=
      (aux_leftBump_psi b).smooth 1
    rw [← aux_mainBumpOne_T_cast_eq _ hsmooth]
    change ‖iteratedDeriv m
      (fun z : ℝ => FourierTransform.fourier (fun x : ℝ =>
        (Auto.aux_sd_T
          (fun y => aux_leftBump_psi b y) x : ℂ)) z) xi‖ ≤ 1
    have hsmoothTheta : ContDiff ℝ 1
        (windowBasedBumpFunctions.thetaTilde b) := by
      have hfun : (fun x : ℝ => thetaTildeSchwartz b x) =
          windowBasedBumpFunctions.thetaTilde b := by
        funext x
        exact thetaTildeSchwartz_apply b x
      rw [← hfun]
      exact (thetaTildeSchwartz b).smooth 1
    have hformula :
        (fun z : ℝ => FourierTransform.fourier (fun x : ℝ =>
          (Auto.aux_sd_T
            (fun y => aux_leftBump_psi b y) x : ℂ)) z) =
          fun z => ((c⁻¹ : ℝ) : ℂ) * FourierTransform.fourier
            (fun x : ℝ => (Auto.aux_sd_T
              (windowBasedBumpFunctions.thetaTilde b) x : ℂ)) z := by
      funext z
      rw [show (fun y : ℝ => aux_leftBump_psi b y) =
          fun y => c⁻¹ * windowBasedBumpFunctions.thetaTilde b y by
            funext y
            simpa [c] using aux_leftBump_psi_apply b y,
        aux_mainBumpOne_T_const_mul c⁻¹ (windowBasedBumpFunctions.thetaTilde b) hsmoothTheta,
        aux_mainAuxOne_fourier_real_const_mul]
    rw [hformula, iteratedDeriv_const_mul_field]
    have hraw := tThetaTildeFourier_deriv_bound b m hm xi
    change ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
      (FourierTransform.fourier (fun x : ℝ =>
        (Auto.aux_sd_T
          (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) xi‖ ≤ 1
    calc
      ‖((c⁻¹ : ℝ) : ℂ) * iteratedDeriv m
          (FourierTransform.fourier (fun x : ℝ =>
            (Auto.aux_sd_T
              (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) xi‖ =
          c⁻¹ * ‖iteratedDeriv m
            (FourierTransform.fourier (fun x : ℝ =>
              (Auto.aux_sd_T
                (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) xi‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hc)]
      _ ≤ c⁻¹ * c :=
        mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hc.le)
      _ = 1 := by field_simp [hc.ne']

theorem aux_leftBump_phiOne_eq_scaled_thetaTilde (b : windowBasedBumpFunctions)
    (k : ℤ) :
    windowBasedBumpFunctions.phiOne b k =
      fun x => (2 : ℝ) ^ k *
        aux_oneRescaled ((2 : ℝ) ^ k) (windowBasedBumpFunctions.thetaTilde b) x := by
  funext x
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let g : ℝ → ℝ := fun z => aux_indicator (Set.Ici 0) z *
    windowBasedBumpFunctions.theta b (a⁻¹ * x - z)
  have hind (y : ℝ) :
      aux_indicator (Set.Ici 0) (a⁻¹ * y) = aux_indicator (Set.Ici 0) y := by
    have hmem : a⁻¹ * y ∈ Set.Ici (0 : ℝ) ↔ y ∈ Set.Ici (0 : ℝ) := by
      change 0 ≤ a⁻¹ * y ↔ 0 ≤ y
      exact mul_nonneg_iff_of_pos_left (inv_pos.mpr ha)
    unfold aux_indicator
    by_cases hy : y ∈ Set.Ici (0 : ℝ)
    · have hy' : a⁻¹ * y ∈ Set.Ici (0 : ℝ) := hmem.mpr hy
      simp [hy, hy']
    · have hy' : a⁻¹ * y ∉ Set.Ici (0 : ℝ) := fun h => hy (hmem.mp h)
      simp [hy, hy']
  have hleft :
      (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
        Auto.aux_realRescaled a
          (windowBasedBumpFunctions.theta b) (x - y)) =
        a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := by
    calc
      (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
          Auto.aux_realRescaled a
            (windowBasedBumpFunctions.theta b) (x - y)) =
          ∫ y : ℝ, a⁻¹ * g (a⁻¹ * y) := by
            apply integral_congr_ae
            filter_upwards [] with y
            dsimp [g, Auto.aux_realRescaled]
            rw [hind]
            ring_nf
      _ = a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := by
        rw [integral_const_mul]
  have hchange := Measure.integral_comp_inv_mul_left g a
  rw [abs_of_pos ha, smul_eq_mul] at hchange
  change (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
      Auto.aux_realRescaled a
        (windowBasedBumpFunctions.theta b) (x - y)) =
    a * (a⁻¹ * ∫ y : ℝ, aux_indicator (Set.Ici 0) y *
      windowBasedBumpFunctions.theta b (a⁻¹ * x - y))
  calc
    (∫ y : ℝ, aux_indicator (Set.Ici 0) y *
        Auto.aux_realRescaled a
          (windowBasedBumpFunctions.theta b) (x - y)) =
        a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := hleft
    _ = a⁻¹ * (a * ∫ y : ℝ, g y) := by rw [hchange]
    _ = ∫ y : ℝ, g y := by field_simp [ha.ne']
    _ = a * (a⁻¹ * ∫ y : ℝ, aux_indicator (Set.Ici 0) y *
        windowBasedBumpFunctions.theta b (a⁻¹ * x - y)) := by
          dsimp [g]
          field_simp [ha.ne']


/--
**Lemma.**

For every $k\le-1$,

$$
\|A_t(\varphi_{1,k})\|_{V_{2,J}(t\in(0,\infty);L^2)}^2
\le C_{\text{lem:leftbump}}2^{2k}J^{\alpha(n)},
$$

where

$$
C_{\text{lem:leftbump}}
=C_{\text{lem:main\_aux2}}(2^{14}C_{\text{Universal pair}})^2.
$$

See also `Auto.leftBump`,
`Auto.mainAuxTwo`,
`Auto.uniPair`.
-/
theorem leftBump {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_variationBound (C_leftBump n * (2 : ℝ) ^ (2 * k))
      (windowBasedBumpFunctions.phiOne b k) f.1 := by
  have _ := hk
  let c : ℝ := (2 : ℝ) ^ 14 * C_uniPair
  have hc : 0 < c := by
    dsimp [c]
    norm_num [C_uniPair]
  have hmain : aux_variationBound (C_mainAuxTwo n)
      (fun x => aux_leftBump_psi b x) f.1 :=
    mainAuxTwo hn (aux_leftBump_psi b) (aux_leftBump_psi_hypotheses b) f
  have htheta' := aux_mainBumpOne_variationBound_const_mul c hc.le (C_mainAuxTwo n)
    (fun x => aux_leftBump_psi b x) f.1 hmain
  have hC : c ^ 2 * C_mainAuxTwo n = C_leftBump n := by
    dsimp [c, C_leftBump]
    ring
  have hfun : (fun x => c * aux_leftBump_psi b x) =
      windowBasedBumpFunctions.thetaTilde b := by
    funext x
    rw [aux_leftBump_psi_apply]
    change c * (c⁻¹ * windowBasedBumpFunctions.thetaTilde b x) =
      windowBasedBumpFunctions.thetaTilde b x
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hC, hfun] at htheta'
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hcomp : aux_oneRescaled a⁻¹
      (aux_oneRescaled a (windowBasedBumpFunctions.thetaTilde b)) =
      windowBasedBumpFunctions.thetaTilde b := by
    funext x
    unfold aux_oneRescaled
    field_simp [ha.ne']
  rw [← hcomp] at htheta'
  have hrescaled := aux_mainBumpTwo_variationBound_of_oneRescaled a⁻¹ (inv_pos.mpr ha)
    (C_leftBump n) (aux_oneRescaled a (windowBasedBumpFunctions.thetaTilde b))
    f.1 htheta'
  have hphi' := aux_mainBumpOne_variationBound_const_mul a ha.le (C_leftBump n)
    (aux_oneRescaled a (windowBasedBumpFunctions.thetaTilde b)) f.1 hrescaled
  have hphifun : (fun x => a * aux_oneRescaled a
      (windowBasedBumpFunctions.thetaTilde b) x) =
      windowBasedBumpFunctions.phiOne b k := by
    funext x
    dsimp [a]
    exact congrFun (aux_leftBump_phiOne_eq_scaled_thetaTilde b k).symm x
  have hCscale : a ^ 2 * C_leftBump n =
      C_leftBump n * (2 : ℝ) ^ (2 * k) := by
    dsimp [a]
    calc
      ((2 : ℝ) ^ k) ^ 2 * C_leftBump n =
          C_leftBump n * ((2 : ℝ) ^ k) ^ 2 := by ring
      _ = C_leftBump n * (2 : ℝ) ^ (k * 2) := by
        rw [zpow_mul]
        rfl
      _ = C_leftBump n * (2 : ℝ) ^ (2 * k) := by
        congr 2
        ring
  rw [hCscale, hphifun] at hphi'
  exact hphi'


/--
**Lemma (constant $C_{\text{lem:leftbump}}$).**

$$
C_{\text{lem:leftbump}}<\tfrac{33}{64}2^{636}<2^{636}.
$$

See also `Auto.leftBump`.
-/
theorem constantLeftBump {n : ℕ} (hn : 2 ≤ n) :
    C_leftBump n < (33 / 64 : ℝ) * (2 : ℝ) ^ 636 := by
  have haux := aux_mainBumpTwo_C_mainAuxTwo_sharp hn
  have hcpos : 0 < ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 := by
    norm_num [C_uniPair]
  have hcsq : ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 = (2 : ℝ) ^ 58 := by
    rw [C_uniPair, ← pow_add, ← pow_mul]
  unfold C_leftBump
  calc
    C_mainAuxTwo n * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 <
        ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) *
          ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 :=
      mul_lt_mul_of_pos_right haux hcpos
    _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 636 := by
      rw [hcsq]
      calc
        ((4191 / 8192 : ℝ) * (2 : ℝ) ^ 578) * (2 : ℝ) ^ 58 =
            (4191 / 8192 : ℝ) * ((2 : ℝ) ^ 578 * (2 : ℝ) ^ 58) := by
              set_option exponentiation.threshold 1000 in
                ring
        _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ (578 + 58) := by
              rw [← pow_add]
        _ = (4191 / 8192 : ℝ) * (2 : ℝ) ^ 636 := by norm_num
    _ < (33 / 64 : ℝ) * (2 : ℝ) ^ 636 := by
      apply mul_lt_mul_of_pos_right
      · norm_num
      · positivity


/-- Fubini for a first prism form whose kernel is a compact parameter integral. -/
theorem aux_leftBumpOneShort_prismBrascampLiebForm_setIntegral
    {d : ℕ} (K : ℝ → KKernel 1) (Kint : KKernel 1)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (hKint : ∀ z : RealVector 1 × ℝ,
      Kint z = ∫ t : ℝ in Set.Icc (1 : ℝ) 2, K t z)
    (hInt : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume)) :
    prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) Kint
      (fun i x => F i x) =
      ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
        prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
          (fun i x => F i x) := by
  let P : KKernel 1 → ((RealVector 1 × RealVector 1) × RealVector (d + 1)) → ℝ :=
    fun L q =>
      L (q.1.2 - q.1.1, coordinateSum q.1.1 + coordinateSum q.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.1 q.2 h i)
  have hInt' : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) => P (K q.1) q.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
    simpa [P] using hInt
  have hPint : Integrable (P Kint) := by
    have h := hInt'.integral_prod_right
    refine h.congr ?_
    filter_upwards [] with q
    dsimp [P]
    rw [hKint]
    rw [integral_mul_const]
  have hIntSwap : Integrable
      (Function.uncurry (fun q : ((RealVector 1 × RealVector 1) ×
        RealVector (d + 1)) => fun t : ℝ => P (K t) q))
      (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
    convert hInt'.swap using 1
    funext q
    rcases q with ⟨q, t⟩
    rfl
  change (∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1),
      P Kint (y, x)) = _
  calc
    (∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1),
        P Kint (y, x)) =
        ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
          P Kint q := by
          simpa only [Measure.volume_eq_prod] using
            (integral_prod (P Kint) hPint).symm
    _ = ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
        ∫ t : ℝ in Set.Icc (1 : ℝ) 2, P (K t) q := by
          apply integral_congr_ae
          filter_upwards [] with q
          dsimp [P]
          rw [hKint]
          rw [integral_mul_const]
    _ = ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
        ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
          P (K t) q := by
          simpa only [Function.uncurry, Measure.volume_eq_prod] using
            integral_integral_swap hIntSwap
    _ = ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
        prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
          (fun i x => F i x) := by
          apply integral_congr_ae
          filter_upwards [hInt'.prod_right_ae] with t ht
          calc
            ∫ q : ((RealVector 1 × RealVector 1) × RealVector (d + 1)),
                P (K t) q =
                ∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1),
                  P (K t) (y, x) := by
                    simpa only [Measure.volume_eq_prod] using
                      integral_prod (P (K t)) ht
            _ = prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
                (fun i x => F i x) := by
                  rfl

/-- The nonnegative extended-real form of the preceding compact-parameter Fubini step. -/
theorem aux_leftBumpOneShort_lintegral_energy_eq_prism_of_setIntegral
    {d : ℕ} (K : ℝ → KKernel 1) (Kint : KKernel 1)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (E : ℝ → ℝ≥0∞)
    (hKint : ∀ z : RealVector 1 × ℝ,
      Kint z = ∫ t : ℝ in Set.Icc (1 : ℝ) 2, K t z)
    (hInt : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume))
    (hPint : Integrable (fun t : ℝ =>
      prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
        (fun i x => F i x)) (volume.restrict (Set.Icc (1 : ℝ) 2)))
    (hPnonneg : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      0 ≤ prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
        (fun i x => F i x))
    (hE : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      E t = ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
          (fun i x => F i x))) :
    ∫⁻ t in Set.Icc (1 : ℝ) 2, E t =
      ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) Kint
          (fun i x => F i x)) := by
  calc
    ∫⁻ t in Set.Icc (1 : ℝ) 2, E t =
        ∫⁻ t in Set.Icc (1 : ℝ) 2, ENNReal.ofReal
          (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
            (fun i x => F i x)) := by
          exact lintegral_congr_ae hE
    _ = ENNReal.ofReal (∫ t : ℝ in Set.Icc (1 : ℝ) 2,
          prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
            (fun i x => F i x)) := by
          exact (ofReal_integral_eq_lintegral_ofReal hPint hPnonneg).symm
    _ = ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) Kint
          (fun i x => F i x)) := by
          rw [← aux_leftBumpOneShort_prismBrascampLiebForm_setIntegral K Kint F hKint hInt]

noncomputable def aux_leftBumpOneShort_integralM
    (s : ℝ) (psi : SchwartzMap ℝ ℝ) : MKernel 1 :=
  fun y => aux_integralFctKernelAtScale s (fun x => psi x)
    (WithLp.toLp 2 ![y.1 0, y.2 0])

noncomputable def aux_leftBumpOneShort_scaleK
    (s : ℝ) (psi : SchwartzMap ℝ ℝ) (t : ℝ) : KKernel 1 :=
  fun z => t⁻¹ * Auto.aux_bf_realRescaled (s * t)
      (fun x => psi x) (z.1 0 + z.2) *
    Auto.aux_bf_realRescaled (s * t)
      (fun x => psi x) z.2

theorem aux_leftBumpOneShort_mToK_integralM_eq_setIntegral
    (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (z : RealVector 1 × ℝ) :
    mToK 1 (by omega) (aux_leftBumpOneShort_integralM s psi) z =
      ∫ t : ℝ in Set.Icc (1 : ℝ) 2, aux_leftBumpOneShort_scaleK s psi t z := by
  unfold mToK
  rw [aux_integral_realVector_zero]
  have hpoint : mToKPoint 1 (by omega) z (default : RealVector 0) =
      ((fun _ : Fin 1 => z.1 0 + z.2), fun _ : Fin 1 => z.2) := by
    apply Prod.ext <;> funext i <;> fin_cases i <;>
      simp [mToKPoint, lastIndex, coordinateSum]
  rw [hpoint]
  unfold aux_leftBumpOneShort_integralM aux_leftBumpOneShort_scaleK
  rw [integralFctKernelAtScale_eq s hs.ne' (fun x => psi x)
    (WithLp.toLp 2 ![z.1 0 + z.2, z.2])]
  apply integral_congr_ae
  filter_upwards [] with t
  simp
  ring

theorem aux_leftBumpOneShort_scaleK_eq_mToK_tensor
    (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t) :
    aux_leftBumpOneShort_scaleK s psi t = fun z => t⁻¹ *
      mToK 1 (by omega)
        (fun y : RealVector 1 × RealVector 1 =>
          aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.1 0) *
            aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.2 0)) z := by
  funext z
  unfold aux_leftBumpOneShort_scaleK
  rw [Auto.aux_aToLambda.mToK_oneTensorSquare_eq]
  rw [aux_mainAuxOne_windowSchwartz_apply, aux_mainAuxOne_windowSchwartz_apply]
  simp only [Auto.aux_bf_realRescaled, aux_windowRescale]
  ring

theorem aux_leftBumpOneShort_prism_scaleK_eq_tensor
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
      (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x) =
      t⁻¹ * prismForm (d + 1) 1 (by omega) (by omega)
        (fun y : RealVector 1 × RealVector 1 =>
          aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.1 0) *
            aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.2 0))
        (fun i x => F i x) := by
  rw [show aux_leftBumpOneShort_scaleK s psi t = fun z => t⁻¹ *
      mToK 1 (by omega)
        (fun y : RealVector 1 × RealVector 1 =>
          aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.1 0) *
            aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht) (y.2 0)) z by
      exact aux_leftBumpOneShort_scaleK_eq_mToK_tensor s hs psi t ht]
  unfold prismBrascampLiebForm prismForm
  simp only [mul_assoc]
  simp_rw [integral_const_mul]
  rfl

theorem aux_leftBumpOneShort_energy_eq_scaleK_prism
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    ENNReal.ofReal t⁻¹ *
      eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
        (fun i x => f i x)) 2 volume ^ 2 =
      ENNReal.ofReal
        (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
          (aux_leftBumpOneShort_scaleK s psi t)
          (fun i x => Auto.aux_aToLambda.transformedFunctions f i x)) := by
  rw [← aux_mainAuxOne_twistedAverage_window psi (s * t) (mul_pos hs ht)]
  rw [aToLambda_transformed]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le)]
  congr 1
  exact (aux_leftBumpOneShort_prism_scaleK_eq_tensor d s hs psi t ht
    (Auto.aux_aToLambda.transformedFunctions f)).symm


theorem aux_leftBumpOneShort_prism_parameter_integrable
    {d : ℕ} (K : ℝ → KKernel 1)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (hInt : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume)) :
    Integrable (fun t : ℝ =>
      prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) (K t)
        (fun i x => F i x)) (volume.restrict (Set.Icc (1 : ℝ) 2)) := by
  let P : KKernel 1 → ((RealVector 1 × RealVector 1) × RealVector (d + 1)) → ℝ :=
    fun L q =>
      L (q.1.2 - q.1.1, coordinateSum q.1.1 + coordinateSum q.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.1 q.2 h i)
  have hInt' : Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) => P (K q.1) q.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
    simpa [P] using hInt
  have h := hInt'.integral_prod_left
  refine h.congr ?_
  filter_upwards [hInt'.prod_right_ae] with t ht
  dsimp [P]
  simpa [P, prismBrascampLiebForm, Measure.volume_eq_prod] using
    (integral_prod (P (K t)) ht)

theorem aux_leftBumpOneShort_prism_scaleK_nonnegative
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) (t : ℝ) (ht : 0 < t)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    0 ≤ prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
      (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x) := by
  rw [aux_leftBumpOneShort_prism_scaleK_eq_tensor d s hs psi t ht F]
  apply mul_nonneg (inv_nonneg.mpr ht.le)
  apply aux_prism_one_rankOne_nonnegative (d + 1) (by omega) 1 (by norm_num)
    (aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht)) F
  · exact mToK_memW0 (d + 1) 1 (by omega) (by omega) _
      (Auto.aux_aToLambda.oneTensorSquare_memW0
        (aux_mainAuxOne_windowSchwartz psi (s * t) (mul_pos hs ht)))
  · intro u
    rw [Auto.aux_aToLambda.mToK_oneTensorSquare_eq]
    ring

theorem aux_leftBumpOneShort_scaleK_triple_integrable
    (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ) :
    Integrable (fun q : ℝ × (RealVector 1 × ℝ) =>
      aux_leftBumpOneShort_scaleK s psi q.1 q.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (1 : ℝ) 2)
  let H : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ := fun q =>
    Auto.aux_bf_realRescaled (s * q.1) (fun x => psi x) (q.2 0) *
      Auto.aux_bf_realRescaled (s * q.1) (fun x => psi x) (q.2 1) * q.1⁻¹
  have hH : Integrable H (μ.prod volume) := by
    simpa [μ, H] using
      (integralFctKernelAtScale_triple_integrable psi s hs).re
  let e1 : RealVector 1 ≃ᵐ ℝ :=
    MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have he1 : MeasurePreserving e1 volume volume := by
    simpa [e1] using volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
  have hpre : MeasurePreserving (fun w : RealVector 1 × ℝ => (e1 w.1, w.2))
      volume volume := by
    change MeasurePreserving (Prod.map e1 id) volume volume
    simpa only [Measure.volume_eq_prod] using
      he1.prod (MeasurePreserving.id (volume : Measure ℝ))
  have hshear : MeasurePreserving (fun p : ℝ × ℝ => (p.1 + p.2, p.2))
      volume volume := by
    change MeasurePreserving (fun p : ℝ × ℝ => (p.1 + p.2, p.2))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume)
    exact measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  let e2 : EuclideanSpace ℝ (Fin 2) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he2 : MeasurePreserving e2 volume volume := by
    simpa [e2] using
      (PiLp.volume_preserving_toLp (Fin 2)).symm.trans
        (MeasureTheory.volume_preserving_finTwoArrow ℝ)
  have he2inv : MeasurePreserving e2.symm volume volume := he2.symm e2
  let e : RealVector 1 × ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun w => e2.symm (e1 w.1 + w.2, w.2)
  have he : MeasurePreserving e volume volume := by
    have hcomp := he2inv.comp (hshear.comp hpre)
    convert hcomp using 1
    funext w
    rfl
  have heprod : MeasurePreserving (Prod.map id e) (μ.prod volume) (μ.prod volume) :=
    (MeasurePreserving.id μ).prod he
  have hcomp := heprod.integrable_comp_of_integrable hH
  refine hcomp.congr ?_
  filter_upwards [] with q
  dsimp [Function.comp_apply, H, e, e1, e2, aux_leftBumpOneShort_scaleK]
  simp
  ring

/--
The parameterized version of the absolute-integrability core for a first prism.
The scale parameter is carried inertly through the standard prism coordinates.
-/
theorem aux_leftBumpOneShort_parameterized_prismIntegrand
    (d : ℕ) (μ : Measure ℝ) [SFinite μ]
    (K : ℝ → KKernel 1)
    (hKmeas : Measurable (Function.uncurry K))
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ)
    (hcore : Integrable (fun q : ℝ ×
      ((RealVector 1 × ℝ) × RealVector (d + 1)) =>
      K q.1 q.2.1 *
        F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega)
          (0 : Fin (d + 1))) q.2.2)
      (μ.prod volume)) :
    Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      K q.1 (q.2.1.2 - q.2.1.1,
        coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega)
              q.2.1 q.2.2 h i))
      (μ.prod volume) := by
  classical
  let n : ℕ := d + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  let I := (Fin 1 → Fin 2) × Fin n
  let a : I := (fun _ => 0, 0)
  let P : I → (RealVector 1 × ℝ) × RealVector n → ℝ := fun hi w =>
    F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)
      (aux_prismPullback n 1 hn hi.1 hi.2 w.1.1 w.1.2 w.2)
  let D : ℝ × ((RealVector 1 × ℝ) × RealVector n) → ℝ := fun q =>
    K q.1 q.2.1 * P a q.2
  let R : (RealVector 1 × ℝ) × RealVector n → ℝ := fun w =>
    ∏ hi ∈ (Finset.univ.erase a), P hi w
  let C : ℝ := ∏ hi ∈ (Finset.univ.erase a),
    SchwartzMap.seminorm ℝ 0 0 (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2))
  let H : ℝ × ((RealVector 1 × ℝ) × RealVector n) → ℝ := fun q =>
    K q.1 q.2.1 * ∏ hi : I, P hi q.2
  have hPmeas (hi : I) : Measurable (P hi) := by
    dsimp [P]
    exact (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)).continuous.measurable.comp
      (aux_measurable_prismPullback n 1 hn hi.1 hi.2)
  have hRbound (w : (RealVector 1 × ℝ) × RealVector n) : ‖R w‖ ≤ C := by
    dsimp [R, C]
    calc
      ‖∏ hi ∈ Finset.univ.erase a, P hi w‖ ≤
          ∏ hi ∈ Finset.univ.erase a, ‖P hi w‖ :=
        Finset.norm_prod_le _ _
      _ ≤ ∏ hi ∈ Finset.univ.erase a,
          SchwartzMap.seminorm ℝ 0 0
            (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)) := by
          gcongr with hi hhi
          exact (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)).norm_le_seminorm ℝ _
  have hfactor (q : ℝ × ((RealVector 1 × ℝ) × RealVector n)) : H q = D q * R q.2 := by
    dsimp [H, D, R]
    rw [← Finset.mul_prod_erase Finset.univ (fun hi => P hi q.2)
      (Finset.mem_univ a)]
    ring
  have hbound (q : ℝ × ((RealVector 1 × ℝ) × RealVector n)) :
      ‖H q‖ ≤ C * ‖D q‖ := by
    rw [hfactor]
    calc
      ‖D q * R q.2‖ = ‖D q‖ * ‖R q.2‖ := norm_mul _ _
      _ ≤ ‖D q‖ * C := mul_le_mul_of_nonneg_left (hRbound q.2) (norm_nonneg _)
      _ = C * ‖D q‖ := mul_comm _ _
  let skew : (RealVector 1 × ℝ) × RealVector n →
      (RealVector 1 × ℝ) × RealVector n :=
    fun w => (w.1, aux_prismPullback n 1 hn a.1 a.2 w.1.1 w.1.2 w.2)
  have hskew : MeasurePreserving skew volume volume := by
    dsimp [skew]
    exact aux_measurePreserving_prismPullbackSkew n 1 hn a.1 a.2
  let liftSkew : ℝ × ((RealVector 1 × ℝ) × RealVector n) →
      ℝ × ((RealVector 1 × ℝ) × RealVector n) :=
    Prod.map id skew
  have hliftSkew : MeasurePreserving liftSkew (μ.prod volume) (μ.prod volume) := by
    dsimp [liftSkew]
    exact (MeasurePreserving.id μ).prod hskew
  have hcore' : Integrable (fun q : ℝ × ((RealVector 1 × ℝ) × RealVector n) =>
      K q.1 q.2.1 *
        F (prismIndex (n := n) (k := 1) (by omega) hn a.2) q.2.2)
      (μ.prod volume) := by
    simpa [a] using hcore
  have hD : Integrable D (μ.prod volume) := by
    have hcomp := hliftSkew.integrable_comp_of_integrable hcore'
    simpa [D, liftSkew, P, Function.comp_def] using hcomp
  have hKsource : Measurable (fun q : ℝ × ((RealVector 1 × ℝ) × RealVector n) =>
      K q.1 q.2.1) := by
    exact hKmeas.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hHmeas : Measurable H := by
    dsimp [H]
    apply hKsource.mul
    apply Finset.measurable_fun_prod Finset.univ
    intro hi _
    exact (hPmeas hi).comp measurable_snd
  have hH : Integrable H (μ.prod volume) := by
    have hDom : Integrable (fun q => C * ‖D q‖) (μ.prod volume) := hD.norm.const_mul C
    exact hDom.mono' hHmeas.aestronglyMeasurable (ae_of_all _ hbound)
  let assoc : RealVector 1 × (ℝ × RealVector n) ≃ᵐ
      (RealVector 1 × ℝ) × RealVector n := MeasurableEquiv.prodAssoc.symm
  have hassoc : MeasurePreserving assoc volume volume := by
    dsimp [assoc]
    exact (MeasureTheory.volume_preserving_prodAssoc).symm _
  let liftAssoc : ℝ × (RealVector 1 × (ℝ × RealVector n)) ≃ᵐ
      ℝ × ((RealVector 1 × ℝ) × RealVector n) :=
    (MeasurableEquiv.refl ℝ).prodCongr assoc
  have hliftAssoc : MeasurePreserving liftAssoc (μ.prod volume) (μ.prod volume) := by
    dsimp [liftAssoc]
    exact (MeasurePreserving.id μ).prod hassoc
  let G : ℝ × ((RealVector 1 × RealVector 1) × RealVector n) → ℝ := fun q =>
    K q.1 (q.2.1.2 - q.2.1.1, coordinateSum q.2.1.1 + coordinateSum q.2.2) *
      ∏ h : Fin 1 → Fin 2, ∏ i : Fin n,
        F (prismIndex (n := n) (k := 1) (by omega) hn i)
          (prismPoint (n := n) (k := 1) (by omega) hn q.2.1 q.2.2 h i)
  let liftCoords : ℝ × (RealVector 1 × (ℝ × RealVector n)) →
      ℝ × ((RealVector 1 × RealVector 1) × RealVector n) :=
    Prod.map id (aux_prismCoordinates n 1 hn)
  have hliftCoords : MeasurePreserving liftCoords (μ.prod volume) (μ.prod volume) := by
    dsimp [liftCoords]
    exact (MeasurePreserving.id μ).prod (aux_measurePreserving_prismCoordinates n 1 hn)
  have hGH : G ∘ liftCoords = H ∘ liftAssoc := by
    funext q
    dsimp [G, H, liftCoords, liftAssoc, assoc, P]
    rw [aux_prismCoordinates_kernelArguments n 1 hn q.2.1 q.2.2.1 q.2.2.2]
    congr 1
    change
      (∏ h : Fin 1 → Fin 2, ∏ i : Fin n,
        F (prismIndex (n := n) (k := 1) (by omega) hn i)
          (prismPoint (n := n) (k := 1) (by omega) hn
            (aux_prismCoordinates n 1 hn q.2).1
            (aux_prismCoordinates n 1 hn q.2).2 h i)) =
      ∏ hi : (Fin 1 → Fin 2) × Fin n,
        F (prismIndex (n := n) (k := 1) (by omega) hn hi.2)
          (aux_prismPullback n 1 hn hi.1 hi.2
            q.2.1 q.2.2.1 q.2.2.2)
    rw [← Fintype.prod_prod_type']
    apply Finset.prod_congr rfl
    intro hi _
    exact congrArg (F (prismIndex (n := n) (k := 1) (by omega) hn hi.2))
      (aux_prismPoint_eq_prismPullbackCoordinates n 1 (by omega) hn
        q.2.1 q.2.2.1 q.2.2.2 hi.1 hi.2)
  have hGcomp : Integrable (G ∘ liftCoords) (μ.prod volume) := by
    rw [hGH]
    exact hliftAssoc.integrable_comp_of_integrable hH
  have hGmeas : Measurable G := by
    dsimp [G]
    have harg : Measurable (fun q : ℝ ×
        ((RealVector 1 × RealVector 1) × RealVector n) =>
        (q.1, (q.2.1.2 - q.2.1.1,
          coordinateSum q.2.1.1 + coordinateSum q.2.2))) := by
      exact measurable_fst.prodMk
        (((measurable_snd.fst.snd.sub measurable_snd.fst.fst).prodMk
        (((aux_continuous_coordinateSum 1).measurable.comp measurable_snd.fst.fst).add
          ((aux_continuous_coordinateSum n).measurable.comp measurable_snd.snd))))
    have hkernel : Measurable (fun q : ℝ ×
        ((RealVector 1 × RealVector 1) × RealVector n) =>
        K q.1 (q.2.1.2 - q.2.1.1,
          coordinateSum q.2.1.1 + coordinateSum q.2.2)) := by
      simpa [Function.comp_def] using hKmeas.comp harg
    refine hkernel.mul ?_
    apply Finset.measurable_fun_prod Finset.univ
    intro h _
    apply Finset.measurable_fun_prod Finset.univ
    intro i _
    have hpointCont : Continuous (fun q : ℝ ×
        ((RealVector 1 × RealVector 1) × RealVector n) =>
        prismPoint (n := n) (k := 1) (by omega) hn q.2.1 q.2.2 h i) := by
      apply continuous_pi
      intro j
      unfold prismPoint concatVector
      split_ifs with hj
      · unfold cubeCorner
        split_ifs <;> fun_prop
      · unfold eraseVector
        fun_prop
    exact (F (prismIndex (n := n) (k := 1) (by omega) hn i)).continuous.measurable.comp
      hpointCont.measurable
  have hG := (hliftCoords.integrable_comp hGmeas.aestronglyMeasurable).mp hGcomp
  simpa [G] using hG

theorem aux_leftBumpOneShort_scaleK_prism_core_integrable
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    Integrable (fun q : ℝ × ((RealVector 1 × ℝ) × RealVector (d + 1)) =>
      aux_leftBumpOneShort_scaleK s psi q.1 q.2.1 *
        F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) (0 : Fin (d + 1)))
          q.2.2)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
  have hK := aux_leftBumpOneShort_scaleK_triple_integrable s hs psi
  have hF : Integrable
      (F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega)
        (0 : Fin (d + 1))) : RealVector (d + 1) → ℝ) :=
    (F _).integrable
  let assoc : ((ℝ × (RealVector 1 × ℝ)) × RealVector (d + 1)) ≃ᵐ
      ℝ × ((RealVector 1 × ℝ) × RealVector (d + 1)) :=
    MeasurableEquiv.prodAssoc
  have hassoc : MeasurePreserving assoc
      (((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume).prod volume)
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod (volume.prod volume)) := by
    dsimp [assoc]
    exact MeasureTheory.measurePreserving_prodAssoc _ _ _
  have hprod := hK.mul_prod hF
  have hcomp := (hassoc.symm assoc).integrable_comp_of_integrable hprod
  rw [Measure.volume_eq_prod (RealVector 1 × ℝ) (RealVector (d + 1))]
  convert hcomp using 1
  rfl

theorem aux_leftBumpOneShort_scaleK_prism_joint_integrable
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ)
    (F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ) :
    Integrable (fun q : ℝ ×
      ((RealVector 1 × RealVector 1) × RealVector (d + 1)) =>
      aux_leftBumpOneShort_scaleK s psi q.1 (q.2.1.2 - q.2.1.1,
        coordinateSum q.2.1.1 + coordinateSum q.2.2) *
        ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
          F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
            (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) q.2.1 q.2.2 h i))
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod volume) := by
  exact aux_leftBumpOneShort_parameterized_prismIntegrand d
    (volume.restrict (Set.Icc (1 : ℝ) 2)) (aux_leftBumpOneShort_scaleK s psi)
    (by
      unfold aux_leftBumpOneShort_scaleK Auto.aux_bf_realRescaled
      fun_prop) F (aux_leftBumpOneShort_scaleK_prism_core_integrable d s hs psi F)

/-- Continuous `A`-to-`Λ₁` for the integral kernel used in the two short estimates. -/
theorem aux_leftBumpOneShort_continuous_aToLambda_integralFct
    (d : ℕ) (s : ℝ) (hs : 0 < s) (psi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    ∫⁻ t in Set.Icc (1 : ℝ) 2,
      ENNReal.ofReal t⁻¹ *
        eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
          (fun i x => f i x)) 2 volume ^ 2 =
      ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (aux_leftBumpOneShort_integralM s psi)
          (fun i x => Auto.aux_aToLambda.transformedFunctions f i x)) := by
  let F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ :=
    Auto.aux_aToLambda.transformedFunctions f
  have hInt := aux_leftBumpOneShort_scaleK_prism_joint_integrable d s hs psi F
  have hPint := aux_leftBumpOneShort_prism_parameter_integrable
    (aux_leftBumpOneShort_scaleK s psi) F hInt
  have hPnonneg : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      0 ≤ prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
        (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact aux_leftBumpOneShort_prism_scaleK_nonnegative d s hs psi t
      (lt_of_lt_of_le zero_lt_one ht.1) F
  have hE : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 : ℝ) 2)),
      ENNReal.ofReal t⁻¹ *
        eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
          (fun i x => f i x)) 2 volume ^ 2 =
        ENNReal.ofReal
          (prismBrascampLiebForm (d + 1) 1 (by omega) (by omega)
            (aux_leftBumpOneShort_scaleK s psi t) (fun i x => F i x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa [F] using aux_leftBumpOneShort_energy_eq_scaleK_prism d s hs psi t
      (lt_of_lt_of_le zero_lt_one ht.1) f
  have hmain := aux_leftBumpOneShort_lintegral_energy_eq_prism_of_setIntegral
    (K := aux_leftBumpOneShort_scaleK s psi)
    (Kint := mToK 1 (by omega) (aux_leftBumpOneShort_integralM s psi)) F
    (fun t => ENNReal.ofReal t⁻¹ *
      eLpNorm (twistedAverageAtScale (s * t) (fun x => psi x)
        (fun i x => f i x)) 2 volume ^ 2)
    (aux_leftBumpOneShort_mToK_integralM_eq_setIntegral s hs psi)
    hInt hPint hPnonneg hE
  simpa [prismForm, F] using hmain


/-! ### First short-variation Whitney normalization -/


theorem aux_leftBumpOneShort_bracket_inv_mul_le (t x : ℝ) (ht : 1 ≤ t) :
    bracketBump (t⁻¹ * x) ≤ t * bracketBump x := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  change (1 + |t⁻¹ * x|)⁻¹ ≤ t * (1 + |x|)⁻¹
  rw [abs_mul, abs_inv, abs_of_pos htpos]
  rw [show (1 + t⁻¹ * |x|)⁻¹ = 1 / (1 + |x| / t) by
    field_simp [ne_of_gt htpos],
    show t * (1 + |x|)⁻¹ = t / (1 + |x|) by field_simp]
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + |x| / t)
    (by positivity : 0 < 1 + |x|)).2
  field_simp [ne_of_gt htpos]
  nlinarith [abs_nonneg x]

theorem aux_leftBumpOneShort_phiFour_rescaled_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (t u : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    |Auto.aux_bf_realRescaled t
        (windowBasedBumpFunctions.phiFour b k) u| ≤
      (2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2 *
        bracketBump (u - t * (2 : ℝ) ^ (-k)) ^ 2 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
  have hkpos : 0 ≤ (2 : ℝ) ^ k := (zpow_pos (by norm_num) _).le
  have hC : 0 ≤ C_thetaPrimitive 2 := by
    norm_num [C_thetaPrimitive, C_uniPair]
  let x : ℝ := u - t * (2 : ℝ) ^ (-k)
  have harg : t⁻¹ * u - (2 : ℝ) ^ (-k) = t⁻¹ * x := by
    dsimp [x]
    field_simp [ne_of_gt htpos]
  have htheta := (thetaPrimitive b 2 (by omega) (by norm_num [N_uniPair])).2.2.1
    (t⁻¹ * x)
  have hbr : bracketBump (t⁻¹ * x) ≤ t * bracketBump x :=
    aux_leftBumpOneShort_bracket_inv_mul_le t x ht.1
  have hbrsq : bracketBump (t⁻¹ * x) ^ 2 ≤ (t * bracketBump x) ^ 2 := by
    exact pow_le_pow_left₀ (by rw [bracketBump]; positivity) hbr 2
  have hB : 0 ≤ bracketBump x ^ 2 := by positivity
  change |t⁻¹ * ((2 : ℝ) ^ k *
      windowBasedBumpFunctions.thetaTilde b (t⁻¹ * u - (2 : ℝ) ^ (-k)))| ≤ _
  rw [harg, abs_mul, abs_mul, abs_of_nonneg htinv,
    abs_of_nonneg hkpos]
  calc
    t⁻¹ * ((2 : ℝ) ^ k * |windowBasedBumpFunctions.thetaTilde b (t⁻¹ * x)|) ≤
        t⁻¹ * ((2 : ℝ) ^ k * (C_thetaPrimitive 2 *
          bracketBump (t⁻¹ * x) ^ 2)) := by
          gcongr
    _ ≤ t⁻¹ * ((2 : ℝ) ^ k * (C_thetaPrimitive 2 *
          (t * bracketBump x) ^ 2)) := by
          gcongr
    _ = (2 : ℝ) ^ k * C_thetaPrimitive 2 * t * bracketBump x ^ 2 := by
          field_simp [ne_of_gt htpos]
    _ ≤ (2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2 * bracketBump x ^ 2 := by
          have htle : t ≤ 2 := ht.2
          have hbase : (2 : ℝ) ^ k * t ≤ (2 : ℝ) ^ k * 2 :=
            mul_le_mul_of_nonneg_left htle hkpos
          have hmain : (2 : ℝ) ^ k * C_thetaPrimitive 2 * t * bracketBump x ^ 2 ≤
              ((2 : ℝ) ^ k * 2) * C_thetaPrimitive 2 * bracketBump x ^ 2 := by
            calc
              (2 : ℝ) ^ k * C_thetaPrimitive 2 * t * bracketBump x ^ 2 =
                  ((2 : ℝ) ^ k * t) * (C_thetaPrimitive 2 * bracketBump x ^ 2) := by
                    ring
              _ ≤ ((2 : ℝ) ^ k * 2) * (C_thetaPrimitive 2 * bracketBump x ^ 2) :=
                mul_le_mul_of_nonneg_right hbase (mul_nonneg hC hB)
              _ = ((2 : ℝ) ^ k * 2) * C_thetaPrimitive 2 * bracketBump x ^ 2 := by
                ring
          calc
            (2 : ℝ) ^ k * C_thetaPrimitive 2 * t * bracketBump x ^ 2 ≤
                ((2 : ℝ) ^ k * 2) * C_thetaPrimitive 2 * bracketBump x ^ 2 := hmain
            _ = (2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2 * bracketBump x ^ 2 := by
                rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
                norm_num
    _ = (2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2 *
        bracketBump (u - t * (2 : ℝ) ^ (-k)) ^ 2 := by rfl

theorem aux_leftBumpOneShort_scalar_identity (k : ℤ) (C : ℝ) :
    Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
      (((2 : ℝ) ^ (k + 1) * C) ^ 2) =
      4 * C ^ 2 * Real.rpow 2 ((k : ℝ) / 2) := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  rw [mul_pow]
  rw [show (2 : ℝ) ^ (k + 1) = Real.rpow 2 ((k + 1 : ℤ) : ℝ) by
    exact (Real.rpow_intCast 2 (k + 1)).symm]
  have hpow : (Real.rpow 2 ((k + 1 : ℤ) : ℝ)) ^ 2 =
      Real.rpow 2 (((k + 1 : ℤ) : ℝ) * 2) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul htwo.le _ _).symm
  rw [hpow]
  calc
    Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
        (Real.rpow 2 (((k + 1 : ℤ) : ℝ) * 2) * C ^ 2) =
        (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
          Real.rpow 2 (((k + 1 : ℤ) : ℝ) * 2)) * C ^ 2 := by ring
    _ = Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2 +
          ((k + 1 : ℤ) : ℝ) * 2) * C ^ 2 := by
      congr 1
      exact (Real.rpow_add htwo _ _).symm
    _ = Real.rpow 2 (2 + (k : ℝ) / 2) * C ^ 2 := by
      congr 2
      push_cast
      ring
    _ = (Real.rpow 2 (2 : ℝ) * Real.rpow 2 ((k : ℝ) / 2)) * C ^ 2 := by
      congr 1
      exact Real.rpow_add htwo _ _
    _ = 4 * C ^ 2 * Real.rpow 2 ((k : ℝ) / 2) := by
      norm_num
      ring

theorem aux_leftBumpOneShort_scaledBracket_one_eq_rpow (x : ℝ) :
    scaledBracketBumpReal (3 / 2 : ℝ) 1 x =
      Real.rpow (bracketBump x) (3 / 2 : ℝ) := by
  unfold scaledBracketBumpReal bracketBump
  norm_num only [inv_one, one_mul]
  calc
    Real.rpow (1 + |x|) (-(3 / 2 : ℝ)) =
        (Real.rpow (1 + |x|) (3 / 2 : ℝ))⁻¹ :=
      Real.rpow_neg (by positivity) _
    _ = Real.rpow ((1 + |x|)⁻¹) (3 / 2 : ℝ) :=
      (Real.inv_rpow (by positivity) _).symm

theorem aux_leftBumpOneShort_bracket_le_div_sqrt_two (x : ℝ) :
    bracketBump x ≤ bracketBump (x / Real.sqrt 2) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
  have hsqrt : 1 ≤ Real.sqrt 2 := by nlinarith
  have hsqrt_pos : 0 < Real.sqrt 2 := lt_of_lt_of_le zero_lt_one hsqrt
  unfold bracketBump
  rw [abs_div, abs_of_pos hsqrt_pos]
  apply (inv_le_inv₀ (by positivity : 0 < 1 + |x|)
    (by positivity : 0 < 1 + |x| / Real.sqrt 2)).mpr
  have hdiv : |x| / Real.sqrt 2 ≤ |x| := by
    apply (div_le_iff₀ hsqrt_pos).2
    nlinarith [abs_nonneg x]
  nlinarith

theorem aux_leftBumpOneShort_offcenter_second_term_le_whitney
    (v : RealPlane) :
    Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) *
      Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ) ≤
      scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W (1 : Fin 2) v).1) *
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W (1 : Fin 2) v).2) := by
  have h0 : Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) ≤
      Real.rpow (bracketBump ((v.1 + v.2) / Real.sqrt 2)) (3 / 2 : ℝ) := by
    exact Real.rpow_le_rpow (by rw [bracketBump]; positivity)
      (aux_leftBumpOneShort_bracket_le_div_sqrt_two (v.1 + v.2)) (by norm_num)
  have h1base : Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ) ≤
      Real.rpow (bracketBump ((v.1 - v.2) / Real.sqrt 2)) (3 / 2 : ℝ) := by
    exact Real.rpow_le_rpow (by rw [bracketBump]; positivity)
      (aux_leftBumpOneShort_bracket_le_div_sqrt_two (v.1 - v.2)) (by norm_num)
  have hneg : bracketBump ((v.1 - v.2) / Real.sqrt 2) =
      bracketBump ((-v.1 + v.2) / Real.sqrt 2) := by
    rw [show (-v.1 + v.2) / Real.sqrt 2 =
        -((v.1 - v.2) / Real.sqrt 2) by ring]
    unfold bracketBump
    rw [abs_neg]
  have h1 : Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ) ≤
      Real.rpow (bracketBump ((-v.1 + v.2) / Real.sqrt 2)) (3 / 2 : ℝ) := by
    rw [← hneg]
    exact h1base
  have h0nonneg : 0 ≤ Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by rw [bracketBump]; positivity) _
  have h1nonneg : 0 ≤ Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by rw [bracketBump]; positivity) _
  rw [W, if_neg (by decide : (1 : Fin 2) ≠ 0),
    aux_leftBumpOneShort_scaledBracket_one_eq_rpow,
    aux_leftBumpOneShort_scaledBracket_one_eq_rpow]
  exact mul_le_mul h0 h1 h1nonneg
    (Real.rpow_nonneg (by rw [bracketBump]; positivity) _)

theorem aux_leftBumpOneShort_offcenter_rhs_le_whitney (v : RealPlane) :
    C_thetaTOffcenter *
      (Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
          Real.rpow (bracketBump v.2) (3 / 2 : ℝ) +
        Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) *
          Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ)) ≤
      C_thetaTOffcenter * ∑ u : Fin 2,
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
  have hfirst : Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
      Real.rpow (bracketBump v.2) (3 / 2 : ℝ) =
      scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W (0 : Fin 2) v).1) *
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W (0 : Fin 2) v).2) := by
    rw [W, if_pos rfl, aux_leftBumpOneShort_scaledBracket_one_eq_rpow,
      aux_leftBumpOneShort_scaledBracket_one_eq_rpow]
  rw [Fin.sum_univ_two, ← hfirst]
  exact mul_le_mul_of_nonneg_left
    (by
      simpa [add_comm] using add_le_add_right
        (aux_leftBumpOneShort_offcenter_second_term_le_whitney v)
        (Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
          Real.rpow (bracketBump v.2) (3 / 2 : ℝ)))
    (by norm_num [C_thetaTOffcenter])

theorem aux_leftBumpOneShort_integrand_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) (v : RealPlane) :
    |Auto.aux_bf_realRescaled t
        (windowBasedBumpFunctions.phiFour b k) v.1 *
      Auto.aux_bf_realRescaled t
        (windowBasedBumpFunctions.phiFour b k) v.2 * t⁻¹| ≤
      ((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) ^ 2 *
        (bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 *
          bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
  have htinvle : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).2 ht.1
  have h0 := aux_leftBumpOneShort_phiFour_rescaled_bound b k t v.1 ht
  have h1 := aux_leftBumpOneShort_phiFour_rescaled_bound b k t v.2 ht
  have hA : 0 ≤ (2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2 :=
    mul_nonneg (zpow_pos (by norm_num) _).le
      (by norm_num [C_thetaPrimitive, C_uniPair])
  have hB0 : 0 ≤ bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 := by positivity
  have hB1 : 0 ≤ bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2 := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg htinv]
  calc
    |Auto.aux_bf_realRescaled t
          (windowBasedBumpFunctions.phiFour b k) v.1| *
        |Auto.aux_bf_realRescaled t
          (windowBasedBumpFunctions.phiFour b k) v.2| * t⁻¹ ≤
        (((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) *
          bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2) *
          (((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) *
            bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) * t⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ htinv
          exact mul_le_mul h0 h1 (abs_nonneg _)
            (mul_nonneg hA hB0)
    _ ≤ (((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) *
          bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2) *
          (((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) *
            bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) * 1 := by
          apply mul_le_mul_of_nonneg_left htinvle
          positivity
    _ = ((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) ^ 2 *
        (bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 *
          bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) := by ring

theorem aux_leftBumpOneShort_kernel_decay
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1) (v : RealPlane) :
    |Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
      integralFctKernel (windowBasedBumpFunctions.phiFour b k)
        (WithLp.toLp 2 ![v.1, v.2])| ≤
      (4 * C_thetaPrimitive 2 ^ 2 * C_thetaTOffcenter) *
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
  let A : ℝ := (2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2
  let B : ℝ → ℝ := fun t =>
    bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 *
      bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2
  have hBcont : Continuous B := by
    dsimp [B]
    have h0 : Continuous (fun t : ℝ =>
        1 + |v.1 - t * (2 : ℝ) ^ (-k)|) := by fun_prop
    have h1 : Continuous (fun t : ℝ =>
        1 + |v.2 - t * (2 : ℝ) ^ (-k)|) := by fun_prop
    have h0ne : ∀ t : ℝ, 1 + |v.1 - t * (2 : ℝ) ^ (-k)| ≠ 0 := by
      intro t
      positivity
    have h1ne : ∀ t : ℝ, 1 + |v.2 - t * (2 : ℝ) ^ (-k)| ≠ 0 := by
      intro t
      positivity
    change Continuous (fun t : ℝ =>
      (1 + |v.1 - t * (2 : ℝ) ^ (-k)|)⁻¹ ^ 2 *
        (1 + |v.2 - t * (2 : ℝ) ^ (-k)|)⁻¹ ^ 2)
    exact ((h0.inv₀ h0ne).pow 2).mul ((h1.inv₀ h1ne).pow 2)
  have hBint : IntegrableOn B (Set.Icc (1 : ℝ) 2) := hBcont.integrableOn_Icc
  have hint : ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
      |Auto.aux_bf_realRescaled t
          (windowBasedBumpFunctions.phiFour b k) v.1 *
        Auto.aux_bf_realRescaled t
          (windowBasedBumpFunctions.phiFour b k) v.2 * t⁻¹| ≤
      A ^ 2 * ∫ t : ℝ in Set.Icc (1 : ℝ) 2, B t := by
    calc
      ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
          |Auto.aux_bf_realRescaled t
              (windowBasedBumpFunctions.phiFour b k) v.1 *
            Auto.aux_bf_realRescaled t
              (windowBasedBumpFunctions.phiFour b k) v.2 * t⁻¹| ≤
          ∫ t : ℝ in Set.Icc (1 : ℝ) 2, A ^ 2 * B t := by
            apply MeasureTheory.setIntegral_mono_of_nonneg
            · intro t ht
              exact abs_nonneg _
            · intro t ht
              simpa only [A, B] using
                aux_leftBumpOneShort_integrand_bound b k t ht v
            · exact hBint.const_mul _
      _ = A ^ 2 * ∫ t : ℝ in Set.Icc (1 : ℝ) 2, B t := by
        rw [integral_const_mul]
  have hc : 0 ≤ Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hoff := thetaTOffcenter k hk v.1 v.2
  change |Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
      ∫ t : ℝ in Set.Icc 1 2,
        Auto.aux_bf_realRescaled t
          (windowBasedBumpFunctions.phiFour b k) v.1 *
        Auto.aux_bf_realRescaled t
          (windowBasedBumpFunctions.phiFour b k) v.2 * t⁻¹| ≤ _
  calc
    |Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
        ∫ t : ℝ in Set.Icc 1 2,
          Auto.aux_bf_realRescaled t
            (windowBasedBumpFunctions.phiFour b k) v.1 *
          Auto.aux_bf_realRescaled t
            (windowBasedBumpFunctions.phiFour b k) v.2 * t⁻¹| =
        Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
          |∫ t : ℝ in Set.Icc 1 2,
            Auto.aux_bf_realRescaled t
              (windowBasedBumpFunctions.phiFour b k) v.1 *
            Auto.aux_bf_realRescaled t
              (windowBasedBumpFunctions.phiFour b k) v.2 * t⁻¹| := by
              rw [abs_mul, abs_of_nonneg hc]
    _ ≤ Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
        ∫ t : ℝ in Set.Icc 1 2,
          |Auto.aux_bf_realRescaled t
              (windowBasedBumpFunctions.phiFour b k) v.1 *
            Auto.aux_bf_realRescaled t
              (windowBasedBumpFunctions.phiFour b k) v.2 * t⁻¹| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hc
    _ ≤ Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
        (A ^ 2 * ∫ t : ℝ in Set.Icc 1 2, B t) :=
      mul_le_mul_of_nonneg_left hint hc
    _ = 4 * C_thetaPrimitive 2 ^ 2 *
        (Real.rpow 2 ((k : ℝ) / 2) *
          ∫ t : ℝ in Set.Icc 1 2, B t) := by
          dsimp [A]
          calc
            Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
                (((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) ^ 2 *
                  ∫ t : ℝ in Set.Icc 1 2, B t) =
                (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
                  ((2 : ℝ) ^ (k + 1) * C_thetaPrimitive 2) ^ 2) *
                    ∫ t : ℝ in Set.Icc 1 2, B t := by ring
            _ = (4 * C_thetaPrimitive 2 ^ 2 * Real.rpow 2 ((k : ℝ) / 2)) *
                    ∫ t : ℝ in Set.Icc 1 2, B t := by
                  rw [aux_leftBumpOneShort_scalar_identity]
            _ = 4 * C_thetaPrimitive 2 ^ 2 *
                (Real.rpow 2 ((k : ℝ) / 2) *
                  ∫ t : ℝ in Set.Icc 1 2, B t) := by ring
    _ ≤ 4 * C_thetaPrimitive 2 ^ 2 *
        (C_thetaTOffcenter *
          (Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
              Real.rpow (bracketBump v.2) (3 / 2 : ℝ) +
            Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) *
              Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [B] using hoff
          · positivity
    _ ≤ 4 * C_thetaPrimitive 2 ^ 2 *
        (C_thetaTOffcenter * ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2)) := by
          apply mul_le_mul_of_nonneg_left
          · exact aux_leftBumpOneShort_offcenter_rhs_le_whitney v
          positivity
    _ = (4 * C_thetaPrimitive 2 ^ 2 * C_thetaTOffcenter) *
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by ring

noncomputable def aux_leftBumpOneShort_whitneyNormalizer : ℝ :=
  4 * C_thetaPrimitive 2 ^ 2 * C_thetaTOffcenter

theorem aux_leftBumpOneShort_whitneyNormalizer_pos :
    0 < aux_leftBumpOneShort_whitneyNormalizer := by
  norm_num [aux_leftBumpOneShort_whitneyNormalizer, C_thetaPrimitive, C_uniPair,
    C_thetaTOffcenter]

theorem aux_leftBumpOneShort_normalized_decay
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1) (v : RealPlane) :
    |(aux_leftBumpOneShort_whitneyNormalizer)⁻¹ *
      Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
      integralFctKernel (windowBasedBumpFunctions.phiFour b k)
        (WithLp.toLp 2 ![v.1, v.2])| ≤
      ∑ u : Fin 2,
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
  let D : ℝ := aux_leftBumpOneShort_whitneyNormalizer
  let S : ℝ := ∑ u : Fin 2,
    scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
      scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2)
  have hD : 0 < D := aux_leftBumpOneShort_whitneyNormalizer_pos
  have hraw : |Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
      integralFctKernel (windowBasedBumpFunctions.phiFour b k)
        (WithLp.toLp 2 ![v.1, v.2])| ≤ D * S := by
    dsimp [D, S, aux_leftBumpOneShort_whitneyNormalizer]
    exact aux_leftBumpOneShort_kernel_decay b k hk v
  change |D⁻¹ * Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
      integralFctKernel (windowBasedBumpFunctions.phiFour b k)
        (WithLp.toLp 2 ![v.1, v.2])| ≤ S
  calc
    |D⁻¹ * Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
        integralFctKernel (windowBasedBumpFunctions.phiFour b k)
          (WithLp.toLp 2 ![v.1, v.2])| =
        |D⁻¹ * (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
          integralFctKernel (windowBasedBumpFunctions.phiFour b k)
            (WithLp.toLp 2 ![v.1, v.2]))| := by
      rw [mul_assoc]
    _ = D⁻¹ * |Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
          integralFctKernel (windowBasedBumpFunctions.phiFour b k)
            (WithLp.toLp 2 ![v.1, v.2])| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hD)]
    _ ≤ D⁻¹ * (D * S) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hD.le)
    _ = S := by field_simp [ne_of_gt hD]

theorem aux_leftBumpOneShort_planeFourier_const_mul
    (c : ℝ) (M : RealPlane → ℝ) (xi : EuclideanSpace ℝ (Fin 2)) :
    aux_planeFourier (fun v => c * M v) xi = c * aux_planeFourier M xi := by
  unfold aux_planeFourier
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  push_cast
  rw [Circle.smul_def, Circle.smul_def]
  ring

theorem aux_leftBumpOneShort_planeFourier_normalize_diagonal
    (D : ℝ) (hD : 0 < D) (M : RealPlane → ℝ)
    (m : ℕ) (xi : ℝ)
    (hraw : ‖iteratedDeriv m
      (fun z : ℝ => aux_planeFourier M (WithLp.toLp 2 ![z, -z])) xi‖ ≤ D) :
    ‖iteratedDeriv m
      (fun z : ℝ => aux_planeFourier (fun v => D⁻¹ * M v)
        (WithLp.toLp 2 ![z, -z])) xi‖ ≤ 1 := by
  have hformula :
      (fun z : ℝ => aux_planeFourier (fun v => D⁻¹ * M v)
        (WithLp.toLp 2 ![z, -z])) =
      fun z => (D⁻¹ : ℂ) * aux_planeFourier M (WithLp.toLp 2 ![z, -z]) := by
    funext z
    rw [aux_leftBumpOneShort_planeFourier_const_mul]
    norm_cast
  rw [hformula, iteratedDeriv_const_mul_field, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  calc
    D⁻¹ * ‖iteratedDeriv m
        (fun z : ℝ => aux_planeFourier M (WithLp.toLp 2 ![z, -z])) xi‖ ≤
        D⁻¹ * D :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hD.le)
    _ = 1 := by field_simp [ne_of_gt hD]

theorem aux_leftBumpOneShort_integralFctKernel_plane_diagonal_fourier_eq
    (psi : SchwartzMap ℝ ℝ) (z : ℝ) :
    aux_planeFourier
      (fun v : RealPlane => integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2]))
      (WithLp.toLp 2 ![z, -z]) =
      ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
        FourierTransform.fourier (fun x : ℝ => (psi x : ℂ)) (t * z) *
          FourierTransform.fourier (fun x : ℝ => (psi x : ℂ)) (-(t * z)) *
            ((t⁻¹ : ℝ) : ℂ) := by
  have hcoord : (fun u : EuclideanSpace ℝ (Fin 2) =>
      (integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![u 0, u 1]) : ℂ)) =
      fun u => (integralFctKernel (fun x : ℝ => psi x) u : ℂ) := by
    funext u
    congr 1
  rw [aux_planeFourier, hcoord, integralFctKernel_fourier_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  funext t
  congr 3
  ring_nf

theorem aux_leftBumpOneShort_integralFct_plane_fourier_support
    (psi : SchwartzMap ℝ ℝ)
    (hband : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
        Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1) :
    Function.support (aux_planeFourier
      (fun v : RealPlane => integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2]))) ⊆
      {v : EuclideanSpace ℝ (Fin 2) |
        v 0 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3) ∧
        v 1 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3)} := by
  have hbase := integralFct psi hband 0
  have hcoord : (fun u : EuclideanSpace ℝ (Fin 2) =>
      (integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![u 0, u 1]) : ℂ)) =
        fun u => (integralFctKernel (fun x : ℝ => psi x) u : ℂ) := by
    funext u
    congr 1
  intro z hz
  have hz' : z ∈ Function.support (FourierTransform.fourier
      (fun u : EuclideanSpace ℝ (Fin 2) =>
        (aux_integralFctKernelAtScale ((2 : ℝ) ^ (0 : ℤ))
          (fun x : ℝ => psi x) u : ℂ))) := by
    simpa [aux_planeFourier, hcoord, aux_integralFctKernelAtScale,
      Auto.rescaled] using hz
  exact hbase.2.2.2 (hbase.2.2.1 hz')

theorem aux_leftBumpOneShort_integralFct_plane_fourier_support_smul
    (psi : SchwartzMap ℝ ℝ)
    (hband : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
        Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1)
    (c : ℝ) :
    Function.support (aux_planeFourier
      (fun v : RealPlane => c * integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2]))) ⊆
      {v : EuclideanSpace ℝ (Fin 2) |
        v 0 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3) ∧
        v 1 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3)} := by
  intro z hz
  have hne := Function.mem_support.mp hz
  rw [aux_leftBumpOneShort_planeFourier_const_mul] at hne
  have hbase : aux_planeFourier
      (fun v : RealPlane => integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2])) z ≠ 0 := by
    intro hzero
    simp [hzero] at hne
  exact aux_leftBumpOneShort_integralFct_plane_fourier_support psi hband
    (Function.mem_support.mpr hbase)

theorem aux_leftBumpOneShort_phiFourSchwartz_support
    (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ => (phiFourSchwartz b k x : ℂ))) ⊆
        Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
  intro xi hxi
  have hraw : xi ∈ Function.support (FourierTransform.fourier
      (fun x : ℝ => (windowBasedBumpFunctions.phiFour b k x : ℂ))) := by
    simpa only [phiFourSchwartz_apply] using hxi
  exact (thetaPrimitive b 2 (by omega) (by norm_num [N_uniPair])).1.2
    ((phiFourSupport b k).1 hraw)

theorem aux_leftBumpOneShort_integralFct_base_symmetric
    (psi : SchwartzMap ℝ ℝ)
    (hband : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
        Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1)
    (v : RealPlane) :
    integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![v.1, v.2]) =
      integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![v.2, v.1]) := by
  have hsym := (integralFct psi hband 0).1
  simpa [aux_integralFctKernelAtScale, Auto.rescaled,
    aux_swapTwo] using hsym (WithLp.toLp 2 ![v.1, v.2])

theorem aux_leftBumpOneShort_integralFct_base_positive
    (psi : SchwartzMap ℝ ℝ)
    (hband : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
        Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1)
    (g : ℝ → ℝ) (hg : Auto.aux_bounded g) :
    0 ≤ ∫ u : EuclideanSpace ℝ (Fin 2),
      g (u 0) * g (u 1) * integralFctKernel (fun x : ℝ => psi x) u := by
  have hpos := (integralFct psi hband 0).2.1 g hg
  simpa [aux_integralFctKernelAtScale, Auto.rescaled] using hpos

noncomputable def aux_leftBumpOneShort_integralFctWhitneyData
    (psi : SchwartzMap ℝ ℝ)
    (hann : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
        Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2))
    (hband : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
        Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1)
    (c : ℝ) (hc : 0 ≤ c)
    (hnonzero : (fun v : RealPlane =>
      c * integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![v.1, v.2])) ≠ 0)
    (hfourier : Function.support (aux_planeFourier
      (fun v : RealPlane =>
        c * integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![v.1, v.2]))) ⊆
        {v : EuclideanSpace ℝ (Fin 2) |
          v 0 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3) ∧
          v 1 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3)})
    (hdiag : ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m
        (fun z : ℝ => aux_planeFourier
          (fun v : RealPlane =>
            c * integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![v.1, v.2]))
          (WithLp.toLp 2 ![z, -z])) xi‖ ≤ 1)
    (hdecay : ∀ v : RealPlane,
      |c * integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![v.1, v.2])| ≤
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2)) :
    WhitneyKernelData where
  kernel := fun v => c * integralFctKernel (fun x : ℝ => psi x)
    (WithLp.toLp 2 ![v.1, v.2])
  kernel_schwartz := c • integralFctKernelSchwartz psi hann
  kernel_schwartz_eq := by
    intro u
    rw [smul_apply, integralFctKernelSchwartz_apply]
    simp only [smul_eq_mul]
    congr 2
    ext i
    fin_cases i <;> rfl
  kernel_memW0 := by
    let e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] RealPlane :=
      (EuclideanSpace.equiv (Fin 2) ℝ).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    have hK : MemW0 (c • integralFctKernelSchwartz psi hann) := SchwartzMap.memW0 _
    have hraw := aux_memW0_comp_continuousLinearEquiv hK e.symm
    convert hraw using 1
    funext v
    simp only [Function.comp_apply]
    rw [smul_apply, integralFctKernelSchwartz_apply]
    simp only [smul_eq_mul]
    change c * integralFctKernel (fun x : ℝ => psi x)
      (WithLp.toLp 2 ![v.1, v.2]) = _
    congr 2
  kernel_nonzero := hnonzero
  symmetric := by
    intro v
    dsimp
    rw [aux_leftBumpOneShort_integralFct_base_symmetric psi hband]
  positive := by
    intro g hg
    let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ RealPlane :=
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
    have he : MeasurePreserving e volume volume :=
      (PiLp.volume_preserving_toLp (Fin 2)).symm.trans
        (MeasureTheory.volume_preserving_finTwoArrow ℝ)
    let G : RealPlane → ℝ := fun v =>
      g v.1 * g v.2 * integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2])
    have hG : (fun u : EuclideanSpace ℝ (Fin 2) =>
        g (u 0) * g (u 1) * integralFctKernel (fun x : ℝ => psi x) u) = G ∘ e := by
      funext u
      have hu : WithLp.toLp 2 ![u 0, u 1] = u := by
        ext i
        fin_cases i <;> rfl
      dsimp [G, e]
      simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.toLp_symm_apply,
        MeasurableEquiv.finTwoArrow_apply]
      change g (u 0) * g (u 1) * integralFctKernel (fun x : ℝ => psi x) u =
        g (u 0) * g (u 1) * integralFctKernel (fun x : ℝ => psi x)
          (WithLp.toLp 2 ![u 0, u 1])
      rw [hu]
    have hbase := aux_leftBumpOneShort_integralFct_base_positive psi hband g hg
    have hplane : 0 ≤ ∫ v : RealPlane, G v := by
      rw [hG] at hbase
      exact (he.integral_comp' G) ▸ hbase
    rw [show (fun v : RealPlane =>
        g v.1 * g v.2 *
          (c * integralFctKernel (fun x : ℝ => psi x) (WithLp.toLp 2 ![v.1, v.2]))) =
        fun v => c * G v by
          funext v
          simp [G]
          ring, integral_const_mul]
    exact mul_nonneg hc hplane
  fourier_support := hfourier
  diagonal_derivative := hdiag
  decay := hdecay

noncomputable def aux_leftBumpOneShort_whitneyData
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (hnonzero : (fun v : RealPlane =>
      (aux_leftBumpOneShort_whitneyNormalizer)⁻¹ *
        Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
        integralFctKernel (windowBasedBumpFunctions.phiFour b k)
          (WithLp.toLp 2 ![v.1, v.2])) ≠ 0)
    (hdiag : ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m
        (fun z : ℝ => aux_planeFourier
          (fun v : RealPlane =>
            (aux_leftBumpOneShort_whitneyNormalizer)⁻¹ *
              Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
              integralFctKernel (fun x : ℝ => phiFourSchwartz b k x)
                (WithLp.toLp 2 ![v.1, v.2]))
          (WithLp.toLp 2 ![z, -z])) xi‖ ≤ 1) :
    WhitneyKernelData := by
  let psi : SchwartzMap ℝ ℝ := phiFourSchwartz b k
  let c : ℝ := (aux_leftBumpOneShort_whitneyNormalizer)⁻¹ *
    Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)
  have hann : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
    dsimp [psi]
    exact aux_leftBumpOneShort_phiFourSchwartz_support b k
  have hband : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
        Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1 := by
    intro xi hxi
    have hraw : xi ∈ Function.support (FourierTransform.fourier
        (fun x : ℝ => (windowBasedBumpFunctions.phiFour b k x : ℂ))) := by
      simpa only [psi, phiFourSchwartz_apply] using hxi
    simpa [aux_frequencyAnnulus] using (phiFourSupport b k).1 hraw
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (inv_nonneg.mpr aux_leftBumpOneShort_whitneyNormalizer_pos.le)
      (Real.rpow_nonneg (by norm_num) _)
  have hfourier : Function.support (aux_planeFourier
      (fun v : RealPlane => c * integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2]))) ⊆
      {v : EuclideanSpace ℝ (Fin 2) |
        v 0 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3) ∧
        v 1 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3)} :=
    aux_leftBumpOneShort_integralFct_plane_fourier_support_smul psi hband c
  have hdecay : ∀ v : RealPlane,
      |c * integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2])| ≤
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
    intro v
    simpa only [c, psi, phiFourSchwartz_apply] using
      aux_leftBumpOneShort_normalized_decay b k hk v
  apply aux_leftBumpOneShort_integralFctWhitneyData psi hann hband c hc
  · simpa only [c, psi, phiFourSchwartz_apply] using hnonzero
  · exact hfourier
  · simpa only [c, psi] using hdiag
  · exact hdecay

theorem aux_leftBumpOneShort_pair_contDiff
    (q : ℝ → ℂ) (hq : ContDiff ℝ 2 q) :
    ContDiff ℝ 2 (fun z : ℝ => q z * q (-z)) := by
  exact hq.mul (hq.comp (by fun_prop))

theorem aux_leftBumpOneShort_pair_deriv_bound
    (q : ℝ → ℂ) (hq : ContDiff ℝ 2 q)
    (C : ℝ) (hC : 0 ≤ C)
    (hqbound : ∀ m : ℕ, m ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv m q x‖ ≤ C) :
    ∀ m : ℕ, m ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv m (fun z : ℝ => q z * q (-z)) x‖ ≤ (2 : ℝ) ^ m * C ^ 2 := by
  intro m hm x
  have hneg : ContDiffAt ℝ (m : ℕ∞) (fun z : ℝ => q (-z)) x := by
    apply ((hq.comp (by fun_prop)).of_le (m := (m : WithTop ℕ∞)) ?_).contDiffAt
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast hm
  have hpos : ContDiffAt ℝ (m : ℕ∞) q x := by
    apply (hq.of_le (m := (m : WithTop ℕ∞)) ?_).contDiffAt
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast hm
  change ‖iteratedDeriv m (q * fun z : ℝ => q (-z)) x‖ ≤ _
  rw [iteratedDeriv_mul hpos hneg]
  calc
    ‖∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i q x *
          iteratedDeriv (m - i) (fun z : ℝ => q (-z)) x‖ ≤
        ∑ i ∈ Finset.range (m + 1),
          ‖(m.choose i : ℂ) * iteratedDeriv i q x *
            iteratedDeriv (m - i) (fun z : ℝ => q (-z)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (C * C) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hmi : m - i ≤ m := Nat.sub_le _ _
      have hq_i := hqbound i (le_trans him hm) x
      have hq_neg : ‖iteratedDeriv (m - i) (fun z : ℝ => q (-z)) x‖ ≤ C := by
        have hqmi : ContDiff ℝ ((m - i : ℕ) : WithTop ℕ∞) q := by
          apply hq.of_le
          apply WithTop.coe_le_coe.mpr
          exact_mod_cast (le_trans hmi hm)
        rw [show iteratedDeriv (m - i) (fun z : ℝ => q (-z)) x =
            ((-1 : ℝ) ^ (m - i)) • iteratedDeriv (m - i) q ((-1 : ℝ) * x) by
              convert congrFun (iteratedDeriv_comp_const_smul hqmi (-1 : ℝ)) x using 1;
                ring_nf]
        rw [norm_smul, Real.norm_eq_abs]
        have hsign : |(-1 : ℝ) ^ (m - i)| = 1 := by
          rw [abs_pow]
          norm_num
        rw [hsign, one_mul]
        exact hqbound (m - i) (le_trans hmi hm) _
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hchoose : 0 ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
      calc
        ↑(m.choose i) * ‖iteratedDeriv i q x‖ *
            ‖iteratedDeriv (m - i) (fun z => q (-z)) x‖ ≤
            ↑(m.choose i) * C * C := by
              gcongr
        _ = (m.choose i : ℝ) * (C * C) := by ring
    _ ≤ (2 : ℝ) ^ m * C ^ 2 := by
      interval_cases m <;> norm_num [Finset.sum_range_succ, Nat.choose] <;>
        ring_nf <;> exact le_rfl

theorem aux_leftBumpOneShort_integral_comp_inv_hasDeriv
    (H : ℝ → ℂ) (hH : ContDiff ℝ 2 H) (C : ℝ)
    (hHbound : ∀ y : ℝ, ‖deriv H y‖ ≤ C) (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => ∫ t : ℝ in Icc (1 : ℝ) 2,
        H (t * z) * ((t⁻¹ : ℝ) : ℂ))
      (∫ t : ℝ in Icc (1 : ℝ) 2, deriv H (t * x)) x := by
  let μ : Measure ℝ := volume.restrict (Icc (1 : ℝ) 2)
  let F : ℝ → ℝ → ℂ := fun z t => H (t * z) * ((t⁻¹ : ℝ) : ℂ)
  let F' : ℝ → ℝ → ℂ := fun z t => deriv H (t * z)
  have hHcont : Continuous H := hH.continuous
  have hderiv_cont : Continuous (deriv H) := by
    rw [← iteratedDeriv_one]
    exact hH.continuous_iteratedDeriv 1 (by norm_num)
  have hHdiff : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hFmeas : ∀ᶠ z in nhds x, AEStronglyMeasurable (F z) μ := by
    filter_upwards [] with z
    dsimp [F, μ]
    fun_prop
  have hFint : Integrable (F x) μ := by
    dsimp [F, μ]
    apply ContinuousOn.integrableOn_Icc
    apply (hHcont.comp_continuousOn (by fun_prop)).mul
    apply Complex.ofRealCLM.continuous.comp_continuousOn
    apply continuousOn_inv₀.mono
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  have hFprimeMeas : AEStronglyMeasurable (F' x) μ := by
    dsimp [F', μ]
    fun_prop
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball x 1, ‖F' z t‖ ≤ C := by
    filter_upwards [] with t z hz
    dsimp [F']
    exact hHbound _
  have hCint : Integrable (fun _ : ℝ => C) μ := by
    dsimp [μ]
    exact integrableOn_const (isCompact_Icc.measure_lt_top.ne)
  have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w : ℝ => F w t) (F' z t) z := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht z hz
    dsimp [F, F']
    have hbase : HasDerivAt H (deriv H (t * z)) (t * z) :=
      (hHdiff (t * z)).hasDerivAt
    have htne : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    have hchain := HasDerivAt.const_smul (t⁻¹ : ℝ)
      (HasDerivAt.scomp z hbase (hasDerivAt_const_mul t))
    have hcancel : (t⁻¹ : ℝ) • (t • deriv H (t * z)) = deriv H (t * z) := by
      rw [← mul_smul, inv_mul_cancel₀ htne, one_smul]
    rw [hcancel] at hchain
    have hfun : (t⁻¹ : ℝ) • (H ∘ fun w : ℝ => t * w) =
        fun w : ℝ => H (t * w) * ((t⁻¹ : ℝ) : ℂ) := by
      funext w
      change ((t⁻¹ : ℝ) : ℂ) * H (t * w) = _
      ring
    rw [hfun] at hchain
    exact hchain
  obtain ⟨_, hmain⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ : ℝ => C) (F := F) (F' := F')
    (Metric.ball_mem_nhds x zero_lt_one) hFmeas hFint hFprimeMeas hbound hCint hdiff
  simpa [μ, F, F'] using hmain

theorem aux_leftBumpOneShort_integral_comp_hasDeriv
    (H : ℝ → ℂ) (hH : ContDiff ℝ 1 H) (C : ℝ) (hC : 0 ≤ C)
    (hHbound : ∀ y : ℝ, ‖deriv H y‖ ≤ C) (x : ℝ) :
    HasDerivAt
      (fun z : ℝ => ∫ t : ℝ in Icc (1 : ℝ) 2, H (t * z))
      (∫ t : ℝ in Icc (1 : ℝ) 2, (t : ℝ) • deriv H (t * x)) x := by
  let μ : Measure ℝ := volume.restrict (Icc (1 : ℝ) 2)
  let F : ℝ → ℝ → ℂ := fun z t => H (t * z)
  let F' : ℝ → ℝ → ℂ := fun z t => (t : ℝ) • deriv H (t * z)
  have hHcont : Continuous H := hH.continuous
  have hderiv_cont : Continuous (deriv H) := by
    rw [← iteratedDeriv_one]
    exact hH.continuous_iteratedDeriv 1 (by norm_num)
  have hHdiff : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hFmeas : ∀ᶠ z in nhds x, AEStronglyMeasurable (F z) μ := by
    filter_upwards [] with z
    dsimp [F, μ]
    fun_prop
  have hFint : Integrable (F x) μ := by
    dsimp [F, μ]
    exact (hHcont.comp_continuousOn (by fun_prop)).integrableOn_Icc
  have hFprimeMeas : AEStronglyMeasurable (F' x) μ := by
    dsimp [F', μ]
    fun_prop
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball x 1, ‖F' z t‖ ≤ 2 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht z hz
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_lt_one.le ht.1)]
    calc
      t * ‖deriv H (t * z)‖ ≤ t * C :=
        mul_le_mul_of_nonneg_left (hHbound _) (le_trans zero_lt_one.le ht.1)
      _ ≤ 2 * C := mul_le_mul_of_nonneg_right ht.2 hC
  have hCint : Integrable (fun _ : ℝ => 2 * C) μ := by
    dsimp [μ]
    exact integrableOn_const (isCompact_Icc.measure_lt_top.ne)
  have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball x 1,
      HasDerivAt (fun w : ℝ => F w t) (F' z t) z := by
    filter_upwards [] with t z hz
    dsimp [F, F']
    have hbase : HasDerivAt H (deriv H (t * z)) (t * z) :=
      (hHdiff (t * z)).hasDerivAt
    simpa [Function.comp_def] using
      (HasDerivAt.scomp z hbase (hasDerivAt_const_mul t))
  obtain ⟨_, hmain⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ : ℝ => 2 * C) (F := F) (F' := F')
    (Metric.ball_mem_nhds x zero_lt_one) hFmeas hFint hFprimeMeas hbound hCint hdiff
  simpa [μ, F, F'] using hmain

theorem aux_leftBumpOneShort_norm_setIntegral_Icc_le_const
    (F : ℝ → ℂ) (A : ℝ) (hA : ∀ t ∈ Icc (1 : ℝ) 2, ‖F t‖ ≤ A) :
    ‖∫ t : ℝ in Icc (1 : ℝ) 2, F t‖ ≤ A := by
  calc
    ‖∫ t : ℝ in Icc (1 : ℝ) 2, F t‖ ≤ A * volume.real (Icc (1 : ℝ) 2) :=
      norm_setIntegral_le_of_norm_le_const_ae' measure_Icc_lt_top
        (Filter.Eventually.of_forall hA)
    _ = A := by norm_num [Real.volume_Icc]

theorem aux_leftBumpOneShort_pair_logIntegral_deriv_bound
    (q : ℝ → ℂ) (hq : ContDiff ℝ 2 q) (C : ℝ) (hC : 0 ≤ C)
    (hqbound : ∀ m : ℕ, m ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv m q x‖ ≤ C) :
    ∀ m : ℕ, m < 3 → ∀ x : ℝ,
      ‖iteratedDeriv m (fun z : ℝ =>
        ∫ t : ℝ in Icc (1 : ℝ) 2,
          q (t * z) * q (-(t * z)) * ((t⁻¹ : ℝ) : ℂ)) x‖ ≤ 8 * C ^ 2 := by
  let H : ℝ → ℂ := fun z => q z * q (-z)
  have hH : ContDiff ℝ 2 H := by
    dsimp [H]
    exact aux_leftBumpOneShort_pair_contDiff q hq
  have hHbound : ∀ m : ℕ, m ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv m H x‖ ≤ (2 : ℝ) ^ m * C ^ 2 := by
    intro m hm x
    dsimp [H]
    exact aux_leftBumpOneShort_pair_deriv_bound q hq C hC hqbound m hm x
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hH0 : ∀ x : ℝ, ‖H x‖ ≤ C ^ 2 := by
    intro x
    simpa only [iteratedDeriv_zero, pow_zero, one_mul] using hHbound 0 (by norm_num) x
  have hH1 : ∀ x : ℝ, ‖deriv H x‖ ≤ 2 * C ^ 2 := by
    intro x
    rw [← iteratedDeriv_one]
    simpa using hHbound 1 (by norm_num) x
  have hH2 : ∀ x : ℝ, ‖deriv (deriv H) x‖ ≤ 4 * C ^ 2 := by
    intro x
    have heq : iteratedDeriv 2 H = deriv (deriv H) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
    rw [← heq]
    convert hHbound 2 (by norm_num) x using 1; norm_num
  have hHtwo : ContDiff ℝ 2 H := hH
  have hHderiv : ContDiff ℝ 1 (deriv H) := by simpa using hH.deriv'
  let I0 : ℝ → ℂ := fun z => ∫ t : ℝ in Icc (1 : ℝ) 2,
    H (t * z) * ((t⁻¹ : ℝ) : ℂ)
  let I1 : ℝ → ℂ := fun z => ∫ t : ℝ in Icc (1 : ℝ) 2, deriv H (t * z)
  let I2 : ℝ → ℂ := fun z => ∫ t : ℝ in Icc (1 : ℝ) 2,
    (t : ℝ) • deriv (deriv H) (t * z)
  have hD1 : ∀ x : ℝ, HasDerivAt I0 (I1 x) x := by
    intro x
    simpa only [I0, I1] using
      aux_leftBumpOneShort_integral_comp_inv_hasDeriv H hHtwo (2 * C ^ 2) hH1 x
  have hD2 : ∀ x : ℝ, HasDerivAt I1 (I2 x) x := by
    intro x
    simpa only [I1, I2] using
      aux_leftBumpOneShort_integral_comp_hasDeriv (deriv H) hHderiv (4 * C ^ 2)
        (by positivity) hH2 x
  have hI1 : deriv I0 = I1 := by
    funext x
    exact (hD1 x).deriv
  have hI2 : deriv I1 = I2 := by
    funext x
    exact (hD2 x).deriv
  have hI0bound : ∀ x : ℝ, ‖I0 x‖ ≤ C ^ 2 := by
    intro x
    apply aux_leftBumpOneShort_norm_setIntegral_Icc_le_const
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (le_trans zero_lt_one.le ht.1))]
    have htinvle : t⁻¹ ≤ 1 :=
      (inv_le_one₀ (lt_of_lt_of_le zero_lt_one ht.1)).2 ht.1
    calc
      ‖H (t * x)‖ * t⁻¹ ≤ C ^ 2 * t⁻¹ :=
        mul_le_mul_of_nonneg_right (hH0 _) (inv_nonneg.mpr (le_trans zero_lt_one.le ht.1))
      _ ≤ C ^ 2 * 1 := mul_le_mul_of_nonneg_left htinvle hC2
      _ = C ^ 2 := by ring
  have hI1bound : ∀ x : ℝ, ‖I1 x‖ ≤ 2 * C ^ 2 := by
    intro x
    apply aux_leftBumpOneShort_norm_setIntegral_Icc_le_const
    intro t ht
    exact hH1 _
  have hI2bound : ∀ x : ℝ, ‖I2 x‖ ≤ 8 * C ^ 2 := by
    intro x
    apply aux_leftBumpOneShort_norm_setIntegral_Icc_le_const
    intro t ht
    dsimp [I2]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_lt_one.le ht.1)]
    calc
      t * ‖deriv (deriv H) (t * x)‖ ≤ t * (4 * C ^ 2) :=
        mul_le_mul_of_nonneg_left (hH2 _) (le_trans zero_lt_one.le ht.1)
      _ ≤ 2 * (4 * C ^ 2) := mul_le_mul_of_nonneg_right ht.2 (by positivity)
      _ = 8 * C ^ 2 := by ring
  intro m hm x
  interval_cases m
  · rw [iteratedDeriv_zero]
    change ‖I0 x‖ ≤ _
    exact (hI0bound x).trans (by nlinarith [sq_nonneg C])
  · rw [iteratedDeriv_one, hI1]
    exact (hI1bound x).trans (by nlinarith [sq_nonneg C])
  · rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, hI1, hI2]
    exact hI2bound x

theorem aux_leftBumpOneShort_thetaTildeFourier_contDiff
    (b : windowBasedBumpFunctions) :
    ContDiff ℝ 3 (FourierTransform.fourier
      (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))) := by
  let Theta : SchwartzMap ℝ ℂ :=
    (thetaTildeSchwartz b).postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hTheta : (Theta : ℝ → ℂ) = fun x : ℝ =>
      (windowBasedBumpFunctions.thetaTilde b x : ℂ) := by
    funext x
    simp [Theta, thetaTildeSchwartz_apply, SchwartzMap.postcompCLM_apply]
  have hs : ContDiff ℝ 3 (FourierTransform.fourier Theta : ℝ → ℂ) :=
    (FourierTransform.fourier Theta).smooth 3
  rw [SchwartzMap.fourier_coe, hTheta] at hs
  exact hs

theorem aux_leftBumpOneShort_thetaTilde_pair_logIntegral_bound
    (b : windowBasedBumpFunctions) (m : ℕ) (hm : m < 3) (z : ℝ) :
    ‖iteratedDeriv m (fun x : ℝ => ∫ t : ℝ in Icc (1 : ℝ) 2,
      FourierTransform.fourier
        (fun y : ℝ => (windowBasedBumpFunctions.thetaTilde b y : ℂ)) (t * x) *
        FourierTransform.fourier
          (fun y : ℝ => (windowBasedBumpFunctions.thetaTilde b y : ℂ)) (-(t * x)) *
          ((t⁻¹ : ℝ) : ℂ)) z‖ ≤
      8 * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 := by
  exact aux_leftBumpOneShort_pair_logIntegral_deriv_bound
    (fun x : ℝ => FourierTransform.fourier
      (fun y : ℝ => (windowBasedBumpFunctions.thetaTilde b y : ℂ)) x)
    ((aux_leftBumpOneShort_thetaTildeFourier_contDiff b).of_le (by norm_num))
    ((2 : ℝ) ^ 14 * C_uniPair)
    (by norm_num [C_uniPair])
    (fun r hr x => thetaTildeFourier_deriv_bound b r (by omega) x)
    m hm z

theorem aux_leftBumpOneShort_phiFour_integralFct_plane_diagonal_eq
    (b : windowBasedBumpFunctions) (k : ℤ) (z : ℝ) :
    aux_planeFourier
      (fun v : RealPlane =>
        integralFctKernel (fun x : ℝ => phiFourSchwartz b k x)
          (WithLp.toLp 2 ![v.1, v.2]))
      (WithLp.toLp 2 ![z, -z]) =
      (((2 : ℝ) ^ (2 * k) : ℝ) : ℂ) *
        ∫ t : ℝ in Icc (1 : ℝ) 2,
          FourierTransform.fourier
            (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) (t * z) *
            FourierTransform.fourier
              (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) (-(t * z)) *
              ((t⁻¹ : ℝ) : ℂ) := by
  rw [aux_leftBumpOneShort_integralFctKernel_plane_diagonal_fourier_eq
    (phiFourSchwartz b k) z, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  have hpair := phiFour_fourier_pair_eq b k (t * z)
  simpa only [phiFourSchwartz_apply] using (show
    FourierTransform.fourier
        (fun x : ℝ => (windowBasedBumpFunctions.phiFour b k x : ℂ)) (t * z) *
        FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.phiFour b k x : ℂ)) (-(t * z)) *
          ((t⁻¹ : ℝ) : ℂ) =
      (((2 : ℝ) ^ (2 * k) : ℝ) : ℂ) *
        (FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) (t * z) *
          FourierTransform.fourier
            (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) (-(t * z)) *
          ((t⁻¹ : ℝ) : ℂ)) by
        rw [hpair]
        ring)

theorem aux_leftBumpOneShort_phiFour_base_diagonal_deriv_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (m : ℕ) (hm : m < 3) (z : ℝ) :
    ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane =>
          integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
            (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤
      (2 : ℝ) ^ (2 * k) * (8 * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2) := by
  let I : ℝ → ℂ := fun x => ∫ t : ℝ in Icc (1 : ℝ) 2,
    FourierTransform.fourier
      (fun y : ℝ => (windowBasedBumpFunctions.thetaTilde b y : ℂ)) (t * x) *
      FourierTransform.fourier
        (fun y : ℝ => (windowBasedBumpFunctions.thetaTilde b y : ℂ)) (-(t * x)) *
        ((t⁻¹ : ℝ) : ℂ)
  let s : ℝ := (2 : ℝ) ^ (2 * k)
  have hs : 0 ≤ s := (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hformula :
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane =>
          integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
            (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) =
      fun x => (s : ℂ) * I x := by
    funext x
    exact aux_leftBumpOneShort_phiFour_integralFct_plane_diagonal_eq b k x
  rw [hformula, iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs]
  exact mul_le_mul_of_nonneg_left
    (aux_leftBumpOneShort_thetaTilde_pair_logIntegral_bound b m hm z) hs

theorem aux_leftBumpOneShort_normalizer_dominates_thetaTilde_pair :
    8 * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2 ≤
      aux_leftBumpOneShort_whitneyNormalizer := by
  norm_num [aux_leftBumpOneShort_whitneyNormalizer, C_thetaPrimitive,
    C_uniPair, C_thetaTOffcenter]

theorem aux_leftBumpOneShort_rpow_zpow_product_eq (k : ℤ) :
    Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) * (2 : ℝ) ^ (2 * k) =
      Real.rpow 2 ((k : ℝ) / 2) := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  rw [show (2 : ℝ) ^ (2 * k) = Real.rpow 2 ((2 * k : ℤ) : ℝ) by
    exact (Real.rpow_intCast 2 (2 * k)).symm]
  calc
    Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
        Real.rpow 2 ((2 * k : ℤ) : ℝ) =
        Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2 + ((2 * k : ℤ) : ℝ)) :=
      (Real.rpow_add htwo _ _).symm
    _ = Real.rpow 2 ((k : ℝ) / 2) := by
      congr 1
      push_cast
      ring

theorem aux_leftBumpOneShort_rpow_zpow_product_le_one
    (k : ℤ) (hk : k ≤ -1) :
    Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) * (2 : ℝ) ^ (2 * k) ≤ 1 := by
  rw [aux_leftBumpOneShort_rpow_zpow_product_eq]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have hkreal : (k : ℝ) ≤ -1 := by exact_mod_cast hk
  linarith

theorem aux_leftBumpOneShort_raw_scaled_diagonal_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (m : ℕ) (hm : m < 3) (z : ℝ) :
    ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane =>
          Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
            integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
              (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤
      aux_leftBumpOneShort_whitneyNormalizer := by
  let P : ℝ := Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)
  let s : ℝ := (2 : ℝ) ^ (2 * k)
  let B : ℝ := 8 * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2
  have hP : 0 ≤ P := Real.rpow_nonneg (by norm_num) _
  have hs : 0 ≤ s := (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbase := aux_leftBumpOneShort_phiFour_base_diagonal_deriv_bound b k m hm z
  have hformula :
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => P *
          integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
            (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) =
      fun x => (P : ℂ) * aux_planeFourier
        (fun v : RealPlane =>
          integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
            (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x]) := by
    funext x
    rw [aux_leftBumpOneShort_planeFourier_const_mul]
  change ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => P *
          integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
            (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤ _
  rw [hformula, iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hP]
  have hbase' : ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane =>
          integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
            (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤ s * B := by
    simpa only [s, B] using hbase
  calc
    P * ‖iteratedDeriv m
        (fun x : ℝ => aux_planeFourier
          (fun v : RealPlane =>
            integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
              (WithLp.toLp 2 ![v.1, v.2]))
          (WithLp.toLp 2 ![x, -x])) z‖ ≤ P * (s * B) :=
      mul_le_mul_of_nonneg_left hbase' hP
    _ = (P * s) * B := by ring
    _ ≤ 1 * B := mul_le_mul_of_nonneg_right
      (by simpa only [P, s] using
        aux_leftBumpOneShort_rpow_zpow_product_le_one k hk) hB
    _ = B := by ring
    _ ≤ aux_leftBumpOneShort_whitneyNormalizer :=
      aux_leftBumpOneShort_normalizer_dominates_thetaTilde_pair

theorem aux_leftBumpOneShort_normalized_diagonal_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (m : ℕ) (hm : m < 3) (z : ℝ) :
    ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane =>
          (aux_leftBumpOneShort_whitneyNormalizer)⁻¹ *
            Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2) *
            integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
              (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤ 1 := by
  let D : ℝ := aux_leftBumpOneShort_whitneyNormalizer
  let P : ℝ := Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)
  let M : RealPlane → ℝ := fun v => P *
    integralFctKernel (fun y : ℝ => phiFourSchwartz b k y)
      (WithLp.toLp 2 ![v.1, v.2])
  have hraw : ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier M (WithLp.toLp 2 ![x, -x])) z‖ ≤ D := by
    simpa only [D, P, M] using
      aux_leftBumpOneShort_raw_scaled_diagonal_bound b k hk m hm z
  have hnorm := aux_leftBumpOneShort_planeFourier_normalize_diagonal D
    (by simpa only [D] using aux_leftBumpOneShort_whitneyNormalizer_pos)
    M m z hraw
  simpa only [D, P, M, mul_assoc] using hnorm

theorem aux_leftBumpOneShort_whitneySequence_integralM_eq
    (c : ℝ) (psi : SchwartzMap ℝ ℝ) (a : ℤ → ℝ) :
    aux_whitneySequence
      (fun v : RealPlane => c * integralFctKernel (fun x => psi x)
        (WithLp.toLp 2 ![v.1, v.2])) a =
      fun j y => c * aux_leftBumpOneShort_integralM (a j) psi y := by
  funext j y
  let u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![y.1 0, y.2 0]
  have hu0 : u 0 = y.1 0 := by simp [u]
  have hu1 : u 1 = y.2 0 := by simp [u]
  have hbase := planeRescale_integralFctKernel_eq (a j) (fun x => psi x) u
  change (a j)⁻¹ ^ 2 *
      (c * integralFctKernel (fun x => psi x)
        (WithLp.toLp 2 ![(a j)⁻¹ * y.1 0, (a j)⁻¹ * y.2 0])) = _
  rw [hu0, hu1] at hbase
  have hbase' : (a j)⁻¹ ^ 2 *
      integralFctKernel (fun x => psi x)
        (WithLp.toLp 2 ![(a j)⁻¹ * y.1 0, (a j)⁻¹ * y.2 0]) =
      aux_integralFctKernelAtScale (a j) (fun x => psi x) u := by
    simpa [aux_planeRescale] using hbase
  calc
    (a j)⁻¹ ^ 2 *
        (c * integralFctKernel (fun x => psi x)
          (WithLp.toLp 2 ![(a j)⁻¹ * y.1 0, (a j)⁻¹ * y.2 0])) =
        c * ((a j)⁻¹ ^ 2 * integralFctKernel (fun x => psi x)
          (WithLp.toLp 2 ![(a j)⁻¹ * y.1 0, (a j)⁻¹ * y.2 0])) := by ring
    _ = c * aux_integralFctKernelAtScale (a j) (fun x => psi x) u := by rw [hbase']
    _ = c * aux_leftBumpOneShort_integralM (a j) psi y := by
      simp [aux_leftBumpOneShort_integralM, u]

theorem aux_leftBumpOneShort_integralM_zero_of_kernel_zero
    (c : ℝ) (hc : 0 < c) (psi : SchwartzMap ℝ ℝ)
    (hzero : (fun v : RealPlane => c * integralFctKernel (fun x => psi x)
      (WithLp.toLp 2 ![v.1, v.2])) = 0) (s : ℝ) :
    aux_leftBumpOneShort_integralM s psi = 0 := by
  have hbase : (fun v : RealPlane => integralFctKernel (fun x => psi x)
      (WithLp.toLp 2 ![v.1, v.2])) = 0 := by
    funext v
    have hv := congrFun hzero v
    exact (mul_eq_zero.mp hv).resolve_left hc.ne'
  funext y
  let u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![y.1 0, y.2 0]
  have hplane := planeRescale_integralFctKernel_eq s (fun x => psi x) u
  change aux_integralFctKernelAtScale s (fun x => psi x) u = 0
  rw [← hplane]
  change s⁻¹ ^ 2 * integralFctKernel (fun x => psi x)
    (WithLp.toLp 2 ![s⁻¹ * u 0, s⁻¹ * u 1]) = 0
  rw [show integralFctKernel (fun x => psi x)
      (WithLp.toLp 2 ![s⁻¹ * u 0, s⁻¹ * u 1]) = 0 by
        exact congrFun hbase (s⁻¹ * u 0, s⁻¹ * u 1)]
  ring

theorem aux_leftBumpOneShort_prismForm_const_mul
    {n : ℕ} (hn : 1 ≤ n) (c : ℝ) (M : MKernel 1)
    (F : Fin n → RealVector n → ℝ) :
    prismForm n 1 (by omega) hn (fun y => c * M y) F =
      c * prismForm n 1 (by omega) hn M F := by
  unfold prismForm prismBrascampLiebForm mToK
  simp_rw [integral_const_mul]
  rw [show (fun y : RealVector 1 × RealVector 1 =>
      ∫ x : RealVector (n - 1 + 1),
        (c * ∫ p : RealVector (1 - 1),
          M (mToKPoint 1 (by omega)
            (y.2 - y.1, Auto.coordinateSum y.1 +
              Auto.coordinateSum x) p)) *
          ∏ h : Fin 1 → Fin 2, ∏ i : Fin (n - 1 + 1),
            F (prismIndex (by omega) hn i)
              (prismPoint (by omega) hn y x h i)) =
      fun y => c * ∫ x : RealVector (n - 1 + 1),
        (∫ p : RealVector (1 - 1),
          M (mToKPoint 1 (by omega)
            (y.2 - y.1, Auto.coordinateSum y.1 +
              Auto.coordinateSum x) p)) *
          ∏ h : Fin 1 → Fin 2, ∏ i : Fin (n - 1 + 1),
            F (prismIndex (by omega) hn i)
              (prismPoint (by omega) hn y x h i) by
    funext y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring]
  rw [integral_const_mul]

theorem aux_leftBumpOneShort_prismForm_zero
    {n : ℕ} (hn : 1 ≤ n) (F : Fin n → RealVector n → ℝ) :
    prismForm n 1 (by omega) hn (0 : MKernel 1) F = 0 := by
  unfold prismForm prismBrascampLiebForm mToK
  simp

theorem aux_leftBumpOneShort_zero_energy_sum
    {d J : ℕ} (c : ℝ) (hc : 0 < c) (psi : SchwartzMap ℝ ℝ)
    (hzero : (fun v : RealPlane => c * integralFctKernel (fun x => psi x)
      (WithLp.toLp 2 ![v.1, v.2])) = 0)
    (a : ℤ → ℝ) (f : ReductionNormalizedTuple (d + 1))
    (P : ℝ) (E : Fin J → ℝ≥0∞)
    (henergy : ∀ j : Fin J,
      E j = ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi)
          (fun i x =>
            Auto.aux_aToLambda.transformedFunctions f.1 i x))) :
    ∑ j : Fin J, ENNReal.ofReal P * E j = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  rw [henergy j,
    aux_leftBumpOneShort_integralM_zero_of_kernel_zero c hc psi hzero (a (j : ℤ))]
  simp [aux_leftBumpOneShort_prismForm_zero]

theorem aux_leftBumpOneShort_planeRescale_memW0
    (Psi : RealPlane → ℝ) (hPsi : MemW0 Psi) {t : ℝ} (ht : 0 < t) :
    MemW0 (aux_planeRescale t Psi) := by
  let e : RealPlane ≃L[ℝ] RealPlane :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 t⁻¹ (inv_ne_zero ht.ne'))
  have hcomp : MemW0 (Psi ∘ e) := aux_memW0_comp_continuousLinearEquiv hPsi e
  have hscale : 0 ≤ t⁻¹ ^ 2 := sq_nonneg _
  have h := aux_memW0_const_mul_nonneg hcomp (t⁻¹ ^ 2) hscale
  convert h using 1
  funext v
  change t⁻¹ ^ 2 * Psi (t⁻¹ * v.1, t⁻¹ * v.2) = t⁻¹ ^ 2 * Psi (t⁻¹ • v)
  congr 2

theorem aux_leftBumpOneShort_liftPlaneKernel_memW0
    (M : RealPlane → ℝ) (hM : MemW0 M) :
    MemW0 (aux_liftPlaneKernel M) := by
  let : Measure.IsAddHaarMeasure (volume : Measure (RealVector 1 × RealVector 1)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let : Measure.IsAddHaarMeasure (volume : Measure RealPlane) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let e : (RealVector 1 × RealVector 1) ≃L[ℝ] RealPlane :=
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).prodCongr
      (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ))
  have hcomp : MemW0 (M ∘ e) := aux_memW0_comp_continuousLinearEquiv hM e
  convert hcomp using 1
  funext x
  rfl

theorem aux_leftBumpOneShort_whitneySequence_memW0
    (Psi : WhitneyKernelData) (a : ℤ → ℝ) (ha : SpacedSequence a) :
    ∀ j : ℤ, MemW0 (aux_whitneySequence Psi.kernel a j) := by
  intro j
  dsimp [aux_whitneySequence]
  exact aux_leftBumpOneShort_liftPlaneKernel_memW0 _
    (aux_leftBumpOneShort_planeRescale_memW0 _ Psi.kernel_memW0 (ha j).1)

theorem aux_leftBumpOneShort_planeRescale_positive
    (Psi : RealPlane → ℝ)
    (hpos : ∀ g : ℝ → ℝ, aux_bounded g →
      0 ≤ ∫ v : RealPlane, g v.1 * g v.2 * Psi v)
    {t : ℝ} (ht : 0 < t) :
    ∀ g : ℝ → ℝ, aux_bounded g →
      0 ≤ ∫ v : RealPlane, g v.1 * g v.2 * aux_planeRescale t Psi v := by
  intro g hg
  let gt : ℝ → ℝ := fun x => g (t * x)
  have hgt : aux_bounded gt := by
    constructor
    · exact hg.1.comp (by fun_prop)
    · apply hg.2.subset
      rintro y ⟨x, rfl⟩
      exact ⟨t * x, rfl⟩
  let F : RealPlane → ℝ := fun q => gt q.1 * gt q.2 * Psi q
  have hbase : 0 ≤ ∫ q : RealPlane, F q := by
    simpa [F] using hpos gt hgt
  have hformula : (fun v : RealPlane => g v.1 * g v.2 * aux_planeRescale t Psi v) =
      fun v : RealPlane => t⁻¹ ^ 2 * F (t⁻¹ • v) := by
    funext v
    have hscalev : t⁻¹ • v = (t⁻¹ * v.1, t⁻¹ * v.2) := rfl
    rw [hscalev]
    dsimp [aux_planeRescale, F, gt]
    field_simp [ne_of_gt ht]
  rw [hformula, integral_const_mul, Measure.integral_comp_inv_smul]
  norm_num [Module.finrank_prod]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]
  exact hbase

theorem aux_leftBumpOneShort_whitney_lift_positive
    (M : RealPlane → ℝ)
    (hquad : ∀ g : ℝ → ℝ, aux_bounded g →
      0 ≤ ∫ v : RealPlane, g v.1 * g v.2 * M v) :
    ∀ g : ℝ → ℝ, aux_bounded g →
      0 ≤ ∫ u : RealVector 1 × RealVector 1,
        g (u.1 0) * g (u.2 0) * aux_liftPlaneKernel M u := by
  intro g hg
  let e1 : RealVector 1 ≃ᵐ ℝ := MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  let e : (RealVector 1 × RealVector 1) ≃ᵐ RealPlane := e1.prodCongr e1
  have he1 : MeasurePreserving e1 volume volume := by
    simpa [e1] using volume_preserving_piUnique (fun _ : Fin 1 => ℝ)
  have he : MeasurePreserving e volume volume := by
    change MeasurePreserving (Prod.map e1 e1) volume volume
    simpa only [Measure.volume_eq_prod] using he1.prod he1
  let G : RealPlane → ℝ := fun v => g v.1 * g v.2 * M v
  calc
    0 ≤ ∫ v : RealPlane, G v := by simpa [G] using hquad g hg
    _ = ∫ u : RealVector 1 × RealVector 1, G (e u) := (he.integral_comp' G).symm
    _ = ∫ u : RealVector 1 × RealVector 1,
        g (u.1 0) * g (u.2 0) * aux_liftPlaneKernel M u := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [G, e, e1, aux_liftPlaneKernel]
      rfl

theorem aux_leftBumpOneShort_whitneySequence_form_nonneg
    {n : ℕ} (hn : 1 ≤ n) (Psi : WhitneyKernelData)
    (a : ℤ → ℝ) (ha : SpacedSequence a) (j : ℤ)
    (F : Fin n → SchwartzMap (RealVector n) ℝ) :
    0 ≤ prismForm n 1 (by omega) hn (aux_whitneySequence Psi.kernel a j)
      (fun i x => F i x) := by
  apply formPos hn (aux_whitneySequence Psi.kernel a j)
  · exact aux_leftBumpOneShort_whitneySequence_memW0 Psi a ha j
  · dsimp [aux_whitneySequence]
    exact aux_leftBumpOneShort_whitney_lift_positive _
      (aux_leftBumpOneShort_planeRescale_positive Psi.kernel Psi.positive (ha j).1)

theorem aux_leftBumpOneShort_prismForm_finset_sum
    {n J : ℕ} (hn : 1 ≤ n) (M : Fin J → MKernel 1)
    (hM : ∀ j, MemW0 (M j))
    (F : Fin n → SchwartzMap (RealVector n) ℝ) :
    prismForm n 1 (by omega) hn (fun y => ∑ j, M j y) (fun i x => F i x) =
      ∑ j, prismForm n 1 (by omega) hn (M j) (fun i x => F i x) := by
  have hK (j : Fin J) : MemW0 (mToK 1 (by omega) (M j)) :=
    mToK_memW0 n 1 (by omega) hn _ (hM j)
  unfold prismForm
  rw [aux_mToK_finset_sum 1 J (by omega) M hM]
  exact aux_prismBrascampLiebForm_finset_sum n 1 J (by omega) hn
    (fun j => mToK 1 (by omega) (M j)) hK F

theorem aux_leftBumpOneShort_scaled_integralM_prefix
    {d J : ℕ} (hd : 1 ≤ d)
    (D P c : ℝ) (hD : 0 < D) (hc : 0 < c) (hPc : D * c = P)
    (psi : SchwartzMap ℝ ℝ) (a : ℤ → ℝ) (ha : SpacedSequence a)
    (f : ReductionNormalizedTuple (d + 1)) (hJ : 0 < J)
    (phi0 phi1 : SchwartzMap ℝ ℝ) (hpair : uniPair phi0 phi1)
    (Psi : WhitneyKernelData)
    (hPsi : Psi.kernel = fun v : RealPlane => c *
      integralFctKernel (fun x => psi x) (WithLp.toLp 2 ![v.1, v.2]))
    (E : Fin J → ℝ≥0∞)
    (henergy : ∀ j : Fin J,
      E j = ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi)
          (fun i x =>
            Auto.aux_aToLambda.transformedFunctions f.1 i x))) :
    ∑ j : Fin J, ENNReal.ofReal P * E j ≤
      ENNReal.ofReal (D * C_inductPositiveTermsReductionWhitney (d + 1)) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := by
  classical
  let F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ :=
    Auto.aux_aToLambda.transformedFunctions f.1
  let Fnorm : NormalizedFunctionTuple (d + 1) := ⟨F, by
    intro i
    dsimp [F]
    convert
      (Auto.aux_aToLambda.transformedFunctions_eLpNorm f.1 i
        ((2 : ℝ≥0∞) ^ (i.val + min (d + 1 - i.val) 2))).trans (f.2 i) using 1;
      norm_num⟩
  let M : KernelSequence 1 := aux_whitneySequence Psi.kernel a
  have hMbound : kernelSequenceSeminorm (d + 1) 1 (by omega) (by omega) M ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionWhitney (d + 1)) := by
    dsimp [M]
    exact inductPositiveTermsReductionWhitney (by omega) a ha phi0 phi1 hpair Psi
  have hseq : M = fun j y => c * aux_leftBumpOneShort_integralM (a j) psi y := by
    dsimp [M]
    rw [hPsi]
    exact aux_leftBumpOneShort_whitneySequence_integralM_eq c psi a
  have henergyF (j : Fin J) : E j = ENNReal.ofReal
      (prismForm (d + 1) 1 (by omega) (by omega)
        (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi) (fun i x => F i x)) := by
    simpa [F] using henergy j
  have hMmem (j : Fin J) : MemW0 (M (j : ℤ)) := by
    dsimp [M]
    exact aux_leftBumpOneShort_whitneySequence_memW0 Psi a ha (j : ℤ)
  have hMform (j : Fin J) : 0 ≤
      prismForm (d + 1) 1 (by omega) (by omega) (M (j : ℤ))
        (fun i x => F i x) := by
    dsimp [M]
    exact aux_leftBumpOneShort_whitneySequence_form_nonneg (by omega)
      Psi a ha (j : ℤ) F
  have hMscale (j : Fin J) :
      prismForm (d + 1) 1 (by omega) (by omega) (M (j : ℤ))
          (fun i x => F i x) =
        c * prismForm (d + 1) 1 (by omega) (by omega)
          (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi) (fun i x => F i x) := by
    rw [hseq]
    exact aux_leftBumpOneShort_prismForm_const_mul (n := d + 1) (by omega) c
      (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi) (fun i x => F i x)
  have hformsum :
      prismForm (d + 1) 1 (by omega) (by omega)
        (fun y => ∑ j : Fin J, M (j : ℤ) y) (fun i x => F i x) =
      ∑ j : Fin J, prismForm (d + 1) 1 (by omega) (by omega)
        (M (j : ℤ)) (fun i x => F i x) := by
    exact aux_leftBumpOneShort_prismForm_finset_sum (by omega)
      (fun j => M (j : ℤ)) hMmem F
  have hsumNonneg : 0 ≤ prismForm (d + 1) 1 (by omega) (by omega)
      (fun y => ∑ j : Fin J, M (j : ℤ) y) (fun i x => F i x) := by
    rw [hformsum]
    exact Finset.sum_nonneg fun j _ => hMform j
  have hsumKernel :
      (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y) =
        fun y => ∑ j : Fin J, M (j : ℤ) y := by
    funext y
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => M (j : ℤ) y) J]
  have hprefix := aux_mainAuxOne_prefix_from_seminorm (by omega) M
    (C_inductPositiveTermsReductionWhitney (d + 1)) hMbound J hJ Fnorm
  have hprefix' : ENNReal.ofReal
      |prismForm (d + 1) 1 (by omega) (by omega)
        (fun y => ∑ j : Fin J, M (j : ℤ) y) (fun i x => F i x)| ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionWhitney (d + 1)) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := by
    rw [← hsumKernel]
    simpa [Fnorm] using hprefix
  have hP : 0 ≤ P := by rw [← hPc]; positivity
  have hleft : ∑ j : Fin J, ENNReal.ofReal P * E j =
      ENNReal.ofReal D * ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (fun y => ∑ j : Fin J, M (j : ℤ) y) (fun i x => F i x)) := by
    calc
      ∑ j : Fin J, ENNReal.ofReal P * E j =
          ∑ j : Fin J, ENNReal.ofReal D * ENNReal.ofReal
            (prismForm (d + 1) 1 (by omega) (by omega)
              (M (j : ℤ)) (fun i x => F i x)) := by
            apply Finset.sum_congr rfl
            intro j _
            calc
              ENNReal.ofReal P * E j = ENNReal.ofReal P * ENNReal.ofReal
                  (prismForm (d + 1) 1 (by omega) (by omega)
                    (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi)
                    (fun i x => F i x)) := by rw [henergyF]
              _ = ENNReal.ofReal (P * prismForm (d + 1) 1 (by omega) (by omega)
                    (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi)
                    (fun i x => F i x)) := (ENNReal.ofReal_mul hP).symm
              _ = ENNReal.ofReal (D * prismForm (d + 1) 1 (by omega) (by omega)
                    (M (j : ℤ)) (fun i x => F i x)) := by
                    congr 1
                    rw [← hPc, hMscale]
                    ring
              _ = ENNReal.ofReal D * ENNReal.ofReal
                  (prismForm (d + 1) 1 (by omega) (by omega)
                    (M (j : ℤ)) (fun i x => F i x)) := ENNReal.ofReal_mul hD.le
      _ = ENNReal.ofReal D * ∑ j : Fin J, ENNReal.ofReal
          (prismForm (d + 1) 1 (by omega) (by omega)
            (M (j : ℤ)) (fun i x => F i x)) := by rw [Finset.mul_sum]
      _ = ENNReal.ofReal D * ENNReal.ofReal
          (∑ j : Fin J, prismForm (d + 1) 1 (by omega) (by omega)
            (M (j : ℤ)) (fun i x => F i x)) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro j _
            exact hMform j
      _ = ENNReal.ofReal D * ENNReal.ofReal
          (prismForm (d + 1) 1 (by omega) (by omega)
            (fun y => ∑ j : Fin J, M (j : ℤ) y) (fun i x => F i x)) := by
            rw [hformsum]
  calc
    ∑ j : Fin J, ENNReal.ofReal P * E j =
        ENNReal.ofReal D * ENNReal.ofReal
          (prismForm (d + 1) 1 (by omega) (by omega)
            (fun y => ∑ j : Fin J, M (j : ℤ) y) (fun i x => F i x)) := hleft
    _ = ENNReal.ofReal D * ENNReal.ofReal
        |prismForm (d + 1) 1 (by omega) (by omega)
          (fun y => ∑ j : Fin J, M (j : ℤ) y) (fun i x => F i x)| := by
          rw [abs_of_nonneg hsumNonneg]
    _ ≤ ENNReal.ofReal D *
        (ENNReal.ofReal (C_inductPositiveTermsReductionWhitney (d + 1)) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1))) :=
      mul_le_mul_of_nonneg_left hprefix' bot_le
    _ = (ENNReal.ofReal D *
        ENNReal.ofReal (C_inductPositiveTermsReductionWhitney (d + 1))) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := by ac_rfl
    _ = ENNReal.ofReal (D * C_inductPositiveTermsReductionWhitney (d + 1)) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := by
      rw [← ENNReal.ofReal_mul hD.le]


/--
The first short-variation constant in Lemma
`Auto.leftBumpOneShortOne`.
-/
noncomputable def C_leftBumpOneShortOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 2 * C_inductPositiveTermsReductionWhitney n * C_thetaPrimitive 2 ^ 2 *
    C_thetaTOffcenter

/--
**Lemma.**

Let $\gamma=\frac12$. For every $k\le-1$ and every strictly increasing sequence of integers
$(k_j)_{j\in[J)}$,

$$
\sum_{j\in[J)}2^{-(1+\gamma)k}\int_1^2
\|A_{2^{k_j}t}(\varphi_{4,k})\|_2^2\,\tfrac{dt}{t}
\le C_{\text{lem:leftbump1\_short1}}J^{\alpha(n)},
$$

where

$$
C_{\text{lem:leftbump1\_short1}}
=2^2C_{\text{induct positive terms - reduction variant, Whitney}}
C_{\text{lem:theta\_prim},2}^2C_{\text{lem:thetat\_offcenter}}.
$$

See also `Auto.leftBumpOneShortOne`,
`Auto.inductPositiveTermsReductionWhitney`,
`Auto.thetaPrimitive`,
`Auto.thetaTOffcenter`.
-/
theorem leftBumpOneShortOne {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (k : ℤ) (hk : k ≤ -1) (J : ℕ) (hJ : 0 < J)
    (ell : aux_dyadicChain J) :
    ∑ j : Fin J,
      ENNReal.ofReal (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)) *
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          ENNReal.ofReal t⁻¹ *
            eLpNorm
              (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc) * t)
                (windowBasedBumpFunctions.phiFour b k) (fun i x ↦ f.1 i x))
              2 volume ^ 2 ≤
      ENNReal.ofReal (C_leftBumpOneShortOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  cases n with
  | zero => omega
  | succ d =>
    have hd : 1 ≤ d := by omega
    obtain ⟨a, ha, ha_restrict⟩ := aux_mainAuxOne_extend_dyadic_chain J hJ ell
    let E : Fin J → ℝ≥0∞ := fun j =>
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ENNReal.ofReal t⁻¹ *
          eLpNorm
            (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc) * t)
              (windowBasedBumpFunctions.phiFour b k) (fun i x => f.1 i x))
            2 volume ^ 2
    have henergy : ∀ j : Fin J,
        E j = ENNReal.ofReal
          (prismForm (d + 1) 1 (by omega) (by omega)
            (aux_leftBumpOneShort_integralM (a (j : ℤ)) (phiFourSchwartz b k))
            (fun i x =>
              Auto.aux_aToLambda.transformedFunctions f.1 i x)) := by
      intro j
      dsimp [E]
      rw [← ha_restrict j]
      simpa only [phiFourSchwartz_apply] using
        aux_leftBumpOneShort_continuous_aToLambda_integralFct d
          (a (j : ℤ)) (ha (j : ℤ)).1 (phiFourSchwartz b k) f.1
    let D : ℝ := aux_leftBumpOneShort_whitneyNormalizer
    let P : ℝ := Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)
    let c : ℝ := D⁻¹ * P
    have hD : 0 < D := by
      simpa only [D] using aux_leftBumpOneShort_whitneyNormalizer_pos
    have hP : 0 < P := by
      dsimp [P]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hc : 0 < c := mul_pos (inv_pos.mpr hD) hP
    have hPc : D * c = P := by
      dsimp [c]
      field_simp [hD.ne']
    change ∑ j : Fin J, ENNReal.ofReal P * E j ≤
      ENNReal.ofReal (C_leftBumpOneShortOne (d + 1)) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1))
    by_cases hzero : (fun v : RealPlane => c *
        integralFctKernel (windowBasedBumpFunctions.phiFour b k)
          (WithLp.toLp 2 ![v.1, v.2])) = 0
    · have hsum := aux_leftBumpOneShort_zero_energy_sum c hc (phiFourSchwartz b k)
        (by simpa only [phiFourSchwartz_apply] using hzero) a f P E henergy
      rw [hsum]
      exact bot_le
    · let Psi : WhitneyKernelData := aux_leftBumpOneShort_whitneyData b k hk
        (by simpa only [c, D, P] using hzero)
        (fun m hm xi =>
          aux_leftBumpOneShort_normalized_diagonal_bound b k hk m hm xi)
      have hPsi : Psi.kernel = fun v : RealPlane => c *
          integralFctKernel (fun x => phiFourSchwartz b k x)
            (WithLp.toLp 2 ![v.1, v.2]) := by
        dsimp [Psi]
        rfl
      have hmain := aux_leftBumpOneShort_scaled_integralM_prefix hd D P c hD hc hPc
        (phiFourSchwartz b k) a ha f hJ b.phi0 b.phi1 b.universalPair Psi hPsi E henergy
      have hconst : D * C_inductPositiveTermsReductionWhitney (d + 1) =
          C_leftBumpOneShortOne (d + 1) := by
        dsimp [D, aux_leftBumpOneShort_whitneyNormalizer]
        unfold C_leftBumpOneShortOne
        ring
      calc
        ∑ j : Fin J, ENNReal.ofReal P * E j ≤
            ENNReal.ofReal (D * C_inductPositiveTermsReductionWhitney (d + 1)) *
              ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := hmain
        _ = ENNReal.ofReal (C_leftBumpOneShortOne (d + 1)) *
              ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := by
              rw [hconst]

/--
**Lemma (constant $C_{\text{lem:leftbump1\_short1}}$).**

$$
C_{\text{lem:leftbump1\_short1}}
<2^{628}.
$$

See also `Auto.leftBumpOneShortOne`.
-/
theorem constantLeftBumpOneShortOne {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneShortOne n <
      (185801 / 262144 : ℝ) * (2 : ℝ) ^ 628 := by
  have hWhitney : C_inductPositiveTermsReductionWhitney n <
      (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
    unfold C_inductPositiveTermsReductionWhitney
    calc
      11 * C_inductPositiveTermsReductionWhitneyGap n <
          11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553) :=
        mul_lt_mul_of_pos_left (constantWhitneyGapReduction hn) (by norm_num)
      _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 4 * (2 : ℝ) ^ 553) := by
        norm_num
        set_option exponentiation.threshold 1000 in
          ring
      _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
        rw [← pow_add]
  have hA : 0 < (2 : ℝ) ^ 2 * C_thetaPrimitive 2 ^ 2 * C_thetaTOffcenter := by
    norm_num [C_thetaPrimitive, C_uniPair, C_thetaTOffcenter]
  unfold C_leftBumpOneShortOne
  calc
    (2 : ℝ) ^ 2 * C_inductPositiveTermsReductionWhitney n * C_thetaPrimitive 2 ^ 2 *
        C_thetaTOffcenter =
        ((2 : ℝ) ^ 2 * C_thetaPrimitive 2 ^ 2 * C_thetaTOffcenter) *
          C_inductPositiveTermsReductionWhitney n := by ring
    _ < ((2 : ℝ) ^ 2 * C_thetaPrimitive 2 ^ 2 * C_thetaTOffcenter) *
        ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) :=
      mul_lt_mul_of_pos_left hWhitney hA
    _ = (185801 / 262144 : ℝ) * ((2 : ℝ) ^ 71 * (2 : ℝ) ^ 557) := by
      norm_num [C_thetaPrimitive, C_uniPair, C_thetaTOffcenter]
      set_option exponentiation.threshold 1000 in
        ring
    _ = (185801 / 262144 : ℝ) * (2 : ℝ) ^ 628 := by
      rw [← pow_add]

/--
The second short-variation auxiliary constant in Lemma
`Auto.leftBumpOneShortTwo`.
-/
noncomputable def C_leftBumpOneShortTwoAuxiliary : ℝ :=
  max (C_thetaPrimitive 2) (max (C_thetaDecay 2) (C_thetaDecay 3))

/--
The second short-variation constant in Lemma
`Auto.leftBumpOneShortTwo`.
-/
noncomputable def C_leftBumpOneShortTwo (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitney n * C_thetaTOffcenter *
    C_leftBumpOneShortTwoAuxiliary ^ 2


theorem aux_leftBumpOneShortTwo_product_deriv_bound
    (p q : ℝ → ℂ) (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q)
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hpbound : ∀ i : ℕ, i ≤ 2 → ∀ x : ℝ, ‖iteratedDeriv i p x‖ ≤ A)
    (hqbound : ∀ i : ℕ, i ≤ 2 → ∀ x : ℝ, ‖iteratedDeriv i q x‖ ≤ B) :
    ∀ m : ℕ, m ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv m (p * q) x‖ ≤ (2 : ℝ) ^ m * A * B := by
  intro m hm x
  have hpAt : ContDiffAt ℝ (m : ℕ∞) p x := by
    apply (hp.of_le (m := (m : WithTop ℕ∞)) ?_).contDiffAt
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast hm
  have hqAt : ContDiffAt ℝ (m : ℕ∞) q x := by
    apply (hq.of_le (m := (m : WithTop ℕ∞)) ?_).contDiffAt
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast hm
  rw [iteratedDeriv_mul hpAt hqAt]
  calc
    ‖∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i p x * iteratedDeriv (m - i) q x‖ ≤
        ∑ i ∈ Finset.range (m + 1),
          ‖(m.choose i : ℂ) * iteratedDeriv i p x * iteratedDeriv (m - i) q x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (A * B) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hmi : m - i ≤ m := Nat.sub_le _ _
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        ↑(m.choose i) * ‖iteratedDeriv i p x‖ * ‖iteratedDeriv (m - i) q x‖ ≤
            ↑(m.choose i) * A * B := by
          gcongr
          · exact hpbound i (le_trans him hm) x
          · exact hqbound (m - i) (le_trans hmi hm) x
        _ = (m.choose i : ℝ) * (A * B) := by ring
    _ ≤ (2 : ℝ) ^ m * A * B := by
      interval_cases m <;> norm_num [Finset.sum_range_succ, Nat.choose] <;>
        ring_nf <;> exact le_rfl

theorem aux_leftBumpOneShortTwo_product_deriv_bound_at
    (p q : ℝ → ℂ) (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q)
    (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B) (x : ℝ)
    (hpbound : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i p x‖ ≤ A)
    (hqbound : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i q x‖ ≤ B) :
    ∀ m : ℕ, m ≤ 2 →
      ‖iteratedDeriv m (p * q) x‖ ≤ (2 : ℝ) ^ m * A * B := by
  intro m hm
  have hpAt : ContDiffAt ℝ (m : ℕ∞) p x := by
    apply (hp.of_le (m := (m : WithTop ℕ∞)) ?_).contDiffAt
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast hm
  have hqAt : ContDiffAt ℝ (m : ℕ∞) q x := by
    apply (hq.of_le (m := (m : WithTop ℕ∞)) ?_).contDiffAt
    apply WithTop.coe_le_coe.mpr
    exact_mod_cast hm
  rw [iteratedDeriv_mul hpAt hqAt]
  calc
    ‖∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i p x * iteratedDeriv (m - i) q x‖ ≤
        ∑ i ∈ Finset.range (m + 1),
          ‖(m.choose i : ℂ) * iteratedDeriv i p x * iteratedDeriv (m - i) q x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (A * B) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hmi : m - i ≤ m := Nat.sub_le _ _
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        ↑(m.choose i) * ‖iteratedDeriv i p x‖ * ‖iteratedDeriv (m - i) q x‖ ≤
            ↑(m.choose i) * A * B := by
          gcongr
          · exact hpbound i (le_trans him hm)
          · exact hqbound (m - i) (le_trans hmi hm)
        _ = (m.choose i : ℝ) * (A * B) := by ring
    _ ≤ (2 : ℝ) ^ m * A * B := by
      interval_cases m <;> norm_num [Finset.sum_range_succ, Nat.choose] <;>
        ring_nf <;> exact le_rfl

noncomputable def aux_leftBumpOneShortTwo_fourier
    (b : windowBasedBumpFunctions) : ℝ → ℂ :=
  FourierTransform.fourier
    (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))

noncomputable def aux_leftBumpOneShortTwo_amplitude
    (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℂ :=
  fun xi =>
    2 * Real.pi * Complex.I * (xi : ℂ) * aux_leftBumpOneShortTwo_fourier b xi -
      ((2 : ℝ) ^ k : ℂ) * (xi : ℂ) * iteratedDeriv 1 (aux_leftBumpOneShortTwo_fourier b) xi

theorem aux_leftBumpOneShortTwo_fourier_contDiff (b : windowBasedBumpFunctions) :
    ContDiff ℝ 3 (aux_leftBumpOneShortTwo_fourier b) := by
  let Theta : SchwartzMap ℝ ℂ :=
    (thetaTildeSchwartz b).postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  have hTheta : (Theta : ℝ → ℂ) = fun x : ℝ =>
      (windowBasedBumpFunctions.thetaTilde b x : ℂ) := by
    funext x
    simp [Theta, thetaTildeSchwartz_apply, SchwartzMap.postcompCLM_apply]
  have hs : ContDiff ℝ 3 (FourierTransform.fourier Theta : ℝ → ℂ) :=
    (FourierTransform.fourier Theta).smooth 3
  rw [SchwartzMap.fourier_coe, hTheta] at hs
  simpa [aux_leftBumpOneShortTwo_fourier] using hs

theorem aux_leftBumpOneShortTwo_fourier_deriv_bound (b : windowBasedBumpFunctions)
    (m : ℕ) (hm : m ≤ 3) (xi : ℝ) :
    ‖iteratedDeriv m (aux_leftBumpOneShortTwo_fourier b) xi‖ ≤
      (2 : ℝ) ^ 14 * C_uniPair := by
  simpa [aux_leftBumpOneShortTwo_fourier] using thetaTildeFourier_deriv_bound b m hm xi

theorem aux_leftBumpOneShortTwo_fourier_deriv_zero_outside (b : windowBasedBumpFunctions)
    (m : ℕ) (xi : ℝ) (hxi : xi ∉ aux_frequencyAnnulus) :
    iteratedDeriv m (aux_leftBumpOneShortTwo_fourier b) xi = 0 := by
  have hsupp : Function.support (aux_leftBumpOneShortTwo_fourier b) ⊆ aux_frequencyAnnulus := by
    simpa [aux_leftBumpOneShortTwo_fourier] using thetaTildeFourier_support b
  have hclosed : IsClosed aux_frequencyAnnulus := by
    unfold aux_frequencyAnnulus
    exact isClosed_Icc.union isClosed_Icc
  have htsupp : tsupport (aux_leftBumpOneShortTwo_fourier b) ⊆ aux_frequencyAnnulus :=
    closure_minimal hsupp hclosed
  have hderivSupp : Function.support
      (iteratedDeriv m (aux_leftBumpOneShortTwo_fourier b)) ⊆ aux_frequencyAnnulus :=
    (subset_tsupport _).trans
      ((aux_tsupport_iteratedDeriv_subset (aux_leftBumpOneShortTwo_fourier b) m).trans htsupp)
  apply Function.notMem_support.mp
  intro hmem
  exact hxi (hderivSupp hmem)

theorem aux_leftBumpOneShortTwo_amplitude_support (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (aux_leftBumpOneShortTwo_amplitude b k) ⊆ aux_frequencyAnnulus := by
  intro xi hxi
  by_contra hout
  have h0 := aux_leftBumpOneShortTwo_fourier_deriv_zero_outside b 0 xi hout
  have h1 := aux_leftBumpOneShortTwo_fourier_deriv_zero_outside b 1 xi hout
  apply Function.mem_support.mp hxi
  simp only [iteratedDeriv_zero] at h0
  simp [aux_leftBumpOneShortTwo_amplitude, h0, h1]

theorem aux_leftBumpOneShortTwo_amplitude_deriv_zero_outside (b : windowBasedBumpFunctions)
    (k : ℤ) (m : ℕ) (xi : ℝ) (hxi : xi ∉ aux_frequencyAnnulus) :
    iteratedDeriv m (aux_leftBumpOneShortTwo_amplitude b k) xi = 0 := by
  have hclosed : IsClosed aux_frequencyAnnulus := by
    unfold aux_frequencyAnnulus
    exact isClosed_Icc.union isClosed_Icc
  have htsupp : tsupport (aux_leftBumpOneShortTwo_amplitude b k) ⊆ aux_frequencyAnnulus :=
    closure_minimal (aux_leftBumpOneShortTwo_amplitude_support b k) hclosed
  have hderivSupp : Function.support (iteratedDeriv m (aux_leftBumpOneShortTwo_amplitude b k)) ⊆
      aux_frequencyAnnulus :=
    (subset_tsupport _).trans
      ((aux_tsupport_iteratedDeriv_subset (aux_leftBumpOneShortTwo_amplitude b k) m).trans htsupp)
  apply Function.notMem_support.mp
  intro hmem
  exact hxi (hderivSupp hmem)

theorem aux_leftBumpOneShortTwo_linear_deriv (xi : ℝ) :
    deriv (fun y : ℝ => 2 * Real.pi * Complex.I * (y : ℂ)) xi =
      2 * Real.pi * Complex.I := by
  have hcast : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 xi := by
    simpa using
      (hasDerivAt_const xi Complex.ofRealCLM).clm_apply (hasDerivAt_id xi)
  simpa using (hcast.const_mul (2 * Real.pi * Complex.I)).deriv

theorem aux_leftBumpOneShortTwo_linear_deriv_fun :
    deriv (fun y : ℝ => 2 * Real.pi * Complex.I * (y : ℂ)) =
      fun _ : ℝ => 2 * Real.pi * Complex.I := by
  funext x
  exact aux_leftBumpOneShortTwo_linear_deriv x

theorem aux_leftBumpOneShortTwo_annulus_abs_upper {xi : ℝ}
    (hxi : xi ∈ aux_frequencyAnnulus) : |xi| ≤ 1 := by
  rcases hxi with hxi | hxi
  · rw [abs_of_nonpos (by linarith [hxi.2])]
    linarith [hxi.1]
  · rw [abs_of_nonneg (by linarith [hxi.1])]
    exact hxi.2

theorem aux_leftBumpOneShortTwo_linear_iterated_bound (xi : ℝ)
    (hxi : xi ∈ aux_frequencyAnnulus) (m : ℕ) (hm : m ≤ 2) :
    ‖iteratedDeriv m (fun y : ℝ => 2 * Real.pi * Complex.I * (y : ℂ)) xi‖ ≤ 8 := by
  have habs := aux_leftBumpOneShortTwo_annulus_abs_upper hxi
  interval_cases m
  · rw [iteratedDeriv_zero]
    rw [norm_mul, norm_mul, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg Real.pi_pos.le, Complex.norm_I]
    calc
      2 * Real.pi * |xi| ≤ 2 * Real.pi * 1 :=
        mul_le_mul_of_nonneg_left habs (by positivity)
      _ ≤ 2 * 4 * 1 := by
        gcongr
        exact Real.pi_le_four
      _ = 8 := by norm_num
  · rw [iteratedDeriv_one, aux_leftBumpOneShortTwo_linear_deriv]
    rw [norm_mul, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg Real.pi_pos.le, Complex.norm_I]
    nlinarith [Real.pi_le_four]
  · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, aux_leftBumpOneShortTwo_linear_deriv_fun]
    simp

theorem aux_leftBumpOneShortTwo_cast_iterated_bound (xi : ℝ)
    (hxi : xi ∈ aux_frequencyAnnulus) (m : ℕ) (hm : m ≤ 2) :
    ‖iteratedDeriv m (fun y : ℝ => (y : ℂ)) xi‖ ≤ 1 := by
  have habs := aux_leftBumpOneShortTwo_annulus_abs_upper hxi
  interval_cases m
  · rw [iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs]
    exact habs
  · rw [iteratedDeriv_one]
    have hcast : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 xi := by
      simpa using
        (hasDerivAt_const xi Complex.ofRealCLM).clm_apply (hasDerivAt_id xi)
    rw [hcast.deriv]
    norm_num
  · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
    have hcastfun : deriv (fun y : ℝ => (y : ℂ)) = fun _ : ℝ => (1 : ℂ) := by
      funext y
      have hcast : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y := by
        simpa using
          (hasDerivAt_const y Complex.ofRealCLM).clm_apply (hasDerivAt_id y)
      exact hcast.deriv
    rw [hcastfun]
    simp

theorem aux_leftBumpOneShortTwo_fourier_deriv_contDiff (b : windowBasedBumpFunctions) :
    ContDiff ℝ 2 (deriv (aux_leftBumpOneShortTwo_fourier b)) := by
  simpa using (aux_leftBumpOneShortTwo_fourier_contDiff b).deriv'

theorem aux_leftBumpOneShortTwo_fourier_deriv_iterated_bound (b : windowBasedBumpFunctions)
    (m : ℕ) (hm : m ≤ 2) (xi : ℝ) :
    ‖iteratedDeriv m (deriv (aux_leftBumpOneShortTwo_fourier b)) xi‖ ≤
      (2 : ℝ) ^ 14 * C_uniPair := by
  interval_cases m
  · rw [iteratedDeriv_zero, ← iteratedDeriv_one]
    exact aux_leftBumpOneShortTwo_fourier_deriv_bound b 1 (by norm_num) xi
  · rw [iteratedDeriv_one]
    have heq :
        iteratedDeriv 2 (aux_leftBumpOneShortTwo_fourier b) =
          deriv (deriv (aux_leftBumpOneShortTwo_fourier b)) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]
    rw [← heq]
    exact aux_leftBumpOneShortTwo_fourier_deriv_bound b 2 (by norm_num) xi
  · have heq : iteratedDeriv 3 (aux_leftBumpOneShortTwo_fourier b) =
        deriv (deriv (deriv (aux_leftBumpOneShortTwo_fourier b))) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
        show iteratedDeriv 2 (aux_leftBumpOneShortTwo_fourier b) =
            deriv (deriv (aux_leftBumpOneShortTwo_fourier b)) by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
            iteratedDeriv_one]]
    rw [show iteratedDeriv 2 (deriv (aux_leftBumpOneShortTwo_fourier b)) =
        deriv (deriv (deriv (aux_leftBumpOneShortTwo_fourier b))) by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
            iteratedDeriv_one], ← heq]
    exact aux_leftBumpOneShortTwo_fourier_deriv_bound b 3 (by norm_num) xi

theorem aux_leftBumpOneShortTwo_amplitude_contDiff
    (b : windowBasedBumpFunctions) (k : ℤ) :
    ContDiff ℝ 2 (aux_leftBumpOneShortTwo_amplitude b k) := by
  let L : ℝ → ℂ := fun y => 2 * Real.pi * Complex.I * (y : ℂ)
  let X : ℝ → ℂ := fun y => (y : ℂ)
  let H : ℝ → ℂ := aux_leftBumpOneShortTwo_fourier b
  have hL : ContDiff ℝ 2 L := by
    dsimp [L]
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hX : ContDiff ℝ 2 X := by
    dsimp [X]
    exact Complex.ofRealCLM.contDiff
  have hH : ContDiff ℝ 2 H := (aux_leftBumpOneShortTwo_fourier_contDiff b).of_le (by norm_num)
  have hHd : ContDiff ℝ 2 (deriv H) := by
    dsimp [H]
    exact aux_leftBumpOneShortTwo_fourier_deriv_contDiff b
  have hc : ContDiff ℝ 2 (fun _ : ℝ => ((2 : ℂ) ^ k)) := contDiff_const
  have hmain : ContDiff ℝ 2 (fun x => L x * H x -
      ((2 : ℂ) ^ k) * (X x * deriv H x)) :=
    (hL.mul hH).sub (hc.mul (hX.mul hHd))
  have hfun : aux_leftBumpOneShortTwo_amplitude b k = fun x => L x * H x -
      ((2 : ℂ) ^ k) * (X x * deriv H x) := by
    funext x
    dsimp [aux_leftBumpOneShortTwo_amplitude, L, X, H]
    rw [iteratedDeriv_one]
    ring
  rw [hfun]
  exact hmain

theorem aux_leftBumpOneShortTwo_amplitude_deriv_bound
    (b : windowBasedBumpFunctions) (k : ℤ)
    (hk : k ≤ -1) (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m (aux_leftBumpOneShortTwo_amplitude b k) xi‖ ≤
      64 * ((2 : ℝ) ^ 14 * C_uniPair) := by
  let B : ℝ := (2 : ℝ) ^ 14 * C_uniPair
  have hB : 0 ≤ B := by norm_num [B, C_uniPair]
  have hm' : m ≤ 2 := by omega
  by_cases hxi : xi ∈ aux_frequencyAnnulus
  · let L : ℝ → ℂ := fun y => 2 * Real.pi * Complex.I * (y : ℂ)
    let X : ℝ → ℂ := fun y => (y : ℂ)
    let H : ℝ → ℂ := aux_leftBumpOneShortTwo_fourier b
    have hL : ContDiff ℝ 2 L := by
      dsimp [L]
      exact contDiff_const.mul Complex.ofRealCLM.contDiff
    have hX : ContDiff ℝ 2 X := by
      dsimp [X]
      exact Complex.ofRealCLM.contDiff
    have hH : ContDiff ℝ 2 H := (aux_leftBumpOneShortTwo_fourier_contDiff b).of_le (by norm_num)
    have hHd : ContDiff ℝ 2 (deriv H) := by
      dsimp [H]
      exact aux_leftBumpOneShortTwo_fourier_deriv_contDiff b
    have hLbound : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i L xi‖ ≤ 8 := by
      intro i hi
      simpa [L] using aux_leftBumpOneShortTwo_linear_iterated_bound xi hxi i hi
    have hXbound : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i X xi‖ ≤ 1 := by
      intro i hi
      simpa [X] using aux_leftBumpOneShortTwo_cast_iterated_bound xi hxi i hi
    have hHbound : ∀ i : ℕ, i ≤ 2 → ‖iteratedDeriv i H xi‖ ≤ B := by
      intro i hi
      simpa [H, B] using aux_leftBumpOneShortTwo_fourier_deriv_bound b i (by omega) xi
    have hHdbound : ∀ i : ℕ, i ≤ 2 →
        ‖iteratedDeriv i (deriv H) xi‖ ≤ B := by
      intro i hi
      simpa [H, B] using aux_leftBumpOneShortTwo_fourier_deriv_iterated_bound b i hi xi
    have hLH := aux_leftBumpOneShortTwo_product_deriv_bound_at L H hL hH 8 B (by norm_num) hB xi
      hLbound hHbound m hm'
    have hXHd := aux_leftBumpOneShortTwo_product_deriv_bound_at X (deriv H) hX hHd 1 B
      (by norm_num) hB xi hXbound hHdbound m hm'
    have hpow : (2 : ℝ) ^ m ≤ 4 := by
      interval_cases m <;> norm_num
    have hLH' : ‖iteratedDeriv m (L * H) xi‖ ≤ 32 * B := by
      calc
        ‖iteratedDeriv m (L * H) xi‖ ≤ (2 : ℝ) ^ m * 8 * B := hLH
        _ ≤ 4 * 8 * B := by gcongr
        _ = 32 * B := by ring
    have hXHd' : ‖iteratedDeriv m (X * deriv H) xi‖ ≤ 4 * B := by
      calc
        ‖iteratedDeriv m (X * deriv H) xi‖ ≤ (2 : ℝ) ^ m * 1 * B := hXHd
        _ ≤ 4 * 1 * B := by gcongr
        _ = 4 * B := by ring
    have hcknonneg : 0 ≤ (2 : ℝ) ^ k :=
      (zpow_pos (by norm_num) _).le
    have hckle : (2 : ℝ) ^ k ≤ 1 := by
      calc
        (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (0 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 1 := by norm_num
    have hcnorm : ‖((2 : ℂ) ^ k)‖ ≤ 1 := by
      rw [norm_zpow]
      norm_num
      omega
    have hPAt : ContDiffAt ℝ (m : ℕ∞) (L * H) xi := by
      apply ((hL.mul hH).of_le (m := (m : WithTop ℕ∞)) ?_).contDiffAt
      apply WithTop.coe_le_coe.mpr
      exact_mod_cast hm'
    let Q : ℝ → ℂ := fun x => ((2 : ℂ) ^ k) * (X * deriv H) x
    have hQ : ContDiff ℝ 2 Q := by
      dsimp [Q]
      exact contDiff_const.mul (hX.mul hHd)
    have hQAt : ContDiffAt ℝ (m : ℕ∞) Q xi := by
      apply (hQ.of_le
        (m := (m : WithTop ℕ∞)) ?_).contDiffAt
      apply WithTop.coe_le_coe.mpr
      exact_mod_cast hm'
    have hformula : aux_leftBumpOneShortTwo_amplitude b k = fun x => (L * H) x - Q x := by
      funext x
      dsimp [aux_leftBumpOneShortTwo_amplitude, L, X, H, Q]
      rw [iteratedDeriv_one]
      ring
    rw [hformula]
    change ‖iteratedDeriv m ((L * H) - Q) xi‖ ≤ 64 * B
    rw [iteratedDeriv_sub hPAt hQAt]
    have hQderiv : iteratedDeriv m Q xi =
        ((2 : ℂ) ^ k) * iteratedDeriv m (X * deriv H) xi := by
      dsimp [Q]
      rw [iteratedDeriv_const_mul_field]
      rfl
    rw [hQderiv]
    calc
      ‖iteratedDeriv m (L * H) xi -
          ((2 : ℂ) ^ k) * iteratedDeriv m (X * deriv H) xi‖ ≤
          ‖iteratedDeriv m (L * H) xi‖ +
            ‖((2 : ℂ) ^ k) * iteratedDeriv m (X * deriv H) xi‖ :=
        norm_sub_le _ _
      _ = ‖iteratedDeriv m (L * H) xi‖ +
          ‖((2 : ℂ) ^ k)‖ * ‖iteratedDeriv m (X * deriv H) xi‖ := by
        rw [norm_mul]
      _ ≤ 32 * B + 1 * (4 * B) := by gcongr
      _ ≤ 64 * B := by nlinarith
  · rw [aux_leftBumpOneShortTwo_amplitude_deriv_zero_outside b k m xi hxi, norm_zero]
    positivity

theorem aux_leftBumpOneShortTwo_integralFct_plane_diagonal_eq
    (b : windowBasedBumpFunctions) (k : ℤ) (z : ℝ) :
    aux_planeFourier
      (fun v : RealPlane => integralFctKernel
        (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x)
        (WithLp.toLp 2 ![v.1, v.2]))
      (WithLp.toLp 2 ![z, -z]) =
      ∫ t : ℝ in Icc (1 : ℝ) 2,
        aux_leftBumpOneShortTwo_amplitude b k (t * z) *
          aux_leftBumpOneShortTwo_amplitude b k (-(t * z)) *
          ((t⁻¹ : ℝ) : ℂ) := by
  have hcoord : (fun u : EuclideanSpace ℝ (Fin 2) =>
      (integralFctKernel
        (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x)
        (WithLp.toLp 2 ![u 0, u 1]) : ℂ)) =
      fun u => (integralFctKernel
        (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x) u : ℂ) := by
    funext u
    congr 1
  rw [aux_planeFourier, hcoord, integralFctKernel_fourier_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  funext t
  rw [show t * -z = -(t * z) by ring]
  have hpsi (x : ℝ) :
      (tBumpSchwartz (phiFourSchwartz b k) x : ℂ) =
        ((Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k) x : ℝ) : ℂ) := by
    rw [tBumpSchwartz_apply]
    unfold Auto.aux_sd_T
      Auto.aux_T
      Auto.multiplicationOperatorX
    congr 1
  have hpair := phiFour_T_fourier_pair_eq b k (t * z)
  simpa only [aux_leftBumpOneShortTwo_amplitude, aux_leftBumpOneShortTwo_fourier, hpsi] using
    (show
      FourierTransform.fourier
          (fun x : ℝ => ((Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k) x : ℝ) : ℂ)) (t * z) *
        FourierTransform.fourier
          (fun x : ℝ => ((Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k) x : ℝ) : ℂ)) (-(t * z)) *
          ((t⁻¹ : ℝ) : ℂ) =
        (aux_leftBumpOneShortTwo_amplitude b k (t * z) *
          aux_leftBumpOneShortTwo_amplitude b k (-(t * z))) *
          ((t⁻¹ : ℝ) : ℂ) by
        rw [hpair]
        simp only [aux_leftBumpOneShortTwo_amplitude, aux_leftBumpOneShortTwo_fourier]
        push_cast
        rfl)

theorem aux_leftBumpOneShortTwo_base_diagonal_deriv_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (m : ℕ) (hm : m < 3) (z : ℝ) :
    ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => integralFctKernel
          (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
          (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤
      8 * (64 * ((2 : ℝ) ^ 14 * C_uniPair)) ^ 2 := by
  let A : ℝ → ℂ := aux_leftBumpOneShortTwo_amplitude b k
  have hA : ContDiff ℝ 2 A := aux_leftBumpOneShortTwo_amplitude_contDiff b k
  have hC : 0 ≤ 64 * ((2 : ℝ) ^ 14 * C_uniPair) := by
    norm_num [C_uniPair]
  have hAbound : ∀ r : ℕ, r ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv r A x‖ ≤ 64 * ((2 : ℝ) ^ 14 * C_uniPair) := by
    intro r hr x
    simpa [A] using aux_leftBumpOneShortTwo_amplitude_deriv_bound b k hk r (by omega) x
  have hlog := aux_leftBumpOneShort_pair_logIntegral_deriv_bound A hA
    (64 * ((2 : ℝ) ^ 14 * C_uniPair)) hC hAbound m hm z
  have hformula :
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => integralFctKernel
          (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
          (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) =
      fun x => ∫ t : ℝ in Icc (1 : ℝ) 2,
        A (t * x) * A (-(t * x)) * ((t⁻¹ : ℝ) : ℂ) := by
    funext x
    simpa [A] using aux_leftBumpOneShortTwo_integralFct_plane_diagonal_eq b k x
  rw [hformula]
  exact hlog

theorem aux_leftBumpOneShortTwo_normalizer_dominates_diagonal :
    8 * (64 * ((2 : ℝ) ^ 14 * C_uniPair)) ^ 2 ≤
      16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter := by
  have haux : C_thetaPrimitive 2 ≤ C_leftBumpOneShortTwoAuxiliary := by
    unfold C_leftBumpOneShortTwoAuxiliary
    exact le_max_left _ _
  have hprim : C_thetaPrimitive 2 = (2 : ℝ) ^ 16 * C_uniPair := by
    norm_num [C_thetaPrimitive]
  have hmain : 8 * (64 * ((2 : ℝ) ^ 14 * C_uniPair)) ^ 2 ≤
      16 * (C_thetaPrimitive 2) ^ 2 * C_thetaTOffcenter := by
    rw [hprim]
    norm_num [C_thetaTOffcenter, C_uniPair]
  have hprimnonneg : 0 ≤ C_thetaPrimitive 2 := by
    norm_num [C_thetaPrimitive, C_uniPair]
  have hcoff : 0 ≤ C_thetaTOffcenter := by
    norm_num [C_thetaTOffcenter]
  calc
    8 * (64 * ((2 : ℝ) ^ 14 * C_uniPair)) ^ 2 ≤
        16 * (C_thetaPrimitive 2) ^ 2 * C_thetaTOffcenter := hmain
    _ ≤ 16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter := by
      gcongr

theorem aux_leftBumpOneShortTwo_raw_scaled_diagonal_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (m : ℕ) (hm : m < 3) (z : ℝ) :
    ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => Real.rpow 2 ((k : ℝ) / 2) *
          integralFctKernel
            (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
            (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤
      16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter := by
  let p : ℝ := Real.rpow 2 ((k : ℝ) / 2)
  have hp : 0 ≤ p := Real.rpow_nonneg (by norm_num) _
  have hple : p ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have hkreal : (k : ℝ) ≤ -1 := by exact_mod_cast hk
    linarith
  have hbase := aux_leftBumpOneShortTwo_base_diagonal_deriv_bound b k hk m hm z
  have hformula :
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => p * integralFctKernel
          (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
          (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) =
      fun x => (p : ℂ) * aux_planeFourier
        (fun v : RealPlane => integralFctKernel
          (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
          (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x]) := by
    funext x
    rw [aux_leftBumpOneShort_planeFourier_const_mul]
  change ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => p * integralFctKernel
          (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
          (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤ _
  rw [hformula, iteratedDeriv_const_mul_field, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  calc
    p * ‖iteratedDeriv m
        (fun x : ℝ => aux_planeFourier
          (fun v : RealPlane => integralFctKernel
            (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
            (WithLp.toLp 2 ![v.1, v.2]))
          (WithLp.toLp 2 ![x, -x])) z‖ ≤
        p * (8 * (64 * ((2 : ℝ) ^ 14 * C_uniPair)) ^ 2) :=
      mul_le_mul_of_nonneg_left hbase hp
    _ ≤ 1 * (8 * (64 * ((2 : ℝ) ^ 14 * C_uniPair)) ^ 2) := by gcongr
    _ = 8 * (64 * ((2 : ℝ) ^ 14 * C_uniPair)) ^ 2 := by ring
    _ ≤ 16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter :=
      aux_leftBumpOneShortTwo_normalizer_dominates_diagonal

theorem aux_leftBumpOneShortTwo_normalized_diagonal_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (m : ℕ) (hm : m < 3) (z : ℝ) :
    ‖iteratedDeriv m
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane =>
          (16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter)⁻¹ *
            Real.rpow 2 ((k : ℝ) / 2) *
            integralFctKernel
              (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
              (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x])) z‖ ≤ 1 := by
  let D : ℝ := 16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter
  have hD : 0 < D := by
    dsimp [D]
    have haux : 0 < C_leftBumpOneShortTwoAuxiliary := by
      unfold C_leftBumpOneShortTwoAuxiliary
      have hprim : 0 < C_thetaPrimitive 2 := by
        norm_num [C_thetaPrimitive, C_uniPair]
      exact hprim.trans_le (le_max_left _ _)
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos haux))
      (by norm_num [C_thetaTOffcenter])
  have hraw := aux_leftBumpOneShortTwo_raw_scaled_diagonal_bound b k hk m hm z
  have hformula :
      (fun x : ℝ => aux_planeFourier
        (fun v : RealPlane => D⁻¹ *
          (Real.rpow 2 ((k : ℝ) / 2) *
            integralFctKernel
              (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
              (WithLp.toLp 2 ![v.1, v.2])))
        (WithLp.toLp 2 ![x, -x])) =
      fun x => (D⁻¹ : ℂ) * aux_planeFourier
        (fun v : RealPlane =>
          Real.rpow 2 ((k : ℝ) / 2) *
            integralFctKernel
              (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
              (WithLp.toLp 2 ![v.1, v.2]))
        (WithLp.toLp 2 ![x, -x]) := by
    funext x
    rw [aux_leftBumpOneShort_planeFourier_const_mul]
    norm_cast
  have hkernel :
      (fun v : RealPlane =>
        (16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter)⁻¹ *
          Real.rpow 2 ((k : ℝ) / 2) *
          integralFctKernel
            (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
            (WithLp.toLp 2 ![v.1, v.2])) =
      fun v => D⁻¹ *
        (Real.rpow 2 ((k : ℝ) / 2) *
          integralFctKernel
            (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
            (WithLp.toLp 2 ![v.1, v.2])) := by
    funext v
    dsimp [D]
    ring
  rw [hkernel, hformula, iteratedDeriv_const_mul_field, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hD]
  calc
    D⁻¹ * ‖iteratedDeriv m
        (fun x : ℝ => aux_planeFourier
          (fun v : RealPlane =>
            Real.rpow 2 ((k : ℝ) / 2) *
              integralFctKernel
                (fun y : ℝ => tBumpSchwartz (phiFourSchwartz b k) y)
                (WithLp.toLp 2 ![v.1, v.2]))
          (WithLp.toLp 2 ![x, -x])) z‖ ≤ D⁻¹ * D :=
      mul_le_mul_of_nonneg_left (by simpa [D] using hraw)
        (inv_nonneg.mpr hD.le)
    _ = 1 := by field_simp [ne_of_gt hD]



theorem aux_leftBumpOneShortTwo_auxiliary_nonneg :
    0 ≤ C_leftBumpOneShortTwoAuxiliary := by
  unfold C_leftBumpOneShortTwoAuxiliary
  exact le_max_of_le_left (by norm_num [C_thetaPrimitive, C_uniPair])

theorem aux_leftBumpOneShortTwo_auxiliary_pos :
    0 < C_leftBumpOneShortTwoAuxiliary := by
  unfold C_leftBumpOneShortTwoAuxiliary
  have hprim : 0 < C_thetaPrimitive 2 := by
    norm_num [C_thetaPrimitive, C_uniPair]
  exact hprim.trans_le (le_max_left _ _)

noncomputable def aux_leftBumpOneShortTwo_normalizer : ℝ :=
  16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter

theorem aux_leftBumpOneShortTwo_normalizer_pos :
    0 < aux_leftBumpOneShortTwo_normalizer := by
  unfold aux_leftBumpOneShortTwo_normalizer
  exact mul_pos (mul_pos (by norm_num)
    (sq_pos_of_pos aux_leftBumpOneShortTwo_auxiliary_pos))
    (by norm_num [C_thetaTOffcenter])

theorem aux_leftBumpOneShortTwo_tBump_eq_aux_T (phi : SchwartzMap ℝ ℝ) :
    (fun x : ℝ => tBumpSchwartz phi x) =
      Auto.aux_T (fun x : ℝ => phi x) := by
  funext x
  rw [tBumpSchwartz_apply]
  unfold Auto.aux_sd_T
    Auto.aux_T
    Auto.multiplicationOperatorX
  congr 1

theorem aux_leftBumpOneShortTwo_rescaled_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (t u : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2)
    (hTformula : ∀ x : ℝ,
      Auto.aux_T (windowBasedBumpFunctions.phiFour b k) x =
        (2 : ℝ) ^ k *
          (Auto.aux_T
            (windowBasedBumpFunctions.thetaTilde b) (x - (2 : ℝ) ^ (-k)) +
            (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b
              (x - (2 : ℝ) ^ (-k)))) :
    |Auto.aux_bf_realRescaled t
        (Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k)) u| ≤
      4 * C_leftBumpOneShortTwoAuxiliary *
        bracketBump (u - t * (2 : ℝ) ^ (-k)) ^ 2 := by
  let C : ℝ := C_leftBumpOneShortTwoAuxiliary
  let x : ℝ := u - t * (2 : ℝ) ^ (-k)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
  have hp : 0 ≤ (2 : ℝ) ^ k := (zpow_pos (by norm_num) _).le
  have hpinv : 0 ≤ (2 : ℝ) ^ (-k) := (zpow_pos (by norm_num) _).le
  have hC : 0 ≤ C := aux_leftBumpOneShortTwo_auxiliary_nonneg
  have hprimle : C_thetaPrimitive 2 ≤ C := by
    dsimp [C, C_leftBumpOneShortTwoAuxiliary]
    exact le_max_left _ _
  have hthetale : C_thetaDecay 2 ≤ C := by
    dsimp [C, C_leftBumpOneShortTwoAuxiliary]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have harg : t⁻¹ * u - (2 : ℝ) ^ (-k) = t⁻¹ * x := by
    dsimp [x]
    field_simp [ne_of_gt htpos]
  have hbr : bracketBump (t⁻¹ * x) ≤ t * bracketBump x :=
    aux_leftBumpOneShort_bracket_inv_mul_le t x ht.1
  have hbrsq : bracketBump (t⁻¹ * x) ^ 2 ≤ (t * bracketBump x) ^ 2 :=
    pow_le_pow_left₀ (by rw [bracketBump]; positivity) hbr 2
  have htilde : |Auto.aux_T
      (windowBasedBumpFunctions.thetaTilde b) (t⁻¹ * x)| ≤
      C * (t * bracketBump x) ^ 2 := by
    have hbase := (thetaPrimitive b 2 (by omega) (by norm_num [N_uniPair])).2.2.2
      (t⁻¹ * x)
    calc
      |Auto.aux_T
          (windowBasedBumpFunctions.thetaTilde b) (t⁻¹ * x)| ≤
          C_thetaPrimitive 2 * bracketBump (t⁻¹ * x) ^ 2 := hbase
      _ ≤ C * bracketBump (t⁻¹ * x) ^ 2 :=
        mul_le_mul_of_nonneg_right hprimle (by positivity)
      _ ≤ C * (t * bracketBump x) ^ 2 :=
        mul_le_mul_of_nonneg_left hbrsq hC
  have htheta : |windowBasedBumpFunctions.theta b (t⁻¹ * x)| ≤
      C * (t * bracketBump x) ^ 2 := by
    have hbase := thetaDecay b 2 (by omega) (by omega) (t⁻¹ * x)
    calc
      |windowBasedBumpFunctions.theta b (t⁻¹ * x)| ≤
          C_thetaDecay 2 * bracketBump (t⁻¹ * x) ^ 2 := hbase
      _ ≤ C * bracketBump (t⁻¹ * x) ^ 2 :=
        mul_le_mul_of_nonneg_right hthetale (by positivity)
      _ ≤ C * (t * bracketBump x) ^ 2 :=
        mul_le_mul_of_nonneg_left hbrsq hC
  have hsum : |Auto.aux_T
      (windowBasedBumpFunctions.thetaTilde b) (t⁻¹ * x) +
      (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b (t⁻¹ * x)| ≤
      (1 + (2 : ℝ) ^ (-k)) * (C * (t * bracketBump x) ^ 2) := by
    calc
      |Auto.aux_T
          (windowBasedBumpFunctions.thetaTilde b) (t⁻¹ * x) +
          (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b (t⁻¹ * x)| ≤
          |Auto.aux_T
            (windowBasedBumpFunctions.thetaTilde b) (t⁻¹ * x)| +
            |(2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b (t⁻¹ * x)| :=
        abs_add_le _ _
      _ = |Auto.aux_T
            (windowBasedBumpFunctions.thetaTilde b) (t⁻¹ * x)| +
          (2 : ℝ) ^ (-k) * |windowBasedBumpFunctions.theta b (t⁻¹ * x)| := by
        rw [abs_mul, abs_of_nonneg hpinv]
      _ ≤ C * (t * bracketBump x) ^ 2 +
          (2 : ℝ) ^ (-k) * (C * (t * bracketBump x) ^ 2) := by
        gcongr
      _ = (1 + (2 : ℝ) ^ (-k)) * (C * (t * bracketBump x) ^ 2) := by ring
  have hcancel : (2 : ℝ) ^ k * (2 : ℝ) ^ (-k) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hpowhalf : (2 : ℝ) ^ k ≤ (1 / 2 : ℝ) := by
    calc
      (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) hk
      _ = (1 / 2 : ℝ) := by norm_num [zpow_neg]
  have hpt : (2 : ℝ) ^ k * t ≤ 1 := by
    calc
      (2 : ℝ) ^ k * t ≤ (1 / 2 : ℝ) * t :=
        mul_le_mul_of_nonneg_right hpowhalf htpos.le
      _ ≤ 1 := by nlinarith [ht.2]
  have hcoeff : (2 : ℝ) ^ k * t + t ≤ 4 := by
    nlinarith [hpt, ht.2]
  change |t⁻¹ * Auto.aux_T
      (windowBasedBumpFunctions.phiFour b k) (t⁻¹ * u)| ≤
      4 * C * bracketBump x ^ 2
  rw [hTformula, harg, abs_mul, abs_of_nonneg htinv,
    abs_mul, abs_of_nonneg hp]
  calc
    t⁻¹ * ((2 : ℝ) ^ k *
        |Auto.aux_T
          (windowBasedBumpFunctions.thetaTilde b) (t⁻¹ * x) +
          (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b (t⁻¹ * x)|) ≤
        t⁻¹ * ((2 : ℝ) ^ k *
          ((1 + (2 : ℝ) ^ (-k)) * (C * (t * bracketBump x) ^ 2))) := by
      gcongr
    _ = ((2 : ℝ) ^ k * t + t) * C * bracketBump x ^ 2 := by
      have hfac : (2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (-k)) =
          (2 : ℝ) ^ k + 1 := by
        calc
          (2 : ℝ) ^ k * (1 + (2 : ℝ) ^ (-k)) =
              (2 : ℝ) ^ k + (2 : ℝ) ^ k * (2 : ℝ) ^ (-k) := by ring
          _ = (2 : ℝ) ^ k + 1 := by rw [hcancel]
      field_simp [ne_of_gt htpos]
      rw [hfac]
      ring
    _ ≤ 4 * C * bracketBump x ^ 2 := by
      have hB : 0 ≤ bracketBump x ^ 2 := by positivity
      have hmain : ((2 : ℝ) ^ k * t + t) * (C * bracketBump x ^ 2) ≤
          4 * (C * bracketBump x ^ 2) :=
        mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hC hB)
      simpa [mul_assoc] using hmain

/-- Product estimate for the short-two logarithmic integrand. -/
theorem aux_leftBumpOneShortTwo_integrand_bound
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) (v : RealPlane)
    (hTformula : ∀ x : ℝ,
      Auto.aux_T (windowBasedBumpFunctions.phiFour b k) x =
        (2 : ℝ) ^ k *
          (Auto.aux_T
            (windowBasedBumpFunctions.thetaTilde b) (x - (2 : ℝ) ^ (-k)) +
            (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b
              (x - (2 : ℝ) ^ (-k)))) :
    |Auto.aux_bf_realRescaled t
        (Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k)) v.1 *
      Auto.aux_bf_realRescaled t
        (Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k)) v.2 * t⁻¹| ≤
      (4 * C_leftBumpOneShortTwoAuxiliary) ^ 2 *
        (bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 *
          bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr htpos.le
  have htinvle : t⁻¹ ≤ 1 := (inv_le_one₀ htpos).2 ht.1
  have h0 := aux_leftBumpOneShortTwo_rescaled_bound b k hk t v.1 ht hTformula
  have h1 := aux_leftBumpOneShortTwo_rescaled_bound b k hk t v.2 ht hTformula
  have hA : 0 ≤ 4 * C_leftBumpOneShortTwoAuxiliary :=
    mul_nonneg (by norm_num) aux_leftBumpOneShortTwo_auxiliary_nonneg
  have hB0 : 0 ≤ bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg htinv]
  calc
    |Auto.aux_bf_realRescaled t
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k)) v.1| *
        |Auto.aux_bf_realRescaled t
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k)) v.2| * t⁻¹ ≤
        ((4 * C_leftBumpOneShortTwoAuxiliary) *
          bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2) *
          ((4 * C_leftBumpOneShortTwoAuxiliary) *
            bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) * t⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ htinv
          exact mul_le_mul h0 h1 (abs_nonneg _) (mul_nonneg hA hB0)
    _ ≤ ((4 * C_leftBumpOneShortTwoAuxiliary) *
          bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2) *
          ((4 * C_leftBumpOneShortTwoAuxiliary) *
            bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) * 1 := by
          apply mul_le_mul_of_nonneg_left htinvle
          positivity
    _ = (4 * C_leftBumpOneShortTwoAuxiliary) ^ 2 *
        (bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 *
          bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2) := by ring

/--
The fully normalized physical Whitney decay for the short-two kernel,
conditional only on the public logarithmic-derivative formula for `phiFour`.
-/
theorem aux_leftBumpOneShortTwo_kernel_decay
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (v : RealPlane)
    (hTformula : ∀ x : ℝ,
      Auto.aux_T (windowBasedBumpFunctions.phiFour b k) x =
        (2 : ℝ) ^ k *
          (Auto.aux_T
            (windowBasedBumpFunctions.thetaTilde b) (x - (2 : ℝ) ^ (-k)) +
            (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b
              (x - (2 : ℝ) ^ (-k)))) :
    |Real.rpow 2 ((k : ℝ) / 2) *
      integralFctKernel
        (Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k))
        (WithLp.toLp 2 ![v.1, v.2])| ≤
      (16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter) *
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
  let A : ℝ := 4 * C_leftBumpOneShortTwoAuxiliary
  let B : ℝ → ℝ := fun t =>
    bracketBump (v.1 - t * (2 : ℝ) ^ (-k)) ^ 2 *
      bracketBump (v.2 - t * (2 : ℝ) ^ (-k)) ^ 2
  have hA2 : 0 ≤ A ^ 2 := sq_nonneg _
  have hBcont : Continuous B := by
    dsimp [B]
    have h0 : Continuous (fun t : ℝ =>
        1 + |v.1 - t * (2 : ℝ) ^ (-k)|) := by fun_prop
    have h1 : Continuous (fun t : ℝ =>
        1 + |v.2 - t * (2 : ℝ) ^ (-k)|) := by fun_prop
    have h0ne : ∀ t : ℝ, 1 + |v.1 - t * (2 : ℝ) ^ (-k)| ≠ 0 := by
      intro t
      positivity
    have h1ne : ∀ t : ℝ, 1 + |v.2 - t * (2 : ℝ) ^ (-k)| ≠ 0 := by
      intro t
      positivity
    change Continuous (fun t : ℝ =>
      (1 + |v.1 - t * (2 : ℝ) ^ (-k)|)⁻¹ ^ 2 *
        (1 + |v.2 - t * (2 : ℝ) ^ (-k)|)⁻¹ ^ 2)
    exact ((h0.inv₀ h0ne).pow 2).mul ((h1.inv₀ h1ne).pow 2)
  have hBint : IntegrableOn B (Set.Icc (1 : ℝ) 2) := hBcont.integrableOn_Icc
  have hint : ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
      |Auto.aux_bf_realRescaled t
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k)) v.1 *
        Auto.aux_bf_realRescaled t
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k)) v.2 * t⁻¹| ≤
      A ^ 2 * ∫ t : ℝ in Set.Icc (1 : ℝ) 2, B t := by
    calc
      ∫ t : ℝ in Set.Icc (1 : ℝ) 2,
          |Auto.aux_bf_realRescaled t
              (Auto.aux_T
                (windowBasedBumpFunctions.phiFour b k)) v.1 *
            Auto.aux_bf_realRescaled t
              (Auto.aux_T
                (windowBasedBumpFunctions.phiFour b k)) v.2 * t⁻¹| ≤
          ∫ t : ℝ in Set.Icc (1 : ℝ) 2, A ^ 2 * B t := by
            apply MeasureTheory.setIntegral_mono_of_nonneg
            · intro t ht
              exact abs_nonneg _
            · intro t ht
              simpa only [A, B] using
                aux_leftBumpOneShortTwo_integrand_bound b k hk t ht v hTformula
            · exact hBint.const_mul _
      _ = A ^ 2 * ∫ t : ℝ in Set.Icc (1 : ℝ) 2, B t := by
        rw [integral_const_mul]
  have hc : 0 ≤ Real.rpow 2 ((k : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hoff := thetaTOffcenter k hk v.1 v.2
  change |Real.rpow 2 ((k : ℝ) / 2) *
      ∫ t : ℝ in Set.Icc 1 2,
        Auto.aux_bf_realRescaled t
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k)) v.1 *
        Auto.aux_bf_realRescaled t
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k)) v.2 * t⁻¹| ≤ _
  calc
    |Real.rpow 2 ((k : ℝ) / 2) *
        ∫ t : ℝ in Set.Icc 1 2,
          Auto.aux_bf_realRescaled t
            (Auto.aux_T
              (windowBasedBumpFunctions.phiFour b k)) v.1 *
          Auto.aux_bf_realRescaled t
            (Auto.aux_T
              (windowBasedBumpFunctions.phiFour b k)) v.2 * t⁻¹| =
        Real.rpow 2 ((k : ℝ) / 2) *
          |∫ t : ℝ in Set.Icc 1 2,
            Auto.aux_bf_realRescaled t
              (Auto.aux_T
                (windowBasedBumpFunctions.phiFour b k)) v.1 *
            Auto.aux_bf_realRescaled t
              (Auto.aux_T
                (windowBasedBumpFunctions.phiFour b k)) v.2 * t⁻¹| := by
              rw [abs_mul, abs_of_nonneg hc]
    _ ≤ Real.rpow 2 ((k : ℝ) / 2) *
        ∫ t : ℝ in Set.Icc 1 2,
          |Auto.aux_bf_realRescaled t
              (Auto.aux_T
                (windowBasedBumpFunctions.phiFour b k)) v.1 *
            Auto.aux_bf_realRescaled t
              (Auto.aux_T
                (windowBasedBumpFunctions.phiFour b k)) v.2 * t⁻¹| := by
              exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hc
    _ ≤ Real.rpow 2 ((k : ℝ) / 2) *
        (A ^ 2 * ∫ t : ℝ in Set.Icc 1 2, B t) := by
          exact mul_le_mul_of_nonneg_left hint hc
    _ = 16 * C_leftBumpOneShortTwoAuxiliary ^ 2 *
        (Real.rpow 2 ((k : ℝ) / 2) *
          ∫ t : ℝ in Set.Icc 1 2, B t) := by
          dsimp [A]
          ring
    _ ≤ 16 * C_leftBumpOneShortTwoAuxiliary ^ 2 *
        (C_thetaTOffcenter *
          (Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
              Real.rpow (bracketBump v.2) (3 / 2 : ℝ) +
            Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) *
              Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [B] using hoff
          · positivity
    _ ≤ 16 * C_leftBumpOneShortTwoAuxiliary ^ 2 *
        (C_thetaTOffcenter * ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2)) := by
          apply mul_le_mul_of_nonneg_left
          · exact aux_leftBumpOneShort_offcenter_rhs_le_whitney v
          positivity
    _ = (16 * C_leftBumpOneShortTwoAuxiliary ^ 2 * C_thetaTOffcenter) *
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by ring

theorem aux_leftBumpOneShortTwo_normalized_decay
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (v : RealPlane)
    (hTformula : ∀ x : ℝ,
      Auto.aux_T (windowBasedBumpFunctions.phiFour b k) x =
        (2 : ℝ) ^ k *
          (Auto.aux_T
            (windowBasedBumpFunctions.thetaTilde b) (x - (2 : ℝ) ^ (-k)) +
            (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b
              (x - (2 : ℝ) ^ (-k)))) :
    |(aux_leftBumpOneShortTwo_normalizer)⁻¹ *
      Real.rpow 2 ((k : ℝ) / 2) *
      integralFctKernel
        (Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k))
        (WithLp.toLp 2 ![v.1, v.2])| ≤
      ∑ u : Fin 2,
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
  let D : ℝ := aux_leftBumpOneShortTwo_normalizer
  let S : ℝ := ∑ u : Fin 2,
    scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
      scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2)
  have hD : 0 < D := aux_leftBumpOneShortTwo_normalizer_pos
  have hraw : |Real.rpow 2 ((k : ℝ) / 2) *
      integralFctKernel
        (Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k))
        (WithLp.toLp 2 ![v.1, v.2])| ≤ D * S := by
    dsimp [D, S, aux_leftBumpOneShortTwo_normalizer]
    exact aux_leftBumpOneShortTwo_kernel_decay b k hk v hTformula
  change |D⁻¹ * Real.rpow 2 ((k : ℝ) / 2) *
      integralFctKernel
        (Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k))
        (WithLp.toLp 2 ![v.1, v.2])| ≤ S
  calc
    |D⁻¹ * Real.rpow 2 ((k : ℝ) / 2) *
        integralFctKernel
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k))
          (WithLp.toLp 2 ![v.1, v.2])| =
        |D⁻¹ * (Real.rpow 2 ((k : ℝ) / 2) *
          integralFctKernel
            (Auto.aux_T
              (windowBasedBumpFunctions.phiFour b k))
            (WithLp.toLp 2 ![v.1, v.2]))| := by
      rw [mul_assoc]
    _ = D⁻¹ * |Real.rpow 2 ((k : ℝ) / 2) *
        integralFctKernel
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k))
          (WithLp.toLp 2 ![v.1, v.2])| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hD)]
    _ ≤ D⁻¹ * (D * S) :=
      mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hD.le)
    _ = S := by field_simp [ne_of_gt hD]

theorem aux_leftBumpOneShortTwo_tPhiFourSchwartz_support
    (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ => (tBumpSchwartz (phiFourSchwartz b k) x : ℂ))) ⊆
        Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
  intro xi hxi
  have heq : (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x) =
      Auto.aux_T
        (windowBasedBumpFunctions.phiFour b k) := by
    rw [aux_leftBumpOneShortTwo_tBump_eq_aux_T]
    congr 1
  have hraw : xi ∈ Function.support (FourierTransform.fourier
      (fun x : ℝ =>
        ((Auto.aux_T
          (fun y : ℝ => (windowBasedBumpFunctions.phiFour b k y : ℝ)) x : ℝ) : ℂ))) := by
    simpa only [heq] using hxi
  exact (thetaPrimitive b 2 (by omega) (by norm_num [N_uniPair])).1.2
    ((phiFourSupport b k).2 hraw)

/--
Full short-two Whitney packaging, conditional only on nonvanishing and the
same phase-cancelled diagonal Fourier derivative estimate as the blueprint.
-/
noncomputable def aux_leftBumpOneShortTwo_whitneyData
    (b : windowBasedBumpFunctions) (k : ℤ) (hk : k ≤ -1)
    (hTformula : ∀ x : ℝ,
      Auto.aux_T (windowBasedBumpFunctions.phiFour b k) x =
        (2 : ℝ) ^ k *
          (Auto.aux_T
            (windowBasedBumpFunctions.thetaTilde b) (x - (2 : ℝ) ^ (-k)) +
            (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b
              (x - (2 : ℝ) ^ (-k))))
    (hnonzero : (fun v : RealPlane =>
      (aux_leftBumpOneShortTwo_normalizer)⁻¹ *
        Real.rpow 2 ((k : ℝ) / 2) *
        integralFctKernel
          (Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k))
          (WithLp.toLp 2 ![v.1, v.2])) ≠ 0)
    (hdiag : ∀ m : ℕ, m < 3 → ∀ xi : ℝ,
      ‖iteratedDeriv m
        (fun z : ℝ => aux_planeFourier
          (fun v : RealPlane =>
            (aux_leftBumpOneShortTwo_normalizer)⁻¹ *
              Real.rpow 2 ((k : ℝ) / 2) *
              integralFctKernel
                (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x)
                (WithLp.toLp 2 ![v.1, v.2]))
          (WithLp.toLp 2 ![z, -z])) xi‖ ≤ 1) :
    WhitneyKernelData := by
  let psi : SchwartzMap ℝ ℝ := tBumpSchwartz (phiFourSchwartz b k)
  let c : ℝ := (aux_leftBumpOneShortTwo_normalizer)⁻¹ *
    Real.rpow 2 ((k : ℝ) / 2)
  have hann : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 2) := by
    dsimp [psi]
    exact aux_leftBumpOneShortTwo_tPhiFourSchwartz_support b k
  have hband : Function.support (FourierTransform.fourier
      (fun x : ℝ => (psi x : ℂ))) ⊆
      Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1 := by
    intro xi hxi
    have heq : (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x) =
        Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k) := by
      rw [aux_leftBumpOneShortTwo_tBump_eq_aux_T]
      congr 1
    have hraw : xi ∈ Function.support (FourierTransform.fourier
        (fun x : ℝ =>
          ((Auto.aux_T
            (fun y : ℝ => (windowBasedBumpFunctions.phiFour b k y : ℝ)) x : ℝ) : ℂ))) := by
      simpa only [psi, heq] using hxi
    simpa [aux_frequencyAnnulus] using (phiFourSupport b k).2 hraw
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (inv_nonneg.mpr aux_leftBumpOneShortTwo_normalizer_pos.le)
      (Real.rpow_nonneg (by norm_num) _)
  have hfourier : Function.support (aux_planeFourier
      (fun v : RealPlane => c * integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2]))) ⊆
      {v : EuclideanSpace ℝ (Fin 2) |
        v 0 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3) ∧
        v 1 ∈ Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3)} :=
    aux_leftBumpOneShort_integralFct_plane_fourier_support_smul psi hband c
  have hdecay : ∀ v : RealPlane,
      |c * integralFctKernel (fun x : ℝ => psi x)
        (WithLp.toLp 2 ![v.1, v.2])| ≤
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
    intro v
    have heq : (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x) =
        Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k) := by
      rw [aux_leftBumpOneShortTwo_tBump_eq_aux_T]
      congr 1
    simpa only [c, psi, heq] using
      aux_leftBumpOneShortTwo_normalized_decay b k hk v hTformula
  apply aux_leftBumpOneShort_integralFctWhitneyData psi hann hband c hc
  · have heq : (fun x : ℝ => tBumpSchwartz (phiFourSchwartz b k) x) =
        Auto.aux_T
          (windowBasedBumpFunctions.phiFour b k) := by
        rw [aux_leftBumpOneShortTwo_tBump_eq_aux_T]
        congr 1
    simpa only [c, psi, heq] using hnonzero
  · exact hfourier
  · simpa only [c, psi] using hdiag
  · exact hdecay


/--
**Lemma.**

Let $\gamma=\frac12$. For every $k\le-1$ and every strictly increasing sequence of integers
$(k_j)_{j\in[J)}$,

$$
\sum_{j\in[J)}2^{(1-\gamma)k}\int_1^2
\|A_{2^{k_j}t}(T\varphi_{4,k})\|_2^2\,\tfrac{dt}{t}
\le C_{\text{lem:leftbump1\_short2}}J^{\alpha(n)},
$$

where, with

$$
C=\max\bigl(C_{\text{lem:theta\_prim},2},C_{\text{lem:theta\_decay},2},C_{\text{lem:theta\_decay},3}
\bigr),
$$

we have

$$
C_{\text{lem:leftbump1\_short2}}
=2^4C_{\text{induct positive terms - reduction variant, Whitney}}
C_{\text{lem:thetat\_offcenter}}C^2.
$$

See also `Auto.leftBumpOneShortTwo`,
`Auto.thetaPrimitive`,
`Auto.thetaDecay`,
`Auto.inductPositiveTermsReductionWhitney`,
`Auto.thetaTOffcenter`.
-/
theorem leftBumpOneShortTwo {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (k : ℤ) (hk : k ≤ -1) (J : ℕ) (hJ : 0 < J)
    (ell : aux_dyadicChain J) :
    ∑ j : Fin J,
      ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)) *
        ∫⁻ t in Set.Icc (1 : ℝ) 2,
          ENNReal.ofReal t⁻¹ *
            eLpNorm
              (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc) * t)
                (Auto.aux_T (windowBasedBumpFunctions.phiFour b k))
                (fun i x ↦ f.1 i x))
              2 volume ^ 2 ≤
      ENNReal.ofReal (C_leftBumpOneShortTwo n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  cases n with
  | zero => omega
  | succ d =>
    have hd : 1 ≤ d := by omega
    obtain ⟨a, ha, ha_restrict⟩ := aux_mainAuxOne_extend_dyadic_chain J hJ ell
    let D : ℝ := aux_leftBumpOneShortTwo_normalizer
    let P : ℝ := Real.rpow 2 ((k : ℝ) / 2)
    let c : ℝ := D⁻¹ * P
    let psi : SchwartzMap ℝ ℝ := tBumpSchwartz (phiFourSchwartz b k)
    let E : Fin J → ℝ≥0∞ := fun j =>
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ENNReal.ofReal t⁻¹ *
          eLpNorm
            (twistedAverageAtScale ((2 : ℝ) ^ (ell.1 j.castSucc) * t)
              (Auto.aux_T
                (windowBasedBumpFunctions.phiFour b k))
              (fun i x => f.1 i x))
            2 volume ^ 2
    have hD : 0 < D := by
      simpa only [D] using aux_leftBumpOneShortTwo_normalizer_pos
    have hP : 0 < P := by
      dsimp [P]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hc : 0 < c := mul_pos (inv_pos.mpr hD) hP
    have hPc : D * c = P := by
      dsimp [c]
      field_simp [hD.ne']
    have henergy : ∀ j : Fin J,
        E j = ENNReal.ofReal
          (prismForm (d + 1) 1 (by omega) (by omega)
            (aux_leftBumpOneShort_integralM (a (j : ℤ)) psi)
            (fun i x =>
              Auto.aux_aToLambda.transformedFunctions f.1 i x)) := by
      intro j
      dsimp [E]
      rw [← ha_restrict j]
      simpa only [psi, aux_leftBumpOneShortTwo_tBump_eq_aux_T,
        phiFourSchwartz_apply] using
        aux_leftBumpOneShort_continuous_aToLambda_integralFct d
          (a (j : ℤ)) (ha (j : ℤ)).1 psi f.1
    change ∑ j : Fin J, ENNReal.ofReal P * E j ≤
      ENNReal.ofReal (C_leftBumpOneShortTwo (d + 1)) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1))
    let K : RealPlane → ℝ := fun v => c *
      integralFctKernel (fun x => psi x) (WithLp.toLp 2 ![v.1, v.2])
    by_cases hzero : K = 0
    · have hsum := aux_leftBumpOneShort_zero_energy_sum c hc psi hzero a f P E henergy
      rw [hsum]
      exact bot_le
    · have hTformula : ∀ x : ℝ,
        Auto.aux_T
            (windowBasedBumpFunctions.phiFour b k) x =
          (2 : ℝ) ^ k *
            (Auto.aux_T
              (windowBasedBumpFunctions.thetaTilde b) (x - (2 : ℝ) ^ (-k)) +
              (2 : ℝ) ^ (-k) * windowBasedBumpFunctions.theta b
                (x - (2 : ℝ) ^ (-k))) := by
          intro x
          exact congrFun (phiFour_T_eq b k) x
      let Psi : WhitneyKernelData := aux_leftBumpOneShortTwo_whitneyData b k hk hTformula
        (by simpa only [K, c, D, P, psi, aux_leftBumpOneShortTwo_tBump_eq_aux_T,
          phiFourSchwartz_apply] using hzero)
        (fun m hm xi => by
          simpa only [D, P, aux_leftBumpOneShortTwo_normalizer] using
            aux_leftBumpOneShortTwo_normalized_diagonal_bound b k hk m hm xi)
      have hPsi : Psi.kernel = fun v : RealPlane => c *
          integralFctKernel (fun x => psi x) (WithLp.toLp 2 ![v.1, v.2]) := by
        dsimp [Psi]
        rfl
      have hmain := aux_leftBumpOneShort_scaled_integralM_prefix hd D P c hD hc hPc
        psi a ha f hJ b.phi0 b.phi1 b.universalPair Psi hPsi E henergy
      have hconst : D * C_inductPositiveTermsReductionWhitney (d + 1) =
          C_leftBumpOneShortTwo (d + 1) := by
        dsimp [D, aux_leftBumpOneShortTwo_normalizer]
        unfold C_leftBumpOneShortTwo
        ring
      calc
        ∑ j : Fin J, ENNReal.ofReal P * E j ≤
            ENNReal.ofReal (D * C_inductPositiveTermsReductionWhitney (d + 1)) *
              ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := hmain
        _ = ENNReal.ofReal (C_leftBumpOneShortTwo (d + 1)) *
              ENNReal.ofReal ((J : ℝ) ^ variationExponent (d + 1)) := by
              rw [hconst]

/--
**Lemma (constant $C_{\text{lem:leftbump1\_short2}}$).**

$$
C_{\text{lem:leftbump1\_short2}}
<2^{630}.
$$

See also `Auto.leftBumpOneShortTwo`.
-/
theorem constantLeftBumpOneShortTwo {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneShortTwo n < (2 : ℝ) ^ 630 := by
  have hWhitney : C_inductPositiveTermsReductionWhitney n <
      (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
    unfold C_inductPositiveTermsReductionWhitney
    calc
      11 * C_inductPositiveTermsReductionWhitneyGap n <
          11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553) :=
        mul_lt_mul_of_pos_left (constantWhitneyGapReduction hn) (by norm_num)
      _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 4 * (2 : ℝ) ^ 553) := by
        norm_num
        set_option exponentiation.threshold 1000 in
          ring
      _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
        rw [← pow_add]
  have hprim : C_thetaPrimitive 2 ≤ (2 : ℝ) ^ 31 := by
    exact (constantThetaPrimitive 2 (by norm_num) (by norm_num [N_uniPair])).2
  have hdecayTwo : C_thetaDecay 2 ≤ (2 : ℝ) ^ 21 := by
    simpa using constantThetaDecay 2 (by norm_num) (by norm_num)
  have hdecayThree : C_thetaDecay 3 ≤ (2 : ℝ) ^ 23 := by
    simpa using constantThetaDecay 3 (by norm_num) (by norm_num)
  have hdecayTwo' : C_thetaDecay 2 ≤ (2 : ℝ) ^ 31 :=
    hdecayTwo.trans (by norm_num)
  have hdecayThree' : C_thetaDecay 3 ≤ (2 : ℝ) ^ 31 :=
    hdecayThree.trans (by norm_num)
  have haux : C_leftBumpOneShortTwoAuxiliary ≤ (2 : ℝ) ^ 31 := by
    unfold C_leftBumpOneShortTwoAuxiliary
    exact max_le hprim (max_le hdecayTwo' hdecayThree')
  have hauxpos : 0 < C_leftBumpOneShortTwoAuxiliary := by
    unfold C_leftBumpOneShortTwoAuxiliary
    have hprimpos : 0 < C_thetaPrimitive 2 := by
      norm_num [C_thetaPrimitive, C_uniPair]
    exact hprimpos.trans_le (le_max_left _ _)
  have hfacpos : 0 < (2 : ℝ) ^ 4 * C_thetaTOffcenter *
      C_leftBumpOneShortTwoAuxiliary ^ 2 := by
    exact mul_pos
      (mul_pos (by positivity) (by norm_num [C_thetaTOffcenter]))
      (sq_pos_of_pos hauxpos)
  unfold C_leftBumpOneShortTwo
  calc
    (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitney n * C_thetaTOffcenter *
        C_leftBumpOneShortTwoAuxiliary ^ 2 =
        ((2 : ℝ) ^ 4 * C_thetaTOffcenter * C_leftBumpOneShortTwoAuxiliary ^ 2) *
          C_inductPositiveTermsReductionWhitney n := by ring
    _ < ((2 : ℝ) ^ 4 * C_thetaTOffcenter * C_leftBumpOneShortTwoAuxiliary ^ 2) *
        ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) :=
      mul_lt_mul_of_pos_left hWhitney hfacpos
    _ ≤ ((2 : ℝ) ^ 4 * C_thetaTOffcenter * ((2 : ℝ) ^ 31) ^ 2) *
        ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) := by
      gcongr
      norm_num [C_thetaTOffcenter]
    _ = (185801 / 262144 : ℝ) * (2 : ℝ) ^ 630 := by
      have hpow : (2 : ℝ) ^ 4 * ((2 : ℝ) ^ 31) ^ 2 * (2 : ℝ) ^ 557 =
          (2 : ℝ) ^ 623 := by
        rw [← pow_mul, ← pow_add, ← pow_add]
      have hpow630 : (2 : ℝ) ^ 630 = (2 : ℝ) ^ 7 * (2 : ℝ) ^ 623 := by
        rw [← pow_add]
      rw [hpow630, ← hpow]
      norm_num [C_thetaTOffcenter]
      set_option exponentiation.threshold 1000 in
        ring
    _ < (2 : ℝ) ^ 630 := by
      calc
        (185801 / 262144 : ℝ) * (2 : ℝ) ^ 630 <
            1 * (2 : ℝ) ^ 630 :=
          mul_lt_mul_of_pos_right (by norm_num) (by positivity)
        _ = (2 : ℝ) ^ 630 := by
          set_option exponentiation.threshold 1000 in
            ring

/-- The long-variation constant in Lemma `Auto.leftBumpOneLong`. -/
noncomputable def C_leftBumpOneLong (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 6 * C_inductPositiveTermsReductionWhitney n * C_thetaPrimitive 2 ^ 2

/-! ### Long-variation Whitney normalization -/

theorem aux_leftBumpOneLong_bracket_pos (x : ℝ) : 0 < bracketBump x := by
  rw [bracketBump]
  positivity

theorem aux_leftBumpOneLong_bracket_le_one (x : ℝ) : bracketBump x ≤ 1 := by
  rw [bracketBump]
  exact (inv_le_one₀ (by positivity)).2 (by linarith [abs_nonneg x])

theorem aux_leftBumpOneLong_bracket_mul_le (x y : ℝ) :
    bracketBump x * bracketBump y ≤ bracketBump (x - y) := by
  rw [bracketBump, bracketBump, bracketBump]
  have h : 1 + |x - y| ≤ (1 + |x|) * (1 + |y|) := by
    calc
      1 + |x - y| ≤ 1 + (|x| + |y|) := by
        gcongr
        simpa using (abs_sub_le x 0 y)
      _ ≤ (1 + |x|) * (1 + |y|) := by nlinarith [abs_nonneg x, abs_nonneg y]
  have hp : 0 < 1 + |x - y| := by positivity
  rw [← one_div, ← one_div, ← one_div]
  have h' := one_div_le_one_div_of_le hp h
  simpa [one_div, div_eq_mul_inv, mul_comm] using h'

theorem aux_leftBumpOneLong_bracket_sq_mul_le_three_halves (x y : ℝ) :
    bracketBump x ^ 2 * bracketBump y ^ 2 ≤
      Real.rpow (bracketBump (x - y)) (3 / 2 : ℝ) := by
  have hmul := aux_leftBumpOneLong_bracket_mul_le x y
  have hx : 0 ≤ bracketBump x := (aux_leftBumpOneLong_bracket_pos x).le
  have hy : 0 ≤ bracketBump y := (aux_leftBumpOneLong_bracket_pos y).le
  have hxy : 0 ≤ bracketBump x * bracketBump y := mul_nonneg hx hy
  have hsq : (bracketBump x * bracketBump y) ^ 2 ≤ bracketBump (x - y) ^ 2 :=
    pow_le_pow_left₀ hxy hmul 2
  calc
    bracketBump x ^ 2 * bracketBump y ^ 2 =
        (bracketBump x * bracketBump y) ^ 2 := by ring
    _ ≤ bracketBump (x - y) ^ 2 := hsq
    _ ≤ Real.rpow (bracketBump (x - y)) (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge (aux_leftBumpOneLong_bracket_pos _)
        (aux_leftBumpOneLong_bracket_le_one _) (by norm_num)

theorem aux_leftBumpOneLong_bracket_sq_le_three_halves (x : ℝ) :
    bracketBump x ^ 2 ≤ Real.rpow (bracketBump x) (3 / 2 : ℝ) := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge (aux_leftBumpOneLong_bracket_pos x)
    (aux_leftBumpOneLong_bracket_le_one x) (by norm_num)

theorem aux_leftBumpOneLong_bracket_shift_large_raw (R u : ℝ) (hR : 2 ≤ R)
    (hu : R / 2 ≤ |u - R|) :
    bracketBump (u - R) ≤ 3 * bracketBump u := by
  have hRpos : 0 < R := by linarith
  have habs : |u| ≤ |u - R| + R := by
    calc
      |u| = |(u - R) + R| := by congr 1; ring
      _ ≤ |u - R| + |R| := abs_add_le _ _
      _ = |u - R| + R := by rw [abs_of_pos hRpos]
  have hshift : |u| ≤ 3 * |u - R| := by nlinarith
  have htri : 1 + |u| ≤ 3 * (1 + |u - R|) := by
    nlinarith [abs_nonneg (u - R)]
  rw [bracketBump, bracketBump]
  calc
    (1 + |u - R|)⁻¹ = 1 / (1 + |u - R|) := by rw [one_div]
    _ ≤ 3 / (1 + |u|) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using htri)
    _ = 3 * (1 + |u|)⁻¹ := by rw [div_eq_mul_inv]

theorem aux_leftBumpOneLong_bracket_shift_large (R u : ℝ) (hR : 2 ≤ R)
    (hu : R / 2 ≤ |u - R|) :
    bracketBump (u - R) ^ 2 ≤
      Real.rpow 3 (3 / 2 : ℝ) * Real.rpow (bracketBump u) (3 / 2 : ℝ) := by
  have hraw := aux_leftBumpOneLong_bracket_shift_large_raw R u hR hu
  calc
    bracketBump (u - R) ^ 2 ≤
        Real.rpow (bracketBump (u - R)) (3 / 2 : ℝ) :=
      aux_leftBumpOneLong_bracket_sq_le_three_halves _
    _ ≤ Real.rpow (3 * bracketBump u) (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (aux_leftBumpOneLong_bracket_pos _).le hraw (by norm_num)
    _ = Real.rpow 3 (3 / 2 : ℝ) *
        Real.rpow (bracketBump u) (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) (aux_leftBumpOneLong_bracket_pos _).le

theorem aux_leftBumpOneLong_bracket_shift_scale_raw (R v : ℝ) (hR : 2 ≤ R) :
    bracketBump (v - R) ≤ ((3 / 2 : ℝ) * R) * bracketBump v := by
  have hRpos : 0 < R := by linarith
  have habs : |v| ≤ |v - R| + R := by
    calc
      |v| = |(v - R) + R| := by congr 1; ring
      _ ≤ |v - R| + |R| := abs_add_le _ _
      _ = |v - R| + R := by rw [abs_of_pos hRpos]
  have htri : 1 + |v| ≤ ((3 / 2 : ℝ) * R) * (1 + |v - R|) := by
    nlinarith [abs_nonneg (v - R)]
  rw [bracketBump, bracketBump]
  calc
    (1 + |v - R|)⁻¹ = 1 / (1 + |v - R|) := by rw [one_div]
    _ ≤ ((3 / 2 : ℝ) * R) / (1 + |v|) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using htri)
    _ = ((3 / 2 : ℝ) * R) * (1 + |v|)⁻¹ := by rw [div_eq_mul_inv]

theorem aux_leftBumpOneLong_bracket_shift_scale (R v : ℝ) (hR : 2 ≤ R) :
    Real.rpow R (-(3 / 2 : ℝ)) * bracketBump (v - R) ^ 2 ≤
      Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) *
        Real.rpow (bracketBump v) (3 / 2 : ℝ) := by
  have hRpos : 0 < R := by linarith
  have hraw := aux_leftBumpOneLong_bracket_shift_scale_raw R v hR
  have hpow : Real.rpow (bracketBump (v - R)) (3 / 2 : ℝ) ≤
      Real.rpow (((3 / 2 : ℝ) * R) * bracketBump v) (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (aux_leftBumpOneLong_bracket_pos _).le hraw (by norm_num)
  have hcoef : 0 ≤ Real.rpow R (-(3 / 2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  calc
    Real.rpow R (-(3 / 2 : ℝ)) * bracketBump (v - R) ^ 2 ≤
        Real.rpow R (-(3 / 2 : ℝ)) *
          Real.rpow (bracketBump (v - R)) (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (aux_leftBumpOneLong_bracket_sq_le_three_halves _) hcoef
    _ ≤ Real.rpow R (-(3 / 2 : ℝ)) *
          Real.rpow (((3 / 2 : ℝ) * R) * bracketBump v) (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hcoef
    _ = Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) *
        Real.rpow (bracketBump v) (3 / 2 : ℝ) := by
      have hsplit1 : Real.rpow (((3 / 2 : ℝ) * R) * bracketBump v) (3 / 2 : ℝ) =
          Real.rpow ((3 / 2 : ℝ) * R) (3 / 2 : ℝ) *
            Real.rpow (bracketBump v) (3 / 2 : ℝ) :=
        Real.mul_rpow (mul_nonneg (by norm_num) hRpos.le)
          (aux_leftBumpOneLong_bracket_pos _).le
      have hsplit2 : Real.rpow ((3 / 2 : ℝ) * R) (3 / 2 : ℝ) =
          Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) * Real.rpow R (3 / 2 : ℝ) :=
        Real.mul_rpow (by norm_num) hRpos.le
      have hneg : Real.rpow R (-(3 / 2 : ℝ)) =
          (Real.rpow R (3 / 2 : ℝ))⁻¹ :=
        Real.rpow_neg hRpos.le (3 / 2 : ℝ)
      rw [hsplit1, hsplit2, hneg]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hRpos (3 / 2 : ℝ))]

theorem aux_leftBumpOneLong_scale_to_bracket (R c v : ℝ) (hR : 0 < R)
    (hc : 0 < c) (h : 1 + |v| ≤ c * R) :
    Real.rpow R (-(3 / 2 : ℝ)) ≤
      Real.rpow c (3 / 2 : ℝ) * Real.rpow (bracketBump v) (3 / 2 : ℝ) := by
  have hbase : R⁻¹ ≤ c * bracketBump v := by
    change R⁻¹ ≤ c / (1 + |v|)
    rw [le_div_iff₀ (by positivity)]
    calc
      R⁻¹ * (1 + |v|) ≤ R⁻¹ * (c * R) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hR.le)
      _ = c := by field_simp [hR.ne']
  calc
    Real.rpow R (-(3 / 2 : ℝ)) = Real.rpow R⁻¹ (3 / 2 : ℝ) :=
      Real.rpow_neg_eq_inv_rpow R _
    _ ≤ Real.rpow (c * bracketBump v) (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hR.le) hbase (by norm_num)
    _ = Real.rpow c (3 / 2 : ℝ) *
        Real.rpow (bracketBump v) (3 / 2 : ℝ) :=
      Real.mul_rpow hc.le (aux_leftBumpOneLong_bracket_pos v).le

theorem aux_leftBumpOneLong_rpow_three_halves_le (q : ℝ) (hq : 0 < q)
    (hroot : Real.sqrt q ≤ 3) :
    Real.rpow q (3 / 2 : ℝ) ≤ 3 * q := by
  calc
    Real.rpow q (3 / 2 : ℝ) = Real.rpow q (1 / 2 : ℝ) * q := by
      convert Real.rpow_add hq (1 / 2 : ℝ) 1 using 1 <;> norm_num
    _ = Real.sqrt q * q := by
      exact congrArg (fun z : ℝ => z * q) (Real.sqrt_eq_rpow q).symm
    _ ≤ 3 * q := by gcongr

theorem aux_leftBumpOneLong_rpow_nine_halves_le_sixteen :
    Real.rpow (9 / 2 : ℝ) (3 / 2 : ℝ) ≤ 16 := by
  have hsqrt : Real.sqrt (9 / 2 : ℝ) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 9 / 2),
      Real.sqrt_nonneg (9 / 2 : ℝ)]
  calc
    Real.rpow (9 / 2 : ℝ) (3 / 2 : ℝ) ≤ 3 * (9 / 2 : ℝ) :=
      aux_leftBumpOneLong_rpow_three_halves_le _ (by norm_num) hsqrt
    _ ≤ 16 := by norm_num

theorem aux_leftBumpOneLong_rpow_seven_halves_le_sixteen :
    Real.rpow (7 / 2 : ℝ) (3 / 2 : ℝ) ≤ 16 := by
  have hsqrt : Real.sqrt (7 / 2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 2),
      Real.sqrt_nonneg (7 / 2 : ℝ)]
  calc
    Real.rpow (7 / 2 : ℝ) (3 / 2 : ℝ) ≤ 3 * (7 / 2 : ℝ) :=
      aux_leftBumpOneLong_rpow_three_halves_le _ (by norm_num)
        (hsqrt.trans (by norm_num))
    _ ≤ 16 := by norm_num

theorem aux_leftBumpOneLong_shifted_bracket_decay (R u v : ℝ) (hR : 2 ≤ R) :
    Real.rpow R (-(3 / 2 : ℝ)) *
        (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
      16 * (Real.rpow (bracketBump u) (3 / 2 : ℝ) *
          Real.rpow (bracketBump v) (3 / 2 : ℝ) +
        Real.rpow (bracketBump (u + v)) (3 / 2 : ℝ) *
          Real.rpow (bracketBump (u - v)) (3 / 2 : ℝ)) := by
  have hRpos : 0 < R := by linarith
  let A : ℝ := Real.rpow (bracketBump u) (3 / 2 : ℝ) *
    Real.rpow (bracketBump v) (3 / 2 : ℝ)
  let B : ℝ := Real.rpow (bracketBump (u + v)) (3 / 2 : ℝ) *
    Real.rpow (bracketBump (u - v)) (3 / 2 : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (Real.rpow_nonneg (aux_leftBumpOneLong_bracket_pos u).le _)
      (Real.rpow_nonneg (aux_leftBumpOneLong_bracket_pos v).le _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Real.rpow_nonneg (aux_leftBumpOneLong_bracket_pos (u + v)).le _)
      (Real.rpow_nonneg (aux_leftBumpOneLong_bracket_pos (u - v)).le _)
  by_cases hu : R / 2 ≤ |u - R|
  · have hlarge := aux_leftBumpOneLong_bracket_shift_large R u hR hu
    have hscale := aux_leftBumpOneLong_bracket_shift_scale R v hR
    have hcoef : Real.rpow 3 (3 / 2 : ℝ) *
        Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) ≤ 16 := by
      calc
        Real.rpow 3 (3 / 2 : ℝ) * Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) =
            Real.rpow (9 / 2 : ℝ) (3 / 2 : ℝ) := by
              have hmul : Real.rpow ((3 : ℝ) * (3 / 2 : ℝ)) (3 / 2 : ℝ) =
                  Real.rpow 3 (3 / 2 : ℝ) *
                    Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) :=
                Real.mul_rpow (by norm_num) (by norm_num)
              rw [← hmul]
              norm_num
        _ ≤ 16 := aux_leftBumpOneLong_rpow_nine_halves_le_sixteen
    have hprod : Real.rpow R (-(3 / 2 : ℝ)) *
        (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
        (Real.rpow 3 (3 / 2 : ℝ) *
          Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ)) * A := by
      calc
        Real.rpow R (-(3 / 2 : ℝ)) *
            (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) =
            (bracketBump (u - R) ^ 2) *
              (Real.rpow R (-(3 / 2 : ℝ)) * bracketBump (v - R) ^ 2) := by ring
        _ ≤ (Real.rpow 3 (3 / 2 : ℝ) *
              Real.rpow (bracketBump u) (3 / 2 : ℝ)) *
            (Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) *
              Real.rpow (bracketBump v) (3 / 2 : ℝ)) := by
              exact mul_le_mul hlarge hscale
                (mul_nonneg (Real.rpow_nonneg hRpos.le _) (sq_nonneg _))
                (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                  (Real.rpow_nonneg (aux_leftBumpOneLong_bracket_pos u).le _))
        _ = (Real.rpow 3 (3 / 2 : ℝ) *
              Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ)) * A := by
              dsimp [A]
              ring
    calc
      Real.rpow R (-(3 / 2 : ℝ)) *
          (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
          (Real.rpow 3 (3 / 2 : ℝ) *
            Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ)) * A := hprod
      _ ≤ 16 * A := mul_le_mul_of_nonneg_right hcoef hA
      _ ≤ 16 * (A + B) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB) (by norm_num)
  · have hu' : |u - R| < R / 2 := lt_of_not_ge hu
    by_cases hv : R / 2 ≤ |v - R|
    · have hvlarge := aux_leftBumpOneLong_bracket_shift_large R v hR hv
      have huscale := aux_leftBumpOneLong_bracket_shift_scale R u hR
      have hcoef : Real.rpow 3 (3 / 2 : ℝ) *
          Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) ≤ 16 := by
        calc
          Real.rpow 3 (3 / 2 : ℝ) * Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) =
              Real.rpow (9 / 2 : ℝ) (3 / 2 : ℝ) := by
                have hmul : Real.rpow ((3 : ℝ) * (3 / 2 : ℝ)) (3 / 2 : ℝ) =
                    Real.rpow 3 (3 / 2 : ℝ) *
                      Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) :=
                  Real.mul_rpow (by norm_num) (by norm_num)
                rw [← hmul]
                norm_num
        _ ≤ 16 := aux_leftBumpOneLong_rpow_nine_halves_le_sixteen
      have hprod : Real.rpow R (-(3 / 2 : ℝ)) *
          (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
          (Real.rpow 3 (3 / 2 : ℝ) *
            Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ)) * A := by
        calc
          Real.rpow R (-(3 / 2 : ℝ)) *
              (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) =
              (Real.rpow R (-(3 / 2 : ℝ)) * bracketBump (u - R) ^ 2) *
                bracketBump (v - R) ^ 2 := by ring
          _ ≤ (Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ) *
                Real.rpow (bracketBump u) (3 / 2 : ℝ)) *
              (Real.rpow 3 (3 / 2 : ℝ) *
                Real.rpow (bracketBump v) (3 / 2 : ℝ)) := by
                exact mul_le_mul huscale hvlarge
                  (sq_nonneg _)
                  (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                    (Real.rpow_nonneg (aux_leftBumpOneLong_bracket_pos u).le _))
          _ = (Real.rpow 3 (3 / 2 : ℝ) *
                Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ)) * A := by
                dsimp [A]
                ring
      calc
        Real.rpow R (-(3 / 2 : ℝ)) *
            (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
            (Real.rpow 3 (3 / 2 : ℝ) *
              Real.rpow (3 / 2 : ℝ) (3 / 2 : ℝ)) * A := hprod
        _ ≤ 16 * A := mul_le_mul_of_nonneg_right hcoef hA
        _ ≤ 16 * (A + B) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB) (by norm_num)
    · have hv' : |v - R| < R / 2 := lt_of_not_ge hv
      have hsum : 1 + |u + v| ≤ (7 / 2 : ℝ) * R := by
        have habs : |u + v| ≤ |u - R| + |v - R| + 2 * R := by
          calc
            |u + v| = |(u - R) + (v - R) + (R + R)| := by congr 1; ring
            _ ≤ |(u - R) + (v - R)| + |R + R| := abs_add_le _ _
            _ ≤ (|u - R| + |v - R|) + |R + R| := by
              gcongr
              exact abs_add_le _ _
            _ = |u - R| + |v - R| + 2 * R := by
              have hRR : |R + R| = 2 * R := by
                rw [abs_of_nonneg (by linarith [hRpos])]
                ring
              rw [hRR]
        nlinarith
      have hscale := aux_leftBumpOneLong_scale_to_bracket R (7 / 2 : ℝ) (u + v)
        hRpos (by norm_num) hsum
      have hproduct : bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2 ≤
          Real.rpow (bracketBump (u - v)) (3 / 2 : ℝ) := by
        convert aux_leftBumpOneLong_bracket_sq_mul_le_three_halves (u - R) (v - R)
          using 1; ring_nf
      have hcoef := aux_leftBumpOneLong_rpow_seven_halves_le_sixteen
      have hprod : Real.rpow R (-(3 / 2 : ℝ)) *
          (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
          Real.rpow (7 / 2 : ℝ) (3 / 2 : ℝ) * B := by
        calc
          Real.rpow R (-(3 / 2 : ℝ)) *
              (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
              Real.rpow R (-(3 / 2 : ℝ)) *
                Real.rpow (bracketBump (u - v)) (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hproduct (Real.rpow_nonneg hRpos.le _)
          _ ≤ (Real.rpow (7 / 2 : ℝ) (3 / 2 : ℝ) *
                Real.rpow (bracketBump (u + v)) (3 / 2 : ℝ)) *
              Real.rpow (bracketBump (u - v)) (3 / 2 : ℝ) := by
              exact mul_le_mul_of_nonneg_right hscale
                (Real.rpow_nonneg (aux_leftBumpOneLong_bracket_pos (u - v)).le _)
          _ = Real.rpow (7 / 2 : ℝ) (3 / 2 : ℝ) * B := by
              dsimp [B]
              ring
      calc
        Real.rpow R (-(3 / 2 : ℝ)) *
            (bracketBump (u - R) ^ 2 * bracketBump (v - R) ^ 2) ≤
            Real.rpow (7 / 2 : ℝ) (3 / 2 : ℝ) * B := hprod
        _ ≤ 16 * B := mul_le_mul_of_nonneg_right hcoef hB
        _ ≤ 16 * (A + B) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) (by norm_num)

theorem aux_leftBumpOneLong_phiFour_plane_formula (b : windowBasedBumpFunctions)
    (k : ℤ) (c z : ℝ) :
    aux_planeFourier (fun v => c * tensorSquare (phiFourSchwartz b k) v)
      (WithLp.toLp 2 ![z, -z]) =
      (c : ℂ) * (((2 : ℝ) ^ (2 * k) : ℝ) : ℂ) *
        FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) z *
        FourierTransform.fourier
          (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ)) (-z) := by
  have hfun : (fun x : ℝ => (phiFourSchwartz b k x : ℂ)) =
      fun x : ℝ => (windowBasedBumpFunctions.phiFour b k x : ℂ) := by
    funext x
    rw [phiFourSchwartz_apply]
  have htensor (f : ℝ → ℝ) (xi : EuclideanSpace ℝ (Fin 2)) :
      aux_planeFourier (tensorSquare f) xi =
        FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) (xi 0) *
          FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) (xi 1) := by
    unfold aux_planeFourier tensorSquare
    simpa using aux_fourier_tensor_two_eq f f xi
  rw [aux_leftBumpOneShort_planeFourier_const_mul, htensor, hfun]
  change (c : ℂ) *
      (FourierTransform.fourier
        (fun x : ℝ => (windowBasedBumpFunctions.phiFour b k x : ℂ)) z *
      FourierTransform.fourier
        (fun x : ℝ => (windowBasedBumpFunctions.phiFour b k x : ℂ)) (-z)) = _
  rw [phiFour_fourier_pair_eq]
  ring

theorem aux_leftBumpOneLong_phiFour_support (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ => (phiFourSchwartz b k x : ℂ))) ⊆
      Auto.aux_annulusOne 1 ((2 : ℝ) ^ 3) := by
  intro xi hxi
  have h := aux_leftBumpOneShort_phiFourSchwartz_support b k hxi
  unfold Auto.aux_annulusOne at h ⊢
  constructor <;> nlinarith [h.1, h.2]

theorem aux_leftBumpOneLong_diagonal_bound (b : windowBasedBumpFunctions)
    (k : ℤ) (c : ℝ)
    (hscalar : |c * (2 : ℝ) ^ (2 * k)| *
        (4 * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2) ≤ 1)
    (m : ℕ) (hm : m < 3) (xi : ℝ) :
    ‖iteratedDeriv m
      (fun z : ℝ => aux_planeFourier
        (fun v => c * tensorSquare (phiFourSchwartz b k) v)
        (WithLp.toLp 2 ![z, -z])) xi‖ ≤ 1 := by
  let H : ℝ → ℂ := FourierTransform.fourier
    (fun x : ℝ => (windowBasedBumpFunctions.thetaTilde b x : ℂ))
  let B : ℝ := (2 : ℝ) ^ 14 * C_uniPair
  have hB : 0 ≤ B := by
    dsimp [B]
    norm_num [C_uniPair]
  have hbound : ∀ q : ℕ, q ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv q H x‖ ≤ B := by
    intro q hq x
    dsimp [H, B]
    exact thetaTildeFourier_deriv_bound b q (le_trans hq (by norm_num)) x
  have hformula :
      (fun z : ℝ => aux_planeFourier
        (fun v => c * tensorSquare (phiFourSchwartz b k) v)
        (WithLp.toLp 2 ![z, -z])) =
      fun z => ((c * (2 : ℝ) ^ (2 * k) : ℝ) : ℂ) * (H z * H (-z)) := by
    funext z
    rw [aux_leftBumpOneLong_phiFour_plane_formula]
    dsimp [H]
    push_cast
    ring
  rw [hformula, iteratedDeriv_const_mul_field, norm_mul, Complex.norm_real]
  have hprod := aux_leftBumpOneShort_pair_deriv_bound H
    ((aux_leftBumpOneShort_thetaTildeFourier_contDiff b).of_le (by norm_num)) B hB hbound m
    (by omega) xi
  have hprod' : ‖iteratedDeriv m (fun z : ℝ => H z * H (-z)) xi‖ ≤
      4 * B ^ 2 := by
    calc
      ‖iteratedDeriv m (fun z : ℝ => H z * H (-z)) xi‖ ≤ (2 : ℝ) ^ m * B ^ 2 :=
        hprod
      _ ≤ 4 * B ^ 2 := by
        interval_cases m <;> nlinarith [sq_nonneg B]
  calc
    |c * (2 : ℝ) ^ (2 * k)| *
        ‖iteratedDeriv m (fun z : ℝ => H z * H (-z)) xi‖ ≤
        |c * (2 : ℝ) ^ (2 * k)| * (4 * B ^ 2) :=
      mul_le_mul_of_nonneg_left hprod' (abs_nonneg _)
    _ ≤ 1 := by simpa [B] using hscalar

theorem aux_leftBumpOneLong_R_ge_two (k : ℤ) (hk : k ≤ -1) :
    (2 : ℝ) ≤ (2 : ℝ) ^ (-k) := by
  calc
    (2 : ℝ) = (2 : ℝ) ^ (1 : ℤ) := by norm_num
    _ ≤ (2 : ℝ) ^ (-k) :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by omega)

theorem aux_leftBumpOneLong_zpow_twice_rpow (k : ℤ) :
    (2 : ℝ) ^ (2 * k) = Real.rpow ((2 : ℝ) ^ (-k)) (-2 : ℝ) := by
  let R : ℝ := (2 : ℝ) ^ (-k)
  have hR : (2 : ℝ) ^ k = R⁻¹ := by
    simp [R, zpow_neg]
  calc
    (2 : ℝ) ^ (2 * k) = ((2 : ℝ) ^ k) ^ 2 := by
      rw [show 2 * k = k * 2 by ring, zpow_mul]
      rfl
    _ = (R⁻¹) ^ 2 := by rw [hR]
    _ = R ^ (-2 : ℤ) := by
      rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg]
      norm_num
    _ = Real.rpow R (-2 : ℝ) := by
      simp

theorem aux_leftBumpOneLong_c_scale_physical (k : ℤ) :
    let R : ℝ := (2 : ℝ) ^ (-k)
    let C : ℝ := C_thetaPrimitive 2
    let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
    c * (((2 : ℝ) ^ k * C) * ((2 : ℝ) ^ k * C)) =
      (16 : ℝ)⁻¹ * Real.rpow R (-(3 / 2 : ℝ)) := by
  dsimp
  let R : ℝ := (2 : ℝ) ^ (-k)
  let C : ℝ := C_thetaPrimitive 2
  change (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ) *
      (((2 : ℝ) ^ k * C) * ((2 : ℝ) ^ k * C)) =
        (16 : ℝ)⁻¹ * Real.rpow R (-(3 / 2 : ℝ))
  have hR : (2 : ℝ) ^ k = R⁻¹ := by
    simp [R, zpow_neg]
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hCpos : 0 < C := by
    dsimp [C]
    norm_num [C_thetaPrimitive, C_uniPair]
  rw [hR]
  calc
    (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ) *
        (R⁻¹ * C * (R⁻¹ * C)) =
      (16 : ℝ)⁻¹ * (R⁻¹ * R⁻¹) * Real.rpow R (1 / 2 : ℝ) := by
        field_simp [hCpos.ne']
    _ = (16 : ℝ)⁻¹ * Real.rpow R (-(3 / 2 : ℝ)) := by
      have hpow : R⁻¹ * R⁻¹ = Real.rpow R (-2 : ℝ) := by
        calc
          R⁻¹ * R⁻¹ = R ^ (-2 : ℤ) := by
            rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg]
            field_simp [hRpos.ne']
          _ = Real.rpow R (-2 : ℝ) := by
            simp
      calc
        (16 : ℝ)⁻¹ * (R⁻¹ * R⁻¹) * Real.rpow R (1 / 2 : ℝ) =
            (16 : ℝ)⁻¹ * (Real.rpow R (-2 : ℝ) *
              Real.rpow R (1 / 2 : ℝ)) := by rw [hpow]; ring
        _ = (16 : ℝ)⁻¹ * Real.rpow R (-(3 / 2 : ℝ)) := by
            have hsum : Real.rpow R (-2 : ℝ) * Real.rpow R (1 / 2 : ℝ) =
                Real.rpow R (-(3 / 2 : ℝ)) := by
              calc
                Real.rpow R (-2 : ℝ) * Real.rpow R (1 / 2 : ℝ) =
                    Real.rpow R ((-2 : ℝ) + (1 / 2 : ℝ)) :=
                  (Real.rpow_add hRpos (-2 : ℝ) (1 / 2 : ℝ)).symm
                _ = Real.rpow R (-(3 / 2 : ℝ)) := by
                  congr 1
                  ring
            rw [hsum]

theorem aux_leftBumpOneLong_phiFour_decay (b : windowBasedBumpFunctions)
    (k : ℤ) (x : ℝ) :
    |phiFourSchwartz b k x| ≤
      (2 : ℝ) ^ k * C_thetaPrimitive 2 *
        bracketBump (x - (2 : ℝ) ^ (-k)) ^ 2 := by
  rw [phiFourSchwartz_apply, windowBasedBumpFunctions.phiFour, abs_mul,
    abs_of_pos (zpow_pos (by norm_num) _)]
  simpa [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      ((thetaPrimitive b 2 (by norm_num) (by norm_num [N_uniPair])).2.2.1
        (x - (2 : ℝ) ^ (-k)))
      (zpow_pos (by norm_num : (0 : ℝ) < 2) k).le)

theorem aux_leftBumpOneLong_W_decay_dominates (v : RealPlane) :
    Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
          Real.rpow (bracketBump v.2) (3 / 2 : ℝ) +
        Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) *
          Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ) ≤
      ∑ u : Fin 2,
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
  rw [Fin.sum_univ_two]
  have hfirst : Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
      Real.rpow (bracketBump v.2) (3 / 2 : ℝ) =
      scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W (0 : Fin 2) v).1) *
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W (0 : Fin 2) v).2) := by
    rw [W, if_pos rfl, aux_leftBumpOneShort_scaledBracket_one_eq_rpow,
      aux_leftBumpOneShort_scaledBracket_one_eq_rpow]
  rw [← hfirst]
  simpa [add_comm] using
    (add_le_add_left (aux_leftBumpOneShort_offcenter_second_term_le_whitney v)
      (Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
        Real.rpow (bracketBump v.2) (3 / 2 : ℝ)))

theorem aux_leftBumpOneLong_data_decay (b : windowBasedBumpFunctions) (k : ℤ)
    (hk : k ≤ -1) :
    let R : ℝ := (2 : ℝ) ^ (-k)
    let C : ℝ := C_thetaPrimitive 2
    let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
    ∀ v : RealPlane,
      |c * tensorSquare (phiFourSchwartz b k) v| ≤
        ∑ u : Fin 2,
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
            scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) := by
  dsimp
  let R : ℝ := (2 : ℝ) ^ (-k)
  let C : ℝ := C_thetaPrimitive 2
  let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
  change ∀ v : RealPlane,
    |c * tensorSquare (phiFourSchwartz b k) v| ≤
      ∑ u : Fin 2,
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2)
  have hRtwo : 2 ≤ R := by
    dsimp [R]
    exact aux_leftBumpOneLong_R_ge_two k hk
  have hc : 0 ≤ c := by
    have hC : 0 < C := by
      dsimp [C]
      norm_num [C_thetaPrimitive, C_uniPair]
    dsimp [c]
    exact mul_nonneg (inv_nonneg.mpr (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  intro v
  rw [tensorSquare, abs_mul, abs_of_nonneg hc, abs_mul]
  have h0 := aux_leftBumpOneLong_phiFour_decay b k v.1
  have h1 := aux_leftBumpOneLong_phiFour_decay b k v.2
  have hprod :
      |phiFourSchwartz b k v.1| * |phiFourSchwartz b k v.2| ≤
        ((2 : ℝ) ^ k * C) * ((2 : ℝ) ^ k * C) *
          (bracketBump (v.1 - R) ^ 2 * bracketBump (v.2 - R) ^ 2) := by
    have h0' : |phiFourSchwartz b k v.1| ≤
        (2 : ℝ) ^ k * C * bracketBump (v.1 - R) ^ 2 := by
      simpa [R, C, mul_assoc] using h0
    have h1' : |phiFourSchwartz b k v.2| ≤
        (2 : ℝ) ^ k * C * bracketBump (v.2 - R) ^ 2 := by
      simpa [R, C, mul_assoc] using h1
    have hCpos : 0 < C := by
      dsimp [C]
      norm_num [C_thetaPrimitive, C_uniPair]
    have hrightnonneg : 0 ≤
        (2 : ℝ) ^ k * C * bracketBump (v.2 - R) ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (zpow_pos (by norm_num) _).le hCpos.le)
        (sq_nonneg _)
    have hleftnonneg : 0 ≤
        (2 : ℝ) ^ k * C * bracketBump (v.1 - R) ^ 2 := by
      exact mul_nonneg
        (mul_nonneg (zpow_pos (by norm_num) _).le hCpos.le)
        (sq_nonneg _)
    calc
      |phiFourSchwartz b k v.1| * |phiFourSchwartz b k v.2| ≤
          ((2 : ℝ) ^ k * C * bracketBump (v.1 - R) ^ 2) *
            ((2 : ℝ) ^ k * C * bracketBump (v.2 - R) ^ 2) :=
        mul_le_mul h0' h1' (abs_nonneg _) hleftnonneg
      _ = ((2 : ℝ) ^ k * C) * ((2 : ℝ) ^ k * C) *
          (bracketBump (v.1 - R) ^ 2 * bracketBump (v.2 - R) ^ 2) := by ring
  have hcoef := aux_leftBumpOneLong_c_scale_physical k
  change c * (|phiFourSchwartz b k v.1| * |phiFourSchwartz b k v.2|) ≤ _
  calc
    c * (|phiFourSchwartz b k v.1| * |phiFourSchwartz b k v.2|) ≤
        c * (((2 : ℝ) ^ k * C) * ((2 : ℝ) ^ k * C) *
          (bracketBump (v.1 - R) ^ 2 * bracketBump (v.2 - R) ^ 2)) := by
      gcongr
    _ = (16 : ℝ)⁻¹ *
        (Real.rpow R (-(3 / 2 : ℝ)) *
          (bracketBump (v.1 - R) ^ 2 * bracketBump (v.2 - R) ^ 2)) := by
      rw [← mul_assoc, hcoef]
      ring
    _ ≤ Real.rpow (bracketBump v.1) (3 / 2 : ℝ) *
          Real.rpow (bracketBump v.2) (3 / 2 : ℝ) +
        Real.rpow (bracketBump (v.1 + v.2)) (3 / 2 : ℝ) *
          Real.rpow (bracketBump (v.1 - v.2)) (3 / 2 : ℝ) := by
      have hsharp := aux_leftBumpOneLong_shifted_bracket_decay R v.1 v.2 hRtwo
      nlinarith
    _ ≤ ∑ u : Fin 2,
        scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).1) *
          scaledBracketBumpReal (3 / 2 : ℝ) 1 ((W u v).2) :=
      aux_leftBumpOneLong_W_decay_dominates v

theorem aux_leftBumpOneLong_c_diagonal_scalar (k : ℤ) (hk : k ≤ -1) :
    let R : ℝ := (2 : ℝ) ^ (-k)
    let C : ℝ := C_thetaPrimitive 2
    let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
    |c * (2 : ℝ) ^ (2 * k)| *
      (4 * ((2 : ℝ) ^ 14 * C_uniPair) ^ 2) ≤ 1 := by
  dsimp
  let R : ℝ := (2 : ℝ) ^ (-k)
  let C : ℝ := C_thetaPrimitive 2
  let B : ℝ := (2 : ℝ) ^ 14 * C_uniPair
  change |(16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ) *
      (2 : ℝ) ^ (2 * k)| * (4 * B ^ 2) ≤ 1
  have hRtwo : 2 ≤ R := by
    dsimp [R]
    exact aux_leftBumpOneLong_R_ge_two k hk
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hRtwo
  have hC : C = 4 * B := by
    dsimp [C, B]
    norm_num [C_thetaPrimitive]
    ring
  have hCpos : 0 < C := by
    rw [hC]
    have : 0 < B := by dsimp [B]; norm_num [C_uniPair]
    positivity
  have hneg : Real.rpow R (-(3 / 2 : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hRtwo]) (by norm_num)
  rw [aux_leftBumpOneLong_zpow_twice_rpow]
  have hscale :
      (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ) *
          Real.rpow R (-2 : ℝ) =
        (16 * C ^ 2)⁻¹ * Real.rpow R (-(3 / 2 : ℝ)) := by
    calc
      (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ) *
          Real.rpow R (-2 : ℝ) =
        (16 * C ^ 2)⁻¹ *
          (Real.rpow R (1 / 2 : ℝ) * Real.rpow R (-2 : ℝ)) := by ring
      _ = (16 * C ^ 2)⁻¹ * Real.rpow R (-(3 / 2 : ℝ)) := by
        have hsum : Real.rpow R (1 / 2 : ℝ) * Real.rpow R (-2 : ℝ) =
            Real.rpow R (-(3 / 2 : ℝ)) := by
          calc
            Real.rpow R (1 / 2 : ℝ) * Real.rpow R (-2 : ℝ) =
                Real.rpow R ((1 / 2 : ℝ) + (-2 : ℝ)) :=
              (Real.rpow_add hRpos (1 / 2 : ℝ) (-2 : ℝ)).symm
            _ = Real.rpow R (-(3 / 2 : ℝ)) := by
              congr 1
              ring
        rw [hsum]
  have hnonneg : 0 ≤
      (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ) *
        Real.rpow R (-2 : ℝ) := by
    have hden : 0 < 16 * C ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hCpos)
    exact mul_nonneg
      (mul_nonneg (inv_pos.mpr hden).le (Real.rpow_pos_of_pos hRpos _).le)
      (Real.rpow_pos_of_pos hRpos _).le
  rw [abs_of_nonneg hnonneg, hscale, hC]
  have hBpos : 0 < B := by dsimp [B]; norm_num [C_uniPair]
  calc
    (16 * (4 * B) ^ 2)⁻¹ * Real.rpow R (-(3 / 2 : ℝ)) *
        (4 * B ^ 2) =
      (64 : ℝ)⁻¹ * Real.rpow R (-(3 / 2 : ℝ)) := by
        field_simp [hBpos.ne']
        ring
    _ ≤ 1 := by nlinarith

theorem aux_leftBumpOneLong_tensor_sequence_eq (psi : SchwartzMap ℝ ℝ)
    (c : ℝ) (hc : c ≠ 0) (a : ℤ → ℝ) (ha : SpacedSequence a)
    (j : ℤ) (y : RealVector 1 × RealVector 1) :
    aux_liftPlaneKernel
      (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j) (ha j).1)) y =
      c⁻¹ * aux_whitneySequence (fun v => c * tensorSquare psi v) a j y := by
  simp only [aux_liftPlaneKernel, tensorSquare, aux_whitneySequence,
    aux_planeRescale, aux_mainAuxOne_windowSchwartz_apply, aux_windowRescale]
  have hapos : a j ≠ 0 := ne_of_gt (ha j).1
  field_simp [hc, hapos]

theorem aux_leftBumpOneLong_tensor_whitney_prefix {n : ℕ} (hn : 2 ≤ n)
    (a : ℤ → ℝ) (ha : SpacedSequence a) (psi : SchwartzMap ℝ ℝ)
    (c : ℝ) (hc : 0 < c) (Psi : WhitneyKernelData)
    (hkernel : Psi.kernel = fun v => c * tensorSquare psi v)
    (f : ReductionNormalizedTuple n) (J : ℕ) (hJ : 0 < J) :
    ∑ j : Fin J,
      eLpNorm (twistedAverageAtScale (a (j : ℤ)) (fun x => psi x)
        (fun i x => f.1 i x)) 2 volume ^ 2 ≤
      ENNReal.ofReal (c⁻¹ * C_inductPositiveTermsReductionWhitney n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  let phi : Fin J → SchwartzMap ℝ ℝ := fun j =>
    aux_mainAuxOne_windowSchwartz psi (a (j : ℤ)) (ha (j : ℤ)).1
  obtain ⟨F, hFnorm, hsum⟩ := aToLambda_fin_sum (n := n) (J := J) (by omega) phi f.1
  let Fnorm : NormalizedFunctionTuple n := ⟨F, by
    intro i
    convert (hFnorm i ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2))).trans
      (f.2 i) using 1; norm_num⟩
  let M : KernelSequence 1 := fun j y => aux_liftPlaneKernel
    (tensorSquare (aux_mainAuxOne_windowSchwartz psi (a j) (ha j).1)) y
  let N : KernelSequence 1 := aux_whitneySequence Psi.kernel a
  obtain ⟨phi0, phi1, hpair⟩ := existsUniversalPair
  have hNbound : kernelSequenceSeminorm n 1 (by omega) (by omega) N ≤
      ENNReal.ofReal (C_inductPositiveTermsReductionWhitney n) := by
    dsimp [N]
    exact inductPositiveTermsReductionWhitney hn a ha phi0 phi1 hpair Psi
  have hseq : M = fun j y => c⁻¹ * N j y := by
    funext j y
    dsimp [M, N]
    rw [hkernel]
    exact aux_leftBumpOneLong_tensor_sequence_eq psi c hc.ne' a ha j y
  have hMbound : kernelSequenceSeminorm n 1 (by omega) (by omega) M ≤
      ENNReal.ofReal (c⁻¹ * C_inductPositiveTermsReductionWhitney n) := by
    rw [hseq, aux_kernelSequenceSeminorm_const_mul (by omega) (by omega) c⁻¹
      (inv_nonneg.mpr hc.le)]
    calc
      ENNReal.ofReal c⁻¹ * kernelSequenceSeminorm n 1 (by omega) (by omega) N ≤
          ENNReal.ofReal c⁻¹ * ENNReal.ofReal (C_inductPositiveTermsReductionWhitney n) :=
        mul_le_mul_of_nonneg_left hNbound bot_le
      _ = ENNReal.ofReal (c⁻¹ * C_inductPositiveTermsReductionWhitney n) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
  have hprefix := aux_mainAuxOne_prefix_from_seminorm hn M
    (c⁻¹ * C_inductPositiveTermsReductionWhitney n) hMbound J hJ Fnorm
  have hleft :
      (∑ j : Fin J,
        eLpNorm (twistedAverageAtScale (a (j : ℤ)) (fun x => psi x)
          (fun i x => f.1 i x)) 2 volume ^ 2) =
      ∑ j : Fin J,
        eLpNorm (twistedAverage (phi j) (fun i x => f.1 i x)) 2 volume ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [phi]
    unfold twistedAverage twistedAverageAtScale
    congr 1
  have hkernel' :
      (fun y : RealVector 1 × RealVector 1 =>
        ∑ j : Fin J, phi j (y.1 0) * phi j (y.2 0)) =
      fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y := by
    funext y
    let g : ℕ → ℝ := fun r => if hr : r < J then M (r : ℤ) y else 0
    calc
      (∑ j : Fin J, phi j (y.1 0) * phi j (y.2 0)) =
          ∑ r ∈ Finset.range J, g r := by
            rw [← Fin.sum_univ_eq_sum_range g J]
            apply Finset.sum_congr rfl
            intro j hj
            dsimp [g]
            rw [if_pos j.2]
            simp only [M, phi, aux_liftPlaneKernel, tensorSquare]
      _ = ∑ r ∈ Finset.range J, M (r : ℤ) y := by
            apply Finset.sum_congr rfl
            intro r hr
            dsimp [g]
            rw [if_pos (Finset.mem_range.mp hr)]
  have hsum' :
      (∑ j : Fin J,
        eLpNorm (twistedAverage (phi j) (fun i x => f.1 i x)) 2 volume ^ 2) =
      ENNReal.ofReal
        (prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i x => F i x)) := by
    rw [hsum, hkernel']
  calc
    ∑ j : Fin J,
        eLpNorm (twistedAverageAtScale (a (j : ℤ)) (fun x => psi x)
          (fun i x => f.1 i x)) 2 volume ^ 2 =
        ENNReal.ofReal
          (prismForm n 1 (by omega) (by omega)
            (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
            (fun i x ↦ F i x)) := hleft.trans hsum'
    _ ≤ ENNReal.ofReal
        |prismForm n 1 (by omega) (by omega)
          (fun y => ∑ j ∈ Finset.range J, M (j : ℤ) y)
          (fun i x => F i x)| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ENNReal.ofReal (c⁻¹ * C_inductPositiveTermsReductionWhitney n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      simpa [Fnorm] using hprefix

theorem aux_leftBumpOneLong_tensor_whitney_dyadic {n : ℕ} (hn : 2 ≤ n)
    (psi : SchwartzMap ℝ ℝ) (c : ℝ) (hc : 0 < c) (Psi : WhitneyKernelData)
    (hkernel : Psi.kernel = fun v => c * tensorSquare psi v)
    (f : ReductionNormalizedTuple n) :
    aux_dyadicVariationBound
      (4 * (c⁻¹ * C_inductPositiveTermsReductionWhitney n))
      (fun x => psi x) f.1 := by
  intro J hJ k
  have hsup :
      (⨆ ks : {u : Fin J → ℤ // StrictMono u},
        ∑ j, eLpNorm
          (twistedAverageAtScale ((2 : ℝ) ^ (ks.1 j)) (fun x => psi x)
            (fun i x => f.1 i x)) 2 volume ^ 2) ≤
        ENNReal.ofReal (c⁻¹ * C_inductPositiveTermsReductionWhitney n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    apply iSup_le
    intro ks
    obtain ⟨q, hq⟩ := aux_mainAuxTwo_chain_to_dyadicChain J hJ ks
    obtain ⟨a, ha, hrestrict⟩ := aux_mainAuxOne_extend_dyadic_chain J hJ q
    have hprefix := aux_leftBumpOneLong_tensor_whitney_prefix hn a ha psi c hc Psi hkernel f J hJ
    simpa only [hq, hrestrict] using hprefix
  calc
    aux_dyadicJumpEnergy (fun x => psi x) f.1 J k ≤
        twistedDyadicVariationEnergy (fun x => psi x) (fun i x => f.1 i x) J := by
      change twistedDyadicJumpEnergy (fun x => psi x) (fun i x => f.1 i x) J k ≤ _
      rw [twistedDyadicVariationEnergy]
      exact le_iSup (fun q : aux_dyadicChain J =>
        twistedDyadicJumpEnergy (fun x => psi x) (fun i x => f.1 i x) J q) k
    _ ≤ 4 * ⨆ ks : {u : Fin J → ℤ // StrictMono u},
        ∑ j, eLpNorm
          (twistedAverageAtScale ((2 : ℝ) ^ (ks.1 j)) (fun x => psi x)
            (fun i x => f.1 i x)) 2 volume ^ 2 :=
      bootstrap hn psi f.1 J
    _ ≤ 4 * (ENNReal.ofReal (c⁻¹ * C_inductPositiveTermsReductionWhitney n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
      simpa [mul_comm] using mul_le_mul_left hsup 4
    _ = ENNReal.ofReal (4 * (c⁻¹ * C_inductPositiveTermsReductionWhitney n)) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring

noncomputable def aux_leftBumpOneLong_data (b : windowBasedBumpFunctions)
    (k : ℤ) (hk : k ≤ -1) (hpsi : phiFourSchwartz b k ≠ 0) :
    WhitneyKernelData :=
  let R : ℝ := (2 : ℝ) ^ (-k)
  let C : ℝ := C_thetaPrimitive 2
  let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
  aux_tensorWhitneyData (phiFourSchwartz b k)
    (aux_leftBumpOneLong_phiFour_support b k)
    c (by
      dsimp [c, C]
      have hC : 0 < C_thetaPrimitive 2 := by
        norm_num [C_thetaPrimitive, C_uniPair]
      apply mul_pos
      · exact inv_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hC))
      · exact Real.rpow_pos_of_pos (by positivity) _)
    hpsi
    (fun m hm xi =>
      aux_leftBumpOneLong_diagonal_bound b k c
        (aux_leftBumpOneLong_c_diagonal_scalar k hk) m hm xi)
    (aux_leftBumpOneLong_data_decay b k hk)

theorem aux_leftBumpOneLong_final_scalar (n : ℕ) (k : ℤ) :
    let R : ℝ := (2 : ℝ) ^ (-k)
    let C : ℝ := C_thetaPrimitive 2
    let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
    4 * (c⁻¹ * C_inductPositiveTermsReductionWhitney n) =
      C_leftBumpOneLong n * Real.rpow 2 ((k : ℝ) / 2) := by
  dsimp
  let R : ℝ := (2 : ℝ) ^ (-k)
  let C : ℝ := C_thetaPrimitive 2
  let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
  change 4 * (c⁻¹ * C_inductPositiveTermsReductionWhitney n) =
    C_leftBumpOneLong n * Real.rpow 2 ((k : ℝ) / 2)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hCpos : 0 < C := by
    dsimp [C]
    norm_num [C_thetaPrimitive, C_uniPair]
  have hcinv : c⁻¹ = 16 * C ^ 2 * Real.rpow R (-(1 / 2 : ℝ)) := by
    dsimp [c]
    rw [mul_inv_rev, ← Real.rpow_neg hRpos.le]
    field_simp [hCpos.ne']
  have hgamma : Real.rpow 2 ((k : ℝ) / 2) =
      Real.rpow ((2 : ℝ) ^ (-k)) (-(1 / 2 : ℝ)) := by
    calc
      Real.rpow 2 ((k : ℝ) / 2) =
          Real.rpow 2 ((((-k : ℤ) : ℝ) * (-(1 / 2 : ℝ)))) := by
        congr 1
        push_cast
        ring
      _ = Real.rpow ((2 : ℝ) ^ (-k)) (-(1 / 2 : ℝ)) := by
        simpa using (Real.rpow_intCast_mul (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
          (-k) (-(1 / 2 : ℝ)))
  rw [hcinv, ← hgamma]
  change 4 * (16 * C ^ 2 * Real.rpow 2 ((k : ℝ) / 2) *
      C_inductPositiveTermsReductionWhitney n) =
    ((2 : ℝ) ^ 6 * C_inductPositiveTermsReductionWhitney n * C ^ 2) *
      Real.rpow 2 ((k : ℝ) / 2)
  norm_num
  ring

/--
**Lemma.**

Let $\gamma=\frac12$. For every $k\le-1$,

$$
\|A_t(\varphi_{4,k})\|_{V_{2,J}(t\in2^\mathbb Z;L^2)}^2
\le C_{\text{lem:leftbump1\_long}}2^{\gamma k}J^{\alpha(n)},
$$

where

$$
C_{\text{lem:leftbump1\_long}}
=2^6C_{\text{induct positive terms - reduction variant, Whitney}}
C_{\text{lem:theta\_prim},2}^2.
$$

See also `Auto.leftBumpOneLong`,
`Auto.inductPositiveTermsReductionWhitney`,
`Auto.thetaPrimitive`.
-/
theorem leftBumpOneLong {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_dyadicVariationBound (C_leftBumpOneLong n * Real.rpow 2 ((k : ℝ) / 2))
      (windowBasedBumpFunctions.phiFour b k) f.1 := by
  classical
  let R : ℝ := (2 : ℝ) ^ (-k)
  let C : ℝ := C_thetaPrimitive 2
  let c : ℝ := (16 * C ^ 2)⁻¹ * Real.rpow R (1 / 2 : ℝ)
  have hc : 0 < c := by
    dsimp [c, C]
    have hC : 0 < C_thetaPrimitive 2 := by
      norm_num [C_thetaPrimitive, C_uniPair]
    apply mul_pos
    · exact inv_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hC))
    · exact Real.rpow_pos_of_pos (by positivity) _
  by_cases hzero : phiFourSchwartz b k = 0
  · have hrawzero : (fun x : ℝ => windowBasedBumpFunctions.phiFour b k x) = 0 := by
      funext x
      rw [← phiFourSchwartz_apply]
      simp [hzero]
    change aux_dyadicVariationBound
      (C_leftBumpOneLong n * Real.rpow 2 ((k : ℝ) / 2))
      (fun x : ℝ => windowBasedBumpFunctions.phiFour b k x) f.1
    rw [hrawzero]
    intro J hJ ell
    simp [aux_dyadicJumpEnergy, twistedDyadicJumpEnergy,
      aux_twistedAverageAtScale, aux_twistedAverage]
  · let Psi : WhitneyKernelData := aux_leftBumpOneLong_data b k hk hzero
    have hkernel : Psi.kernel = fun v => c * tensorSquare (phiFourSchwartz b k) v := by
      dsimp [Psi, aux_leftBumpOneLong_data, c, C, R]
      rfl
    have hdyadic := aux_leftBumpOneLong_tensor_whitney_dyadic hn
      (phiFourSchwartz b k) c hc Psi hkernel f
    have hscalar : 4 * (c⁻¹ * C_inductPositiveTermsReductionWhitney n) =
        C_leftBumpOneLong n * Real.rpow 2 ((k : ℝ) / 2) := by
      simpa [c, C, R] using aux_leftBumpOneLong_final_scalar n k
    rw [hscalar] at hdyadic
    simpa only [phiFourSchwartz_apply] using hdyadic

theorem aux_leftBumpOneLong_whitney_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionWhitney n <
      (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
  unfold C_inductPositiveTermsReductionWhitney
  calc
    11 * C_inductPositiveTermsReductionWhitneyGap n <
        11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553) :=
      mul_lt_mul_of_pos_left (constantWhitneyGapReduction hn) (by norm_num)
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
      calc
        11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553) =
            ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 4) * (2 : ℝ) ^ 553 := by
              norm_num
              set_option exponentiation.threshold 1000 in
                ring
        _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 4 * (2 : ℝ) ^ 553) := by
          set_option exponentiation.threshold 1000 in
            ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by rw [← pow_add]

theorem aux_leftBumpOneLong_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneLong n <
      (1397 / 2048 : ℝ) * (2 : ℝ) ^ 625 := by
  have hW := aux_leftBumpOneLong_whitney_sharp hn
  have hP := (constantThetaPrimitive 2 (by norm_num) (by norm_num [N_uniPair])).2
  have hPnonneg : 0 ≤ C_thetaPrimitive 2 := by
    norm_num [C_thetaPrimitive, C_uniPair]
  have hPpos : 0 < C_thetaPrimitive 2 := by
    norm_num [C_thetaPrimitive, C_uniPair]
  unfold C_leftBumpOneLong
  calc
    (2 : ℝ) ^ 6 * C_inductPositiveTermsReductionWhitney n * C_thetaPrimitive 2 ^ 2 <
      (2 : ℝ) ^ 6 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) * C_thetaPrimitive 2 ^ 2 := by
        gcongr
    _ ≤ (2 : ℝ) ^ 6 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) * ((2 : ℝ) ^ 31) ^ 2 := by
        gcongr
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 625 := by
      rw [show ((2 : ℝ) ^ 31) ^ 2 = (2 : ℝ) ^ 62 by rw [← pow_mul]]
      calc
        (2 : ℝ) ^ 6 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) *
            (2 : ℝ) ^ 62 =
            (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 6 * (2 : ℝ) ^ 557 * (2 : ℝ) ^ 62) := by
              set_option exponentiation.threshold 1000 in
                ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 625 := by
          rw [← pow_add, ← pow_add]

/--
**Lemma (constant $C_{\text{lem:leftbump1\_long}}$).**

$$
C_{\text{lem:leftbump1\_long}}<2^{625}.
$$

See also `Auto.leftBumpOneLong`.
-/
theorem constantLeftBumpOneLong {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneLong n < (2 : ℝ) ^ 625 := by
  calc
    C_leftBumpOneLong n < (1397 / 2048 : ℝ) * (2 : ℝ) ^ 625 :=
      aux_leftBumpOneLong_sharp hn
    _ < (2 : ℝ) ^ 625 := by
      apply mul_lt_of_lt_one_left
      · positivity
      · norm_num

/-- The constant in Lemma `Auto.leftBumpOne`. -/
noncomputable def C_leftBumpOne (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 7 * Real.sqrt (C_leftBumpOneShortOne n) *
      Real.sqrt (C_leftBumpOneShortTwo n) + 2 * C_leftBumpOneLong n

/-- Lemma `Auto.leftBumpOne`. -/
theorem aux_leftBumpOne_logarithmic_setIntegral_rescale (a : ℝ) (ha : 0 < a)
    (g : ℝ → ℝ) :
    (∫ t : ℝ in Set.Icc a (a * 2), |g t| ^ 2 * t⁻¹) =
      ∫ t : ℝ in Set.Icc 1 2, |g (a * t)| ^ 2 * t⁻¹ := by
  let h : ℝ → ℝ := fun u => |g u| ^ 2 * u⁻¹
  have hinterval :
      (∫ t : ℝ in Set.Icc a (a * 2), h t) =
        a * ∫ t : ℝ in Set.Icc 1 2, h (a * t) := by
    have hcomp := intervalIntegral.integral_comp_mul_left h ha.ne'
      (a := (1 : ℝ)) (b := 2)
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by nlinarith)]
    calc
      (∫ t : ℝ in a..a * 2, h t) = a * (a⁻¹ * ∫ t : ℝ in a..a * 2, h t) := by
        field_simp [ha.ne']
      _ = a * ∫ t : ℝ in 1..2, h (a * t) := by
        rw [hcomp]
        simp only [smul_eq_mul]
        ring_nf
      _ = a * ∫ t : ℝ in Set.Icc 1 2, h (a * t) := by
        congr 1
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num)]
  change (∫ t : ℝ in Set.Icc a (a * 2), h t) = _
  rw [hinterval]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [h]
  field_simp [ha.ne']

theorem aux_leftBumpOne_twistedAverageAtScale_contDiffOn {n : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ContDiffOn ℝ 1
      (fun t ↦ twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x)
      (Set.Icc α β) := by
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x
  let b : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (aux_tBump phi) (fun i y ↦ f i y) x
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun u : ℝ ↦ u) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext u
    change SchwartzMap.derivCLM ℝ ℝ psi u = aux_tBump phi u
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  have hdiff : DifferentiableOn ℝ a (Set.Icc α β) := by
    intro t ht
    exact (aux_twistedAverageAtScale_hasDerivAt phi f x t
      (lt_of_lt_of_le hα ht.1)).differentiableAt.differentiableWithinAt
  have hcontb : ContinuousOn b (Set.Icc α β) := by
    have hconttau : ContinuousOn
        (fun t ↦ twistedAverageAtScale t (fun u ↦ tau u) (fun i y ↦ f i y) x)
        (Set.Icc α β) := by
      intro t ht
      exact (aux_twistedAverageAtScale_hasDerivAt tau f x t
        (lt_of_lt_of_le hα ht.1)).continuousAt.continuousWithinAt
    refine hconttau.congr ?_
    intro t ht
    dsimp [b]
    rw [← htau]
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc α β) := by
    exact continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le hα ht.1))
  have hcontg : ContinuousOn (fun t ↦ -t⁻¹ * b t) (Set.Icc α β) := by
    change ContinuousOn ((fun t : ℝ ↦ -(t⁻¹)) * b) (Set.Icc α β)
    exact hinv.neg.mul hcontb
  rw [show (1 : WithTop ℕ∞) = 1 by rfl,
    contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hαβ)]
  refine ⟨hdiff, hcontg.congr ?_⟩
  intro t ht
  exact (aux_twistedAverageAtScale_hasDerivAt phi f x t
    (lt_of_lt_of_le hα ht.1)).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hαβ) t ht)

theorem aux_leftBumpOne_Aphi_lintegral {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (k : ℤ) :
    (∫⁻ t,
      ‖twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ)
        ∂aux_logarithmicMeasure ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun u ↦ phi u)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let α : ℝ := (2 : ℝ) ^ k
  let β : ℝ := (2 : ℝ) ^ (k + 1)
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f i y) x
  let g : ℝ → ℝ := fun t ↦
    twistedAverageAtScale (α * t) (fun u ↦ phi u) (fun i y ↦ f i y) x
  have hα : 0 < α := by
    dsimp [α]
    exact zpow_pos (by norm_num) _
  have hβ : β = α * 2 := by
    dsimp [α, β]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hconta : ContinuousOn a (Set.Icc α β) := by
    intro t ht
    exact (aux_twistedAverageAtScale_hasDerivAt phi f x t
      (lt_of_lt_of_le hα ht.1)).continuousAt.continuousWithinAt
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc α β) :=
    continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le hα ht.1))
  have hleftCont : ContinuousOn (fun t ↦ |a t| ^ 2 * t⁻¹)
      (Set.Icc α β) := by
    change ContinuousOn ((fun t ↦ |a t| ^ 2) * fun t ↦ t⁻¹)
      (Set.Icc α β)
    exact (hconta.abs.pow 2).mul hinv
  have hleftInt : Integrable (fun t ↦ |a t| ^ 2 * t⁻¹)
      (volume.restrict (Set.Icc α β)) := hleftCont.integrableOn_Icc
  have hcontg : ContinuousOn g (Set.Icc (1 : ℝ) 2) := by
    have hscale : ContinuousOn (fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2) :=
      (continuous_const.mul continuous_id).continuousOn
    have hmaps : MapsTo (fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2)
        (Set.Icc α β) := by
      intro t ht
      constructor
      · calc
          α = α * 1 := (mul_one _).symm
          _ ≤ α * t := mul_le_mul_of_nonneg_left ht.1 hα.le
      · calc
          α * t ≤ α * 2 := mul_le_mul_of_nonneg_left ht.2 hα.le
          _ = β := hβ.symm
    change ContinuousOn (a ∘ fun t : ℝ ↦ α * t) (Set.Icc (1 : ℝ) 2)
    exact hconta.comp hscale hmaps
  have hinvOne : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc (1 : ℝ) 2) :=
    continuousOn_id.inv₀ (fun t ht ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hrightCont : ContinuousOn (fun t ↦ |g t| ^ 2 * t⁻¹)
      (Set.Icc (1 : ℝ) 2) := by
    change ContinuousOn ((fun t ↦ |g t| ^ 2) * fun t ↦ t⁻¹)
      (Set.Icc (1 : ℝ) 2)
    exact (hcontg.abs.pow 2).mul hinvOne
  have hrightInt : Integrable (fun t ↦ |g t| ^ 2 * t⁻¹)
      (volume.restrict (Set.Icc (1 : ℝ) 2)) := hrightCont.integrableOn_Icc
  have hFTC :
      (∫ t in Set.Icc α β, |a t| ^ 2 * t⁻¹) =
        ∫ t in Set.Icc (1 : ℝ) 2, |g t| ^ 2 * t⁻¹ := by
    rw [hβ]
    exact aux_leftBumpOne_logarithmic_setIntegral_rescale α hα a
  have hleftNonneg : 0 ≤ᵐ[volume.restrict (Set.Icc α β)]
      fun t ↦ |a t| ^ 2 * t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (lt_of_lt_of_le hα ht.1).le)
  have hrightNonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)]
      fun t ↦ |g t| ^ 2 * t⁻¹ := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (lt_of_lt_of_le zero_lt_one ht.1).le)
  have hleftOfReal := ofReal_integral_eq_lintegral_ofReal hleftInt hleftNonneg
  have hrightOfReal := ofReal_integral_eq_lintegral_ofReal hrightInt hrightNonneg
  have hweightMeas : AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal t⁻¹)
      (volume.restrict (Set.Icc α β)) :=
    (measurable_inv.comp measurable_id).ennreal_ofReal.aemeasurable
  have hweightFinite : ∀ᵐ t : ℝ ∂volume.restrict (Set.Icc α β),
      ENNReal.ofReal t⁻¹ < ∞ :=
    ae_of_all _ fun _ ↦ lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
  have hleftDensity :
      (∫⁻ t, ‖a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β) =
        ∫⁻ t in Set.Icc α β, ENNReal.ofReal (|a t| ^ 2 * t⁻¹) := by
    unfold aux_logarithmicMeasure
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hweightMeas hweightFinite]
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le hα ht.1
    change ENNReal.ofReal t⁻¹ * ‖a t‖ₑ ^ (2 : ℝ) = _
    rw [show ‖a t‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (|a t| ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two,
        Real.rpow_two]]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [ENNReal.ofReal_inv_of_pos htpos]
    ring
  have hrightEnorm :
      (∫⁻ t in Set.Icc (1 : ℝ) 2,
        ENNReal.ofReal (|g t| ^ 2 * t⁻¹)) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2, ‖g t‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    rw [show ENNReal.ofReal (|g t| ^ 2) = ‖g t‖ₑ ^ (2 : ℝ) by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two,
        Real.rpow_two]]
  change (∫⁻ t, ‖a t‖ₑ ^ (2 : ℝ)
      ∂aux_logarithmicMeasure α β) =
    ∫⁻ t in Set.Icc (1 : ℝ) 2, ‖g t‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  rw [hleftDensity, ← hleftOfReal, hFTC, hrightOfReal, hrightEnorm]

theorem aux_leftBumpOne_pointwise_local_product {n : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (J : ℕ) (k : ℤ)
    (u : Fin (J + 1) → aux_dyadicInterval k) (hu : Monotone u) :
    (∑ j : Fin J,
      ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f i y) x -
        twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f i y) x‖ₑ ^
          (2 : ℝ)) ≤
      8 *
        (∫⁻ t in Set.Icc (1 : ℝ) 2,
          ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ phi q)
            (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ^ ((2 : ℝ)⁻¹) *
        (∫⁻ t in Set.Icc (1 : ℝ) 2,
          ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
              (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ^
            ((2 : ℝ)⁻¹) := by
  let α : ℝ := (2 : ℝ) ^ k
  let β : ℝ := (2 : ℝ) ^ (k + 1)
  let a : ℝ → ℝ := fun t ↦
    twistedAverageAtScale t (fun q ↦ phi q) (fun i y ↦ f i y) x
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun q : ℝ ↦ q) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext z
    change SchwartzMap.derivCLM ℝ ℝ psi z = aux_tBump phi z
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  have hα : 0 < α := by
    dsimp [α]
    exact zpow_pos (by norm_num) _
  have hβ : β = α * 2 := by
    dsimp [α, β]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  have hαβ : α < β := by rw [hβ]; nlinarith
  have hcont : ContDiffOn ℝ 1 a (Set.Icc α β) :=
    aux_leftBumpOne_twistedAverageAtScale_contDiffOn phi f x hα hαβ
  let U : {v : Fin (J + 1) → Set.Icc α β // Monotone v} :=
    ⟨fun j ↦ ⟨u j, by simpa only [α, β, aux_dyadicInterval] using (u j).2⟩,
      by
        intro i j hij
        exact hu hij⟩
  have hchain :
      (∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        finiteVariationSeminorm (fun s : Set.Icc α β ↦ a s) 2 J := by
    rw [finiteVariationSeminorm]
    exact le_iSup (fun v : {v : Fin (J + 1) → Set.Icc α β // Monotone v} ↦
      (∑ j : Fin J,
        (‖a (v.1 j.succ) - a (v.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^
          ((2 : ℝ)⁻¹)) U
  have hsquare := ENNReal.rpow_le_rpow hchain (by norm_num : (0 : ℝ) ≤ 2)
  have hleft :
      ((∑ j : Fin J,
        ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)) ^
          (2 : ℝ) =
        ∑ j : Fin J,
          ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hsquare
  have hftc := (ftcCsR J hα hαβ a hcont).2
  have hrawSq : (aux_logarithmicL2 α β a) ^ (2 : ℝ) =
      ∫⁻ t, ‖a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
    unfold aux_logarithmicL2
    simpa [ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := aux_logarithmicMeasure α β)
        (f := a) (p := (2 : NNReal)) (by norm_num : (2 : NNReal) ≠ 0))
  have hrawIntegral :
      (∫⁻ t, ‖a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ phi q)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    simpa only [α, β, a] using aux_leftBumpOne_Aphi_lintegral phi f x k
  have hderivSq :
      (aux_logarithmicL2 α β (fun t ↦ t * deriv a t)) ^ (2 : ℝ) =
      ∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
    unfold aux_logarithmicL2
    simpa [ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := aux_logarithmicMeasure α β)
        (f := fun t ↦ t * deriv a t) (p := (2 : NNReal))
        (by norm_num : (2 : NNReal) ≠ 0))
  have hderivEq (t : ℝ) (ht : t ∈ Set.Icc α β) :
      t * deriv a t = -twistedAverageAtScale t (aux_tBump phi)
        (fun i y ↦ f i y) x := by
    have h := aux_twistedAverageAtScale_hasDerivAt phi f x t
      (lt_of_lt_of_le hα ht.1)
    rw [h.deriv]
    field_simp [ne_of_gt (lt_of_lt_of_le hα ht.1)]
  have hmem : ∀ᵐ t ∂aux_logarithmicMeasure α β, t ∈ Set.Icc α β := by
    unfold aux_logarithmicMeasure
    exact (withDensity_absolutelyContinuous (volume.restrict (Set.Icc α β)) _).ae_le
      (self_mem_ae_restrict measurableSet_Icc)
  have hderivLog :
      (∫⁻ t, ‖t * deriv a t‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β) =
      ∫⁻ t, ‖twistedAverageAtScale t (fun q ↦ tau q) (fun i y ↦ f i y) x‖ₑ ^
        (2 : ℝ) ∂aux_logarithmicMeasure α β := by
    apply lintegral_congr_ae
    filter_upwards [hmem] with t ht
    rw [hderivEq t ht, ← htau]
    simp
  have htauIntegral :
      (∫⁻ t, ‖twistedAverageAtScale t (fun q ↦ tau q) (fun i y ↦ f i y) x‖ₑ ^
          (2 : ℝ) ∂aux_logarithmicMeasure α β) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
    rw [← htau]
    simpa only [α, β] using aux_leftBumpOne_Aphi_lintegral tau f x k
  have hrawRoot : aux_logarithmicL2 α β a =
      (∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ phi q)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ^ ((2 : ℝ)⁻¹) := by
    calc
      aux_logarithmicL2 α β a = (aux_logarithmicL2 α β a ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ = _ := by rw [hrawSq, hrawIntegral]
  have hderivRoot : aux_logarithmicL2 α β (fun t ↦ t * deriv a t) =
      (∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (aux_tBump phi)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ^ ((2 : ℝ)⁻¹) := by
    calc
      aux_logarithmicL2 α β (fun t ↦ t * deriv a t) =
          (aux_logarithmicL2 α β (fun t ↦ t * deriv a t) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ = _ := by rw [hderivSq, hderivLog, htauIntegral]
  calc
    (∑ j : Fin J,
      ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f i y) x -
        twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f i y) x‖ₑ ^
          (2 : ℝ)) =
        ∑ j : Fin J,
          ‖a (U.1 j.succ) - a (U.1 j.castSucc)‖ₑ ^ (2 : ℝ) := by
      congr 2 with j
    _ ≤ (finiteVariationSeminorm (fun s : Set.Icc α β ↦ a s) 2 J) ^ (2 : ℝ) := hsquare
    _ ≤ 8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := hftc
    _ = _ := by rw [hrawRoot, hderivRoot]

noncomputable def aux_leftBumpOne_scaleKernel
    (phi : SchwartzMap ℝ ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s ↦ t⁻¹ * phi (t⁻¹ * s)

theorem aux_leftBumpOne_scaleKernel_memLp (phi : SchwartzMap ℝ ℝ) (t : ℝ) :
    MemLp (aux_leftBumpOne_scaleKernel phi t) 2 volume := by
  by_cases ht : t = 0
  · subst t
    have : aux_leftBumpOne_scaleKernel phi 0 = 0 := by
      funext s
      simp [aux_leftBumpOne_scaleKernel]
    rw [this]
    exact MemLp.zero
  · have hmeas : AEStronglyMeasurable (aux_leftBumpOne_scaleKernel phi t) volume := by
      change AEStronglyMeasurable (fun s : ℝ ↦ t⁻¹ * phi (t⁻¹ * s)) (volume : Measure ℝ)
      exact (continuous_const.mul
        (phi.continuous.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hmeas).mpr
    have hsq : Integrable (fun s : ℝ ↦ phi s ^ 2) (volume : Measure ℝ) :=
      (phi.memLp 2).integrable_sq
    have hrescale : Integrable (fun s : ℝ ↦
        t⁻¹ ^ 2 * phi (t⁻¹ * s) ^ 2) (volume : Measure ℝ) :=
      (hsq.comp_mul_left' (inv_ne_zero ht)).const_mul (t⁻¹ ^ 2)
    have heq : (fun s : ℝ ↦ aux_leftBumpOne_scaleKernel phi t s ^ 2) =
        fun s ↦ t⁻¹ ^ 2 * phi (t⁻¹ * s) ^ 2 := by
      funext s
      dsimp [aux_leftBumpOne_scaleKernel]
      ring
    rw [heq]
    exact hrescale

noncomputable def aux_leftBumpOne_averageLp {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (t : ℝ) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (aux_twistedAverage_memLp hn f.1 (aux_leftBumpOne_scaleKernel phi t)
    (aux_leftBumpOne_scaleKernel_memLp phi t)).toLp _

theorem aux_leftBumpOne_averageLp_enorm_sub {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (s t : ℝ) :
    (‖aux_leftBumpOne_averageLp hn phi f s -
        aux_leftBumpOne_averageLp hn phi f t‖₊ : ℝ≥0∞) =
      eLpNorm
        (fun x ↦ twistedAverageAtScale s (fun u ↦ phi u) (fun i y ↦ f.1 i y) x -
          twistedAverageAtScale t (fun u ↦ phi u) (fun i y ↦ f.1 i y) x)
        2 volume := by
  let hs := aux_twistedAverage_memLp hn f.1 (aux_leftBumpOne_scaleKernel phi s)
    (aux_leftBumpOne_scaleKernel_memLp phi s)
  let ht := aux_twistedAverage_memLp hn f.1 (aux_leftBumpOne_scaleKernel phi t)
    (aux_leftBumpOne_scaleKernel_memLp phi t)
  change ‖hs.toLp _ - ht.toLp _‖ₑ = _
  rw [← hs.toLp_sub ht]
  rw [Lp.enorm_toLp]
  rfl

theorem aux_leftBumpOne_lp_chain_energy_eq_lintegral {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (k : ℤ)
    (u : Fin (J + 1) → aux_dyadicInterval k) (_hu : Monotone u) :
    (∑ j : Fin J,
      ‖aux_leftBumpOne_averageLp hn phi f (u j.succ) -
        aux_leftBumpOne_averageLp hn phi f (u j.castSucc)‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x,
        ∑ j : Fin J,
          ‖twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q)
              (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) := by
  let g : Fin J → EuclideanSpace ℝ (Fin n) → ℝ := fun j x ↦
    twistedAverageAtScale (u j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
      twistedAverageAtScale (u j.castSucc) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x
  have hmem (j : Fin J) : MemLp (g j) 2 volume := by
    let hs := aux_twistedAverage_memLp hn f.1 (aux_leftBumpOne_scaleKernel phi (u j.succ))
      (aux_leftBumpOne_scaleKernel_memLp phi (u j.succ))
    let ht := aux_twistedAverage_memLp hn f.1 (aux_leftBumpOne_scaleKernel phi (u j.castSucc))
      (aux_leftBumpOne_scaleKernel_memLp phi (u j.castSucc))
    change MemLp
      (twistedAverage (aux_leftBumpOne_scaleKernel phi (u j.succ)) (fun i y ↦ f.1 i y) -
        twistedAverage (aux_leftBumpOne_scaleKernel phi (u j.castSucc))
          (fun i y ↦ f.1 i y)) 2 volume
    exact hs.sub ht
  have hmeas (j : Fin J) : AEMeasurable (fun x ↦ ‖g j x‖ₑ ^ (2 : ℝ)) volume :=
    (hmem j).aestronglyMeasurable.enorm.pow_const _
  calc
    (∑ j : Fin J,
      ‖aux_leftBumpOne_averageLp hn phi f (u j.succ) -
        aux_leftBumpOne_averageLp hn phi f (u j.castSucc)‖ₑ ^ (2 : ℝ)) =
        ∑ j : Fin J, eLpNorm (g j) 2 volume ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℝ))
        (aux_leftBumpOne_averageLp_enorm_sub hn phi f (u j.succ) (u j.castSucc))
    _ = ∑ j : Fin J, ∫⁻ x, ‖g j x‖ₑ ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := g j)
        (p := (2 : NNReal)) (by norm_num)
    _ = ∫⁻ x, ∑ j : Fin J, ‖g j x‖ₑ ^ (2 : ℝ) := by
      simpa using (lintegral_finsetSum' (μ := volume) Finset.univ
        (f := fun j x ↦ ‖g j x‖ₑ ^ (2 : ℝ)) (fun j _ ↦ hmeas j)).symm

theorem aux_leftBumpOne_joint_measurable_twistedAverageAtScale {n : ℕ}
    (psi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (α : ℝ) :
    StronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      twistedAverageAtScale (α * tx.1) (fun u ↦ psi u) (fun i y ↦ f i y) tx.2) := by
  let F : ((ℝ × EuclideanSpace ℝ (Fin n)) × ℝ) → ℝ := fun z ↦
    (α * z.1.1)⁻¹ * psi ((α * z.1.1)⁻¹ * z.2) *
      ∏ i, f i (z.1.2 + z.2 • WithLp.toLp 2 (Pi.single i (1 : ℝ)))
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  have hInt : StronglyMeasurable (fun tx : ℝ × EuclideanSpace ℝ (Fin n) ↦
      ∫ s : ℝ, F (tx, s) ∂(volume : Measure ℝ)) :=
    hF.stronglyMeasurable.integral_prod_right' (ν := volume)
  simpa only [F, aux_twistedAverageAtScale, aux_twistedAverage] using hInt

theorem aux_leftBumpOne_energy_inner_aemeasurable {n : ℕ}
    (psi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (k : ℤ) :
    AEMeasurable (fun x ↦
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) volume := by
  let H : EuclideanSpace ℝ (Fin n) → ℝ → ℝ≥0∞ := fun x t ↦
    ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
      (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  have hjoint : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
        twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ psi q)
          (fun i y ↦ f i y) z.1)
      (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
    exact (aux_leftBumpOne_joint_measurable_twistedAverageAtScale psi f ((2 : ℝ) ^ k)
      |>.comp_measurable measurable_swap).aestronglyMeasurable
  have hHmeas : AEMeasurable (Function.uncurry H)
      (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
    have hweight : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦ ENNReal.ofReal z.2⁻¹)
        (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) :=
      ((measurable_inv.comp measurable_snd).ennreal_ofReal).aemeasurable
    change AEMeasurable
      ((fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ psi q)
          (fun i y ↦ f i y) z.1‖ₑ ^ (2 : ℝ)) *
        fun z ↦ ENNReal.ofReal z.2⁻¹) _
    exact (hjoint.enorm.pow_const _).mul hweight
  simpa only [H] using hHmeas.lintegral_prod_right

theorem aux_leftBumpOne_energy_tonelli {n : ℕ}
    (psi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (k : ℤ) :
    (∫⁻ x,
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
          (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) =
      ∫⁻ t in Set.Icc (1 : ℝ) 2,
        eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
          (fun i y ↦ f i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹ := by
  let H : EuclideanSpace ℝ (Fin n) → ℝ → ℝ≥0∞ := fun x t ↦
    ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
      (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  have hjoint : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
        twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ psi q)
          (fun i y ↦ f i y) z.1)
      (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
    exact (aux_leftBumpOne_joint_measurable_twistedAverageAtScale psi f ((2 : ℝ) ^ k)
      |>.comp_measurable measurable_swap).aestronglyMeasurable
  have hHmeas : AEMeasurable (Function.uncurry H)
      (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) := by
    have hweight : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦ ENNReal.ofReal z.2⁻¹)
        (volume.prod (volume.restrict (Set.Icc (1 : ℝ) 2))) :=
      ((measurable_inv.comp measurable_snd).ennreal_ofReal).aemeasurable
    change AEMeasurable
      ((fun z : EuclideanSpace ℝ (Fin n) × ℝ ↦
        ‖twistedAverageAtScale ((2 : ℝ) ^ k * z.2) (fun q ↦ psi q)
          (fun i y ↦ f i y) z.1‖ₑ ^ (2 : ℝ)) *
        fun z ↦ ENNReal.ofReal z.2⁻¹) _
    exact (hjoint.enorm.pow_const _).mul hweight
  have hswap := lintegral_lintegral_swap hHmeas
  rw [show (fun x ↦ ∫⁻ t in Set.Icc (1 : ℝ) 2,
      ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
        (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) =
      fun x ↦ ∫⁻ t in Set.Icc (1 : ℝ) 2, H x t by rfl]
  rw [hswap]
  change (∫⁻ t in Set.Icc (1 : ℝ) 2,
    ∫⁻ x, ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
      (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) = _
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
  rw [lintegral_mul_const' (ENNReal.ofReal t⁻¹)
    (fun x ↦ ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
      (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ)) ENNReal.ofReal_ne_top]
  have hnorm : eLpNorm
      (fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
        (fun i y ↦ f i y) x) 2 volume ^ (2 : ℝ) =
      ∫⁻ x, ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
        (fun i y ↦ f i y) x‖ₑ ^ (2 : ℝ) := by
    simpa [ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := volume)
        (f := fun x ↦ twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ psi q)
          (fun i y ↦ f i y) x) (p := (2 : NNReal)) (by norm_num))
  rw [← hnorm]

theorem aux_leftBumpOne_lintegral_sqrt_mul_sqrt_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p q : α → ℝ≥0∞)
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ) :
    (∫⁻ x, p x ^ ((2 : ℝ)⁻¹) * q x ^ ((2 : ℝ)⁻¹) ∂μ) ≤
      (∫⁻ x, p x ∂μ) ^ ((2 : ℝ)⁻¹) *
        (∫⁻ x, q x ∂μ) ^ ((2 : ℝ)⁻¹) := by
  have h := ENNReal.lintegral_mul_norm_pow_le hp hq
    (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)
  simpa using h

theorem aux_leftBumpOne_local_variation_product {n : ℕ} (hn : 2 ≤ n)
    (phi tau : SchwartzMap ℝ ℝ) (htau : (tau : ℝ → ℝ) = aux_tBump phi)
    (f : ReductionNormalizedTuple n) (J : ℕ) (k : ℤ) :
    (finiteVariationSeminorm
      (fun s : aux_dyadicInterval k ↦
        aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      8 *
        (∫⁻ t in Set.Icc (1 : ℝ) 2,
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ phi q)
            (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ^
          ((2 : ℝ)⁻¹) *
        (∫⁻ t in Set.Icc (1 : ℝ) 2,
          eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
            (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹) ^
          ((2 : ℝ)⁻¹) := by
  let P : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x ↦
    ∫⁻ t in Set.Icc (1 : ℝ) 2,
      ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ phi q)
        (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  let Q : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x ↦
    ∫⁻ t in Set.Icc (1 : ℝ) 2,
      ‖twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
        (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  let Rphi : ℝ≥0∞ := ∫⁻ t in Set.Icc (1 : ℝ) 2,
    eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ phi q)
      (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  let Rtau : ℝ≥0∞ := ∫⁻ t in Set.Icc (1 : ℝ) 2,
    eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ k * t) (fun q ↦ tau q)
      (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  have hPmeas : AEMeasurable P volume := by
    simpa only [P] using aux_leftBumpOne_energy_inner_aemeasurable phi f.1 k
  have hQmeas : AEMeasurable Q volume := by
    simpa only [Q] using aux_leftBumpOne_energy_inner_aemeasurable tau f.1 k
  have hPtonelli : (∫⁻ x, P x) = Rphi := by
    simpa only [P, Rphi] using aux_leftBumpOne_energy_tonelli phi f.1 k
  have hQtonelli : (∫⁻ x, Q x) = Rtau := by
    simpa only [Q, Rtau] using aux_leftBumpOne_energy_tonelli tau f.1 k
  have hholder := aux_leftBumpOne_lintegral_sqrt_mul_sqrt_le volume P Q hPmeas hQmeas
  have hchain (u : {v : Fin (J + 1) → aux_dyadicInterval k // Monotone v}) :
      (∑ j : Fin J,
        ‖aux_leftBumpOne_averageLp hn phi f (u.1 j.succ) -
          aux_leftBumpOne_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ≤
        8 * Rphi ^ ((2 : ℝ)⁻¹) * Rtau ^ ((2 : ℝ)⁻¹) := by
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        (∑ j : Fin J,
          ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q) (fun i y ↦ f.1 i y) x -
            twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
              (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ≤
          8 * (P x ^ ((2 : ℝ)⁻¹) * Q x ^ ((2 : ℝ)⁻¹)) := by
      have h := aux_leftBumpOne_pointwise_local_product phi f.1 x J k u.1 u.2
      rw [← htau] at h
      simpa only [P, Q, mul_assoc] using h
    have hpointInt :
        (∫⁻ x,
          ∑ j : Fin J,
            ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q)
                (fun i y ↦ f.1 i y) x -
              twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
                (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ)) ≤
          ∫⁻ x, 8 * (P x ^ ((2 : ℝ)⁻¹) * Q x ^ ((2 : ℝ)⁻¹)) := by
      apply lintegral_mono
      exact hpoint
    calc
      (∑ j : Fin J,
        ‖aux_leftBumpOne_averageLp hn phi f (u.1 j.succ) -
          aux_leftBumpOne_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
          ∫⁻ x,
            ∑ j : Fin J,
              ‖twistedAverageAtScale (u.1 j.succ) (fun q ↦ phi q)
                  (fun i y ↦ f.1 i y) x -
                twistedAverageAtScale (u.1 j.castSucc) (fun q ↦ phi q)
                  (fun i y ↦ f.1 i y) x‖ₑ ^ (2 : ℝ) :=
        aux_leftBumpOne_lp_chain_energy_eq_lintegral hn phi f J k u.1 u.2
      _ ≤ ∫⁻ x, 8 * (P x ^ ((2 : ℝ)⁻¹) * Q x ^ ((2 : ℝ)⁻¹)) := hpointInt
      _ = 8 * ∫⁻ x, P x ^ ((2 : ℝ)⁻¹) * Q x ^ ((2 : ℝ)⁻¹) := by
        rw [lintegral_const_mul' 8 _ (by norm_num)]
      _ ≤ 8 * ((∫⁻ x, P x) ^ ((2 : ℝ)⁻¹) *
          (∫⁻ x, Q x) ^ ((2 : ℝ)⁻¹)) := by gcongr
      _ = 8 * Rphi ^ ((2 : ℝ)⁻¹) * Rtau ^ ((2 : ℝ)⁻¹) := by
        rw [hPtonelli, hQtonelli]
        ring
  have hroot : finiteVariationSeminorm
      (fun s : aux_dyadicInterval k ↦ aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J ≤
      (8 * Rphi ^ ((2 : ℝ)⁻¹) * Rtau ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro u
    have h := ENNReal.rpow_le_rpow (hchain u) (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    simpa only [← enorm_eq_nnnorm] using h
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hright :
      ((8 * Rphi ^ ((2 : ℝ)⁻¹) * Rtau ^ ((2 : ℝ)⁻¹)) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) =
        8 * Rphi ^ ((2 : ℝ)⁻¹) * Rtau ^ ((2 : ℝ)⁻¹) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hright] at hsquare
  exact hsquare

theorem aux_leftBumpOne_weighted_energy_bound
    (u v w C D P X Y : ℝ≥0∞)
    (hu0 : u ≠ 0) (hutop : u ≠ ∞) (hv0 : v ≠ 0) (hvtop : v ≠ ∞)
    (hweight : u⁻¹ ^ ((2 : ℝ)⁻¹) * v⁻¹ ^ ((2 : ℝ)⁻¹) = w)
    (hX : u * X ≤ 2 * C * P) (hY : v * Y ≤ 2 * D * P) :
    8 * X ^ ((2 : ℝ)⁻¹) * Y ^ ((2 : ℝ)⁻¹) ≤
      16 * w * C ^ ((2 : ℝ)⁻¹) * D ^ ((2 : ℝ)⁻¹) * P := by
  let h : ℝ := (2 : ℝ)⁻¹
  have hh : 0 ≤ h := by dsimp [h]; norm_num
  have huhr0 : u ^ h ≠ 0 := by
    intro hz
    rcases (ENNReal.rpow_eq_zero_iff.mp hz) with hz | hz
    · exact hu0 hz.1
    · exact hutop hz.1
  have huhrtop : u ^ h ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hh hutop
  have hvhr0 : v ^ h ≠ 0 := by
    intro hz
    rcases (ENNReal.rpow_eq_zero_iff.mp hz) with hz | hz
    · exact hv0 hz.1
    · exact hvtop hz.1
  have hvhrtop : v ^ h ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hh hvtop
  have hXroot : (u * X) ^ h ≤ (2 * C * P) ^ h :=
    ENNReal.rpow_le_rpow hX hh
  have hYroot : (v * Y) ^ h ≤ (2 * D * P) ^ h :=
    ENNReal.rpow_le_rpow hY hh
  have hprod : (u * X) ^ h * (v * Y) ^ h ≤
      (2 * C * P) ^ h * (2 * D * P) ^ h :=
    mul_le_mul hXroot hYroot bot_le bot_le
  have hsplitX : X ^ h = u⁻¹ ^ h * (u * X) ^ h := by
    rw [ENNReal.inv_rpow, ENNReal.mul_rpow_of_nonneg _ _ hh]
    rw [← mul_assoc, ENNReal.inv_mul_cancel huhr0 huhrtop, one_mul]
  have hsplitY : Y ^ h = v⁻¹ ^ h * (v * Y) ^ h := by
    rw [ENNReal.inv_rpow, ENNReal.mul_rpow_of_nonneg _ _ hh]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hvhr0 hvhrtop, one_mul]
  have hpowTwo : (2 : ℝ≥0∞) ^ h * 2 ^ h = 2 := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hh hh]
    dsimp [h]
    norm_num
  have hpowP : P ^ h * P ^ h = P := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ hh hh]
    dsimp [h]
    norm_num
  calc
    8 * X ^ h * Y ^ h =
        8 * (u⁻¹ ^ h * v⁻¹ ^ h) * ((u * X) ^ h * (v * Y) ^ h) := by
      rw [hsplitX, hsplitY]
      ring
    _ ≤ 8 * (u⁻¹ ^ h * v⁻¹ ^ h) *
        ((2 * C * P) ^ h * (2 * D * P) ^ h) := by
      gcongr
    _ = 16 * w * C ^ h * D ^ h * P := by
      rw [hweight]
      repeat' rw [ENNReal.mul_rpow_of_nonneg _ _ hh]
      calc
        8 * w * (2 ^ h * C ^ h * P ^ h * (2 ^ h * D ^ h * P ^ h)) =
            8 * w * ((2 ^ h * 2 ^ h) * C ^ h * D ^ h * (P ^ h * P ^ h)) := by ring
        _ = 16 * w * C ^ h * D ^ h * P := by
          rw [hpowTwo, hpowP]
          ring

theorem aux_leftBumpOne_leftBumpOne_weight_identity (k : ℤ) :
    (ENNReal.ofReal (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)))⁻¹ ^ ((2 : ℝ)⁻¹) *
      (ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)))⁻¹ ^ ((2 : ℝ)⁻¹) =
        ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)) := by
  let a : ℝ := -(3 : ℝ) * (k : ℝ) / 2
  let b : ℝ := (k : ℝ) / 2
  have htwo : (ENNReal.ofReal (2 : ℝ)) ≠ 0 := by norm_num
  have htwo_top : (ENNReal.ofReal (2 : ℝ)) ≠ ∞ := by norm_num
  change (ENNReal.ofReal (Real.rpow 2 a))⁻¹ ^ ((2 : ℝ)⁻¹) *
      (ENNReal.ofReal (Real.rpow 2 b))⁻¹ ^ ((2 : ℝ)⁻¹) =
        ENNReal.ofReal (Real.rpow 2 b)
  have ha : ENNReal.ofReal (Real.rpow 2 a) = (ENNReal.ofReal (2 : ℝ)) ^ a :=
    (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  have hb : ENNReal.ofReal (Real.rpow 2 b) = (ENNReal.ofReal (2 : ℝ)) ^ b :=
    (ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)).symm
  rw [ha, hb,
    ← ENNReal.rpow_neg, ← ENNReal.rpow_neg,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_add _ _ htwo htwo_top]
  congr 1
  dsimp [a, b]
  ring

theorem aux_leftBumpOne_leftBumpOne_weight_nonzero (k : ℤ) :
    ENNReal.ofReal (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)) ≠ 0 := by
  exact ENNReal.ofReal_ne_zero_iff.mpr
    (Real.rpow_pos_of_pos (by norm_num) _)

theorem aux_leftBumpOne_leftBumpOne_weight_not_top (k : ℤ) :
    ENNReal.ofReal (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2)) ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem aux_leftBumpOne_leftBumpOne_Tweight_nonzero (k : ℤ) :
    ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)) ≠ 0 := by
  exact ENNReal.ofReal_ne_zero_iff.mpr
    (Real.rpow_pos_of_pos (by norm_num) _)

theorem aux_leftBumpOne_leftBumpOne_Tweight_not_top (k : ℤ) :
    ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)) ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem aux_leftBumpOne_finset_sqrt_mul_sqrt_le {ι : Type*} (κ : Finset ι)
    (p q : ι → ℝ≥0∞) :
    (∑ i ∈ κ, p i ^ ((2 : ℝ)⁻¹) * q i ^ ((2 : ℝ)⁻¹)) ≤
      (∑ i ∈ κ, p i) ^ ((2 : ℝ)⁻¹) *
        (∑ i ∈ κ, q i) ^ ((2 : ℝ)⁻¹) := by
  classical
  let : MeasurableSpace κ := ⊤
  let p' : κ → ℝ≥0∞ := fun i ↦ p i
  let q' : κ → ℝ≥0∞ := fun i ↦ q i
  have hp : AEMeasurable p' Measure.count := Measurable.aemeasurable (by fun_prop)
  have hq : AEMeasurable q' Measure.count := Measurable.aemeasurable (by fun_prop)
  have h := aux_leftBumpOne_lintegral_sqrt_mul_sqrt_le Measure.count p' q' hp hq
  simpa only [p', q', lintegral_count, tsum_fintype,
    ← Finset.sum_coe_sort κ (fun i ↦ p i ^ ((2 : ℝ)⁻¹) * q i ^ ((2 : ℝ)⁻¹)),
    ← Finset.sum_coe_sort κ p, ← Finset.sum_coe_sort κ q] using h

theorem aux_leftBumpOne_dyadic_index_unique {x : ℝ} {k l : ℤ}
    (hk : (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1))
    (hl : (2 : ℝ) ^ l ≤ x ∧ x < (2 : ℝ) ^ (l + 1)) :
    k = l := by
  apply le_antisymm
  · by_contra hnot
    have hlt : l < k := lt_of_not_ge hnot
    have hstep : l + 1 ≤ k := Int.add_one_le_iff.mpr hlt
    have hp : (2 : ℝ) ^ (l + 1) ≤ (2 : ℝ) ^ k :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hstep
    exact (not_lt_of_ge (hp.trans hk.1)) hl.2
  · by_contra hnot
    have hlt : k < l := lt_of_not_ge hnot
    have hstep : k + 1 ≤ l := Int.add_one_le_iff.mpr hlt
    have hp : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ l :=
      (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hstep
    exact (not_lt_of_ge (hp.trans hl.1)) hk.2

theorem aux_leftBumpOne_kappa_card_le {J : ℕ}
    (t : Fin (J + 1) → ℝ) (_htpos : ∀ j, 0 < t j)
    (kappa : Finset ℤ)
    (hkappa : ∀ k, k ∈ kappa ↔ ∃ j,
      (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) :
    kappa.card ≤ J + 1 := by
  classical
  choose q hq using fun k : kappa => (hkappa k).mp k.property
  have hqin : Function.Injective q := by
    intro k l hkl
    apply Subtype.ext
    apply aux_leftBumpOne_dyadic_index_unique (x := t (q k)) (k := (k : ℤ)) (l := (l : ℤ))
    · exact hq k
    · simpa [hkl] using hq l
  simpa using Fintype.card_le_of_injective q hqin

theorem aux_leftBumpOne_finset_sum_as_dyadic_chain (kappa : Finset ℤ)
    (hkappa : kappa.Nonempty) :
    ∃ (K : ℕ) (_ : 0 < K) (_ : K = kappa.card) (q : aux_dyadicChain K),
      ∀ F : ℤ → ℝ≥0∞,
        (∑ k ∈ kappa, F k) = ∑ j : Fin K, F (q.1 j.castSucc) := by
  classical
  obtain ⟨M, hcard⟩ : ∃ M : ℕ, kappa.card = M + 1 := by
    have hpos : 0 < kappa.card := Finset.card_pos.mpr hkappa
    refine ⟨kappa.card - 1, ?_⟩
    omega
  let e : Fin (M + 1) ↪o ℤ := kappa.orderEmbOfFin hcard
  let qfun : Fin (M + 2) → ℤ :=
    Fin.lastCases (e (Fin.last M) + 1) e
  have hqfun : StrictMono qfun := by
    intro i j hij
    by_cases hj : j = Fin.last (M + 1)
    · subst j
      change i.1 < M + 1 at hij
      let i' : Fin (M + 1) := ⟨i.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      rw [hi]
      simp only [qfun, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hle : e i' ≤ e (Fin.last M) := e.monotone (Fin.le_last i')
      omega
    · have hjlt : j < Fin.last (M + 1) := Fin.lt_last_iff_ne_last.mpr hj
      change i.1 < j.1 at hij
      change j.1 < M + 1 at hjlt
      let i' : Fin (M + 1) := ⟨i.1, by omega⟩
      let j' : Fin (M + 1) := ⟨j.1, by omega⟩
      have hi : i = i'.castSucc := by rfl
      have hj' : j = j'.castSucc := by rfl
      rw [hi, hj']
      simp only [qfun, Fin.lastCases_castSucc]
      apply e.strictMono
      simpa [i', j'] using hij
  let q : aux_dyadicChain (M + 1) := ⟨qfun, hqfun⟩
  refine ⟨M + 1, Nat.zero_lt_succ _, hcard.symm, q, ?_⟩
  intro F
  let e' : Fin (M + 1) → kappa := fun i ↦
    ⟨e i, Finset.orderEmbOfFin_mem kappa hcard i⟩
  have he'inj : Function.Injective e' := by
    intro i j hij
    apply e.injective
    exact congrArg Subtype.val hij
  have he'bij : Function.Bijective e' := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨he'inj, ?_⟩
    simp [hcard]
  let equiv : Fin (M + 1) ≃ kappa := Equiv.ofBijective e' he'bij
  calc
    (∑ k ∈ kappa, F k) = ∑ k : kappa, F k := (Finset.sum_coe_sort kappa F).symm
    _ = ∑ j : Fin (M + 1), F (equiv j) := by
      exact (Equiv.sum_comp equiv (fun k : kappa ↦ F k)).symm
    _ = ∑ j : Fin (M + 1), F (q.1 j.castSucc) := by
      apply Finset.sum_congr rfl
      intro j _
      change F (e j) = F (qfun j.castSucc)
      simp [qfun]

theorem aux_leftBumpOne_card_power_bound {n J K : ℕ} (hn : 2 ≤ n) (hJ : 0 < J)
    (hK : K ≤ J + 1) :
    ENNReal.ofReal ((K : ℝ) ^ variationExponent n) ≤
      2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  have hexpNonneg : 0 ≤ variationExponent n := by
    unfold variationExponent
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    linarith
  have hexpLeOne : variationExponent n ≤ 1 := by
    unfold variationExponent
    have hpow : 0 ≤ (2 : ℝ) ^ (-(n : ℝ) + 2) :=
      Real.rpow_nonneg (by norm_num) _
    linarith
  have hKreal : (K : ℝ) ≤ 2 * J := by
    have hKJ : (K : ℝ) ≤ J + 1 := by exact_mod_cast hK
    have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hpow : (K : ℝ) ^ variationExponent n ≤
      2 * (J : ℝ) ^ variationExponent n := by
    calc
      (K : ℝ) ^ variationExponent n ≤ (2 * J : ℝ) ^ variationExponent n :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hKreal hexpNonneg
      _ = (2 : ℝ) ^ variationExponent n * (J : ℝ) ^ variationExponent n :=
        Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * (J : ℝ) ^ variationExponent n := by
        have htwo : (2 : ℝ) ^ variationExponent n ≤ 2 := by
          calc
            (2 : ℝ) ^ variationExponent n ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpLeOne
            _ = 2 := by norm_num
        gcongr
  calc
    ENNReal.ofReal ((K : ℝ) ^ variationExponent n) ≤
        ENNReal.ofReal (2 * (J : ℝ) ^ variationExponent n) :=
      ENNReal.ofReal_le_ofReal hpow
    _ = 2 * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

theorem aux_leftBumpOne_ofReal_sqrt_rpow_product (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (k : ℤ) :
    ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)) *
        ENNReal.ofReal C ^ ((2 : ℝ)⁻¹) * ENNReal.ofReal D ^ ((2 : ℝ)⁻¹) =
      ENNReal.ofReal
        (Real.sqrt C * Real.sqrt D * Real.rpow 2 ((k : ℝ) / 2)) := by
  have hhalf : 0 ≤ (2 : ℝ)⁻¹ := by norm_num
  rw [ENNReal.ofReal_rpow_of_nonneg hC hhalf,
    ENNReal.ofReal_rpow_of_nonneg hD hhalf]
  have hCsqrt : C ^ ((2 : ℝ)⁻¹) = Real.sqrt C := by
    convert (Real.sqrt_eq_rpow C).symm using 1; norm_num
  have hDsqrt : D ^ ((2 : ℝ)⁻¹) = Real.sqrt D := by
    convert (Real.sqrt_eq_rpow D).symm using 1; norm_num
  rw [hCsqrt, hDsqrt]
  have hsC : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hsD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hkpow : 0 ≤ Real.rpow 2 ((k : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2)) * ENNReal.ofReal (Real.sqrt C) *
        ENNReal.ofReal (Real.sqrt D) =
        ENNReal.ofReal
          (Real.rpow 2 ((k : ℝ) / 2) * Real.sqrt C * Real.sqrt D) := by
          rw [← ENNReal.ofReal_mul hkpow,
            ← ENNReal.ofReal_mul (mul_nonneg hkpow hsC)]
    _ = ENNReal.ofReal
          (Real.sqrt C * Real.sqrt D * Real.rpow 2 ((k : ℝ) / 2)) := by
          congr 1
          ring

theorem aux_leftBumpOne_whitney_nonneg (n : ℕ) :
    0 ≤ C_inductPositiveTermsReductionWhitney n := by
  have hdiagonal : 0 ≤ C_diagonalBandReduction := by
    unfold C_diagonalBandReduction
    exact add_nonneg
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) aux_CincreaseDataReduction_nonneg)
  have hnonWhitney : 0 ≤ C_inductPositiveTermsReductionNonWhitney := by
    unfold C_inductPositiveTermsReductionNonWhitney
    apply add_nonneg
    · norm_num [C_oneScaleEstimateWindow, Auto.C_uniPair]
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) hdiagonal
  have hskip : 0 ≤ C_inductPositiveTermsReductionNonWhitneySkip n := by
    unfold C_inductPositiveTermsReductionNonWhitneySkip
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) hnonWhitney
  have hgap : 0 ≤ C_inductPositiveTermsReductionWhitneyGap n := by
    unfold C_inductPositiveTermsReductionWhitneyGap
    exact add_nonneg (mul_nonneg (by norm_num) hskip)
      (mul_nonneg (mul_nonneg (by positivity) (add_nonneg (sq_nonneg _)
        (sq_nonneg _))) hdiagonal)
  unfold C_inductPositiveTermsReductionWhitney
  exact mul_nonneg (by norm_num) hgap

theorem aux_leftBumpOne_short_one_nonneg (n : ℕ) : 0 ≤ C_leftBumpOneShortOne n := by
  unfold C_leftBumpOneShortOne
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (aux_leftBumpOne_whitney_nonneg n)) (sq_nonneg _))
    (by norm_num [C_thetaTOffcenter])

theorem aux_leftBumpOne_short_two_aux_nonneg : 0 ≤ C_leftBumpOneShortTwoAuxiliary := by
  unfold C_leftBumpOneShortTwoAuxiliary
  exact le_max_of_le_left (by norm_num [C_thetaPrimitive, Auto.C_uniPair])

theorem aux_leftBumpOne_short_two_nonneg (n : ℕ) : 0 ≤ C_leftBumpOneShortTwo n := by
  unfold C_leftBumpOneShortTwo
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (aux_leftBumpOne_whitney_nonneg n))
    (by norm_num [C_thetaTOffcenter])) (sq_nonneg _)

theorem aux_leftBumpOne_long_nonneg (n : ℕ) : 0 ≤ C_leftBumpOneLong n := by
  unfold C_leftBumpOneLong
  exact mul_nonneg
    (mul_nonneg (by positivity) (aux_leftBumpOne_whitney_nonneg n))
    (sq_nonneg _)

theorem aux_leftBumpOne_T_eq_tBump (phi : SchwartzMap ℝ ℝ) :
    Auto.aux_T (fun x : ℝ ↦ phi x) = aux_tBump phi := by
  funext x
  unfold Auto.aux_T
    Auto.multiplicationOperatorX aux_tBump
  simp only [smul_eq_mul]

theorem aux_leftBumpOne_leftBumpOne_local_finset_bound {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) (J : ℕ) (hJ : 0 < J)
    (κ : Finset ℤ) (hcard : κ.card ≤ J + 1) :
    ∑ ell ∈ κ,
      (finiteVariationSeminorm
        (fun s : aux_dyadicInterval ell ↦
          aux_leftBumpOne_averageLp hn (phiFourSchwartz b k) f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      16 * ENNReal.ofReal
        (Real.sqrt (C_leftBumpOneShortOne n) *
          Real.sqrt (C_leftBumpOneShortTwo n) * Real.rpow 2 ((k : ℝ) / 2)) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  classical
  let phi : SchwartzMap ℝ ℝ := phiFourSchwartz b k
  let psi : SchwartzMap ℝ ℝ :=
    SchwartzMap.smulLeftCLM ℝ (fun q : ℝ ↦ q) phi
  let tau : SchwartzMap ℝ ℝ := SchwartzMap.derivCLM ℝ ℝ psi
  have hphi : (phi : ℝ → ℝ) = windowBasedBumpFunctions.phiFour b k := by
    funext x
    exact phiFourSchwartz_apply b k x
  have htau : (tau : ℝ → ℝ) = aux_tBump phi := by
    funext z
    change SchwartzMap.derivCLM ℝ ℝ psi z = aux_tBump phi z
    simp only [SchwartzMap.derivCLM_apply, aux_tBump]
    congr 1
    funext z
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp only [smul_eq_mul]
  let Iphi : ℤ → ℝ≥0∞ := fun ell ↦
    ∫⁻ t in Set.Icc (1 : ℝ) 2,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ ell * t) (fun q ↦ phi q)
        (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  let Itau : ℤ → ℝ≥0∞ := fun ell ↦
    ∫⁻ t in Set.Icc (1 : ℝ) 2,
      eLpNorm (twistedAverageAtScale ((2 : ℝ) ^ ell * t) (fun q ↦ tau q)
        (fun i y ↦ f.1 i y)) 2 volume ^ (2 : ℝ) * ENNReal.ofReal t⁻¹
  let X : ℝ≥0∞ := ∑ ell ∈ κ, Iphi ell
  let Y : ℝ≥0∞ := ∑ ell ∈ κ, Itau ell
  let P : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  let w1 : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 2 (-(3 : ℝ) * (k : ℝ) / 2))
  let w2 : ℝ≥0∞ := ENNReal.ofReal (Real.rpow 2 ((k : ℝ) / 2))
  have hTtau : Auto.aux_T
      (windowBasedBumpFunctions.phiFour b k) = (tau : ℝ → ℝ) := by
    calc
      Auto.aux_T (windowBasedBumpFunctions.phiFour b k) =
          aux_tBump phi := by
            rw [← hphi]
            exact aux_leftBumpOne_T_eq_tBump phi
      _ = (tau : ℝ → ℝ) := htau.symm
  by_cases hκ : κ.Nonempty
  · obtain ⟨K, hK, hKcard, q, hsum⟩ := aux_leftBumpOne_finset_sum_as_dyadic_chain κ hκ
    have hKle : K ≤ J + 1 := by simpa [hKcard] using hcard
    have hpow := aux_leftBumpOne_card_power_bound hn hJ hKle
    have hshortOne := leftBumpOneShortOne hn b f k hk K hK q
    have hshortTwo := leftBumpOneShortTwo hn b f k hk K hK q
    rw [hTtau] at hshortTwo
    have hX : w1 * X ≤ 2 * ENNReal.ofReal (C_leftBumpOneShortOne n) * P := by
      calc
        w1 * X = ∑ ell ∈ κ, w1 * Iphi ell := by
          dsimp [X]
          rw [Finset.mul_sum]
        _ = ∑ j : Fin K, w1 * Iphi (q.1 j.castSucc) := hsum (fun ell ↦ w1 * Iphi ell)
        _ ≤ ENNReal.ofReal (C_leftBumpOneShortOne n) *
            ENNReal.ofReal ((K : ℝ) ^ variationExponent n) := by
          simpa [w1, Iphi, hphi, ENNReal.rpow_two, mul_comm] using hshortOne
        _ ≤ ENNReal.ofReal (C_leftBumpOneShortOne n) * (2 * P) := by
          gcongr
        _ = 2 * ENNReal.ofReal (C_leftBumpOneShortOne n) * P := by ring
    have hY : w2 * Y ≤ 2 * ENNReal.ofReal (C_leftBumpOneShortTwo n) * P := by
      calc
        w2 * Y = ∑ ell ∈ κ, w2 * Itau ell := by
          dsimp [Y]
          rw [Finset.mul_sum]
        _ = ∑ j : Fin K, w2 * Itau (q.1 j.castSucc) := hsum (fun ell ↦ w2 * Itau ell)
        _ ≤ ENNReal.ofReal (C_leftBumpOneShortTwo n) *
            ENNReal.ofReal ((K : ℝ) ^ variationExponent n) := by
          simpa [w2, Itau, ENNReal.rpow_two, mul_comm] using hshortTwo
        _ ≤ ENNReal.ofReal (C_leftBumpOneShortTwo n) * (2 * P) := by
          gcongr
        _ = 2 * ENNReal.ofReal (C_leftBumpOneShortTwo n) * P := by ring
    have hlocal :
        ∑ ell ∈ κ,
          (finiteVariationSeminorm
            (fun s : aux_dyadicInterval ell ↦
              aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
          8 * X ^ ((2 : ℝ)⁻¹) * Y ^ ((2 : ℝ)⁻¹) := by
      calc
        ∑ ell ∈ κ,
          (finiteVariationSeminorm
            (fun s : aux_dyadicInterval ell ↦
              aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
            ∑ ell ∈ κ, 8 * Iphi ell ^ ((2 : ℝ)⁻¹) * Itau ell ^ ((2 : ℝ)⁻¹) := by
              apply Finset.sum_le_sum
              intro ell hell
              have h := aux_leftBumpOne_local_variation_product hn phi tau htau f J ell
              simpa only [Iphi, Itau] using h
        _ = 8 * (∑ ell ∈ κ, Iphi ell ^ ((2 : ℝ)⁻¹) * Itau ell ^ ((2 : ℝ)⁻¹)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ell _
              ring
        _ ≤ 8 * (X ^ ((2 : ℝ)⁻¹) * Y ^ ((2 : ℝ)⁻¹)) := by
              gcongr
              simpa only [X, Y] using aux_leftBumpOne_finset_sqrt_mul_sqrt_le κ Iphi Itau
        _ = 8 * X ^ ((2 : ℝ)⁻¹) * Y ^ ((2 : ℝ)⁻¹) := by ring
    have hweight : w1⁻¹ ^ ((2 : ℝ)⁻¹) * w2⁻¹ ^ ((2 : ℝ)⁻¹) = w2 := by
      simpa only [w1, w2] using aux_leftBumpOne_leftBumpOne_weight_identity k
    have hweighted := aux_leftBumpOne_weighted_energy_bound
      w1 w2 w2 (ENNReal.ofReal (C_leftBumpOneShortOne n))
      (ENNReal.ofReal (C_leftBumpOneShortTwo n)) P X Y
      (by simpa only [w1] using aux_leftBumpOne_leftBumpOne_weight_nonzero k)
      (by simpa only [w1] using aux_leftBumpOne_leftBumpOne_weight_not_top k)
      (by simpa only [w2] using aux_leftBumpOne_leftBumpOne_Tweight_nonzero k)
      (by simpa only [w2] using aux_leftBumpOne_leftBumpOne_Tweight_not_top k)
      hweight hX hY
    have hconstants :
        w2 * ENNReal.ofReal (C_leftBumpOneShortOne n) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (C_leftBumpOneShortTwo n) ^ ((2 : ℝ)⁻¹) =
        ENNReal.ofReal
          (Real.sqrt (C_leftBumpOneShortOne n) *
            Real.sqrt (C_leftBumpOneShortTwo n) * Real.rpow 2 ((k : ℝ) / 2)) := by
      exact aux_leftBumpOne_ofReal_sqrt_rpow_product
        (C_leftBumpOneShortOne n) (C_leftBumpOneShortTwo n)
        (aux_leftBumpOne_short_one_nonneg n) (aux_leftBumpOne_short_two_nonneg n) k
    calc
      ∑ ell ∈ κ,
        (finiteVariationSeminorm
          (fun s : aux_dyadicInterval ell ↦
            aux_leftBumpOne_averageLp hn (phiFourSchwartz b k) f (s : ℝ)) 2 J) ^ (2 : ℝ) =
          ∑ ell ∈ κ,
            (finiteVariationSeminorm
              (fun s : aux_dyadicInterval ell ↦
                aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) := by
            congr 3
      _ ≤ 8 * X ^ ((2 : ℝ)⁻¹) * Y ^ ((2 : ℝ)⁻¹) := hlocal
      _ ≤ 16 * w2 * ENNReal.ofReal (C_leftBumpOneShortOne n) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal (C_leftBumpOneShortTwo n) ^ ((2 : ℝ)⁻¹) * P := hweighted
      _ = 16 * ENNReal.ofReal
          (Real.sqrt (C_leftBumpOneShortOne n) *
            Real.sqrt (C_leftBumpOneShortTwo n) * Real.rpow 2 ((k : ℝ) / 2)) * P := by
          rw [show 16 * w2 * ENNReal.ofReal (C_leftBumpOneShortOne n) ^ ((2 : ℝ)⁻¹) *
              ENNReal.ofReal (C_leftBumpOneShortTwo n) ^ ((2 : ℝ)⁻¹) * P =
              16 * (w2 * ENNReal.ofReal (C_leftBumpOneShortOne n) ^ ((2 : ℝ)⁻¹) *
                ENNReal.ofReal (C_leftBumpOneShortTwo n) ^ ((2 : ℝ)⁻¹)) * P by ring,
            hconstants]
      _ = 16 * ENNReal.ofReal
          (Real.sqrt (C_leftBumpOneShortOne n) *
            Real.sqrt (C_leftBumpOneShortTwo n) * Real.rpow 2 ((k : ℝ) / 2)) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by rfl
  · have hempty : κ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hκ
    simp [hempty]

noncomputable def aux_leftBumpOne_intEnergy (d : ℤ → ℤ → ℝ≥0∞) {J : ℕ}
    (t : Fin (J + 1) → ℤ) : ℝ≥0∞ :=
  ∑ j : Fin J, d (t j.succ) (t j.castSucc)

theorem aux_leftBumpOne_compress_mono_chain
    (d : ℤ → ℤ → ℝ≥0∞) (hdiag : ∀ z, d z z = 0) :
    ∀ (J : ℕ) (t : Fin (J + 1) → ℤ), Monotone t →
      ∃ M : ℕ, M ≤ J ∧ ∃ q : Fin (M + 1) → ℤ,
        StrictMono q ∧ q 0 = t 0 ∧ q (Fin.last M) = t (Fin.last J) ∧
          aux_leftBumpOne_intEnergy d t = aux_leftBumpOne_intEnergy d q := by
  intro J
  induction J with
  | zero =>
      intro t ht
      refine ⟨0, le_rfl, t, ?_, rfl, rfl, ?_⟩
      · intro i j hij
        omega
      · simp [aux_leftBumpOne_intEnergy]
  | succ J ih =>
      intro t ht
      let u : Fin (J + 1) → ℤ := fun i => t i.succ
      have hu : Monotone u := by
        intro i j hij
        dsimp [u]
        apply ht
        exact Fin.succ_le_succ_iff.mpr hij
      obtain ⟨M, hMJ, q, hq, hq0, hqlast, henergy⟩ := ih u hu
      have hsplit : aux_leftBumpOne_intEnergy d t =
          d (t 1) (t 0) + aux_leftBumpOne_intEnergy d u := by
        unfold aux_leftBumpOne_intEnergy
        rw [Fin.sum_univ_succ]
        rfl
      by_cases h01 : t 0 = t 1
      · refine ⟨M, le_trans hMJ (Nat.le_succ _), q, hq, ?_, ?_, ?_⟩
        · simpa [u, h01] using hq0
        · simpa [u, Fin.succ_last] using hqlast
        · rw [hsplit, h01, hdiag, zero_add, henergy]
      · have h01lt : t 0 < t 1 := lt_of_le_of_ne (ht (Fin.zero_le _)) h01
        let q' : Fin (M + 2) → ℤ := fun i => Fin.cases (t 0) q i
        have hq'strict : StrictMono q' := by
          intro i j hij
          by_cases hi : i = 0
          · subst i
            have hj0 : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hij)
            obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero hj0
            subst j
            have hqle : q 0 ≤ q j' := hq.monotone (Fin.zero_le _)
            have hfirst : t 0 < q 0 := by
              calc
                t 0 < t 1 := h01lt
                _ = u 0 := rfl
                _ = q 0 := hq0.symm
            exact hfirst.trans_le hqle
          · obtain ⟨i', hi'⟩ := Fin.exists_succ_eq_of_ne_zero hi
            subst i
            have hj0 : j ≠ 0 := by
              intro hj
              subst j
              exact (Fin.not_lt_zero i'.succ hij).elim
            obtain ⟨j', hj'⟩ := Fin.exists_succ_eq_of_ne_zero hj0
            subst j
            exact hq (Fin.succ_lt_succ_iff.mp hij)
        refine ⟨M + 1, Nat.succ_le_succ hMJ, q', hq'strict, ?_, ?_, ?_⟩
        · rfl
        · simp only [q']
          exact hqlast
        · have hqsplit : aux_leftBumpOne_intEnergy d q' =
              d (t 1) (t 0) + aux_leftBumpOne_intEnergy d q := by
            unfold aux_leftBumpOne_intEnergy
            rw [Fin.sum_univ_succ]
            have hqone : q' (Fin.succ 0) = t 1 := by
              change q 0 = t 1
              simpa [u] using hq0
            rw [hqone]
            rfl
          rw [hsplit, henergy, hqsplit]

theorem aux_leftBumpOne_variationExponent_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ variationExponent n := by
  unfold variationExponent
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(n : ℝ) + 2 ≤ 0 := by linarith
  have hpow : (2 : ℝ) ^ (-(n : ℝ) + 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hexp
  linarith

theorem aux_leftBumpOne_energy_of_root_le (E S V : ℝ≥0∞)
    (h : E ^ ((2 : ℝ)⁻¹) ≤ 2 * S ^ ((2 : ℝ)⁻¹) + V) :
    E ≤ 8 * S + 2 * V ^ (2 : ℝ) := by
  have hsquare := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  have hleft : (E ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = E := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hleft] at hsquare
  calc
    E ≤ (2 * S ^ ((2 : ℝ)⁻¹) + V) ^ (2 : ℝ) := hsquare
    _ ≤ (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) *
        (((2 * S ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ)) + V ^ (2 : ℝ)) := by
      exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (p := (2 : ℝ)) (by norm_num)
    _ = 8 * S + 2 * V ^ (2 : ℝ) := by
      rw [show (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 by norm_num]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      have hterm : (S ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = S := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [hterm]
      norm_num [mul_add]
      congr 1
      · rw [← mul_assoc]
        norm_num

theorem aux_leftBumpOne_long_variation_sq_le {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (J : ℕ) (_hJ : 0 < J)
    (A : ℝ) (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1) :
    (finiteVariationSeminorm
      (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦
        aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
      ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let R : ℝ≥0∞ := ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  have hexpNonneg : 0 ≤ variationExponent n := aux_leftBumpOne_variationExponent_nonneg hn
  have hchain (u : {v : Fin (J + 1) → Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) //
      Monotone v}) :
      (∑ j : Fin J,
        ‖aux_leftBumpOne_averageLp hn phi f (u.1 j.succ) -
          aux_leftBumpOne_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) ≤ R := by
    let z : Fin (J + 1) → ℤ := fun j ↦ (u.1 j).2.choose
    have hzval (j : Fin (J + 1)) : (2 : ℝ) ^ z j = u.1 j :=
      (u.1 j).2.choose_spec
    have hzmono : Monotone z := by
      intro i j hij
      apply (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      calc
        (2 : ℝ) ^ z i = u.1 i := hzval i
        _ ≤ u.1 j := u.2 hij
        _ = (2 : ℝ) ^ z j := (hzval j).symm
    let d : ℤ → ℤ → ℝ≥0∞ := fun p q ↦
      ‖aux_leftBumpOne_averageLp hn phi f ((2 : ℝ) ^ p) -
        aux_leftBumpOne_averageLp hn phi f ((2 : ℝ) ^ q)‖ₑ ^ (2 : ℕ)
    have hdiag (p : ℤ) : d p p = 0 := by
      simp [d]
    obtain ⟨M, hMJ, q, hq, hq0, hqlast, hcompress⟩ :=
      aux_leftBumpOne_compress_mono_chain d hdiag J z hzmono
    have horig :
        (∑ j : Fin J,
          ‖aux_leftBumpOne_averageLp hn phi f (u.1 j.succ) -
            aux_leftBumpOne_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
          aux_leftBumpOne_intEnergy d z := by
      unfold aux_leftBumpOne_intEnergy d
      simp only [ENNReal.rpow_two]
      apply Finset.sum_congr rfl
      intro j _
      rw [hzval]
      rw [hzval]
    by_cases hM : M = 0
    · subst M
      have hzero : aux_leftBumpOne_intEnergy d q = 0 := by simp [aux_leftBumpOne_intEnergy]
      rw [horig, hcompress, hzero]
      exact bot_le
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
      let qc : aux_dyadicChain M := ⟨q, hq⟩
      have hqEnergy : aux_leftBumpOne_intEnergy d q =
          aux_dyadicJumpEnergy (fun x ↦ phi x) f.1 M qc := by
        unfold aux_leftBumpOne_intEnergy d aux_dyadicJumpEnergy
        apply Finset.sum_congr rfl
        intro j _
        dsimp [qc]
        simpa only [← enorm_eq_nnnorm] using congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
          (aux_leftBumpOne_averageLp_enorm_sub hn phi f ((2 : ℝ) ^ (q j.succ))
            ((2 : ℝ) ^ (q j.castSucc)))
      have hq := hA M hMpos qc
      have hMJreal : (M : ℝ) ≤ J := by exact_mod_cast hMJ
      have hpow : (M : ℝ) ^ variationExponent n ≤
          (J : ℝ) ^ variationExponent n :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hMJreal hexpNonneg
      have hpowENN : ENNReal.ofReal ((M : ℝ) ^ variationExponent n) ≤
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
        ENNReal.ofReal_le_ofReal hpow
      calc
        (∑ j : Fin J,
          ‖aux_leftBumpOne_averageLp hn phi f (u.1 j.succ) -
            aux_leftBumpOne_averageLp hn phi f (u.1 j.castSucc)‖ₑ ^ (2 : ℝ)) =
            aux_leftBumpOne_intEnergy d z := horig
        _ = aux_leftBumpOne_intEnergy d q := hcompress
        _ = aux_dyadicJumpEnergy (fun x ↦ phi x) f.1 M qc := hqEnergy
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((M : ℝ) ^ variationExponent n) := hq
        _ ≤ R := by
          dsimp [R]
          exact mul_le_mul_of_nonneg_left hpowENN bot_le
  have hroot : finiteVariationSeminorm
      (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦
        aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J ≤ R ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro u
    have h := ENNReal.rpow_le_rpow (hchain u)
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    simpa only [← enorm_eq_nnnorm] using h
  have hsquare := ENNReal.rpow_le_rpow hroot (by norm_num : (0 : ℝ) ≤ 2)
  have hright : (R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = R := by
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hright] at hsquare
  exact hsquare

theorem aux_leftBumpOne_shortLong_finish_of_local {n : ℕ} (hn : 2 ≤ n)
    (phi : SchwartzMap ℝ ℝ) (f : ReductionNormalizedTuple n) (B A : ℝ)
    (hBnonneg : 0 ≤ B) (hAnonneg : 0 ≤ A)
    (hA : aux_dyadicVariationBound A (fun x ↦ phi x) f.1)
    (hlocal : ∀ (J : ℕ), 0 < J → ∀ κ : Finset ℤ, κ.card ≤ J + 1 →
      ∑ k ∈ κ,
        (finiteVariationSeminorm
          (fun s : aux_dyadicInterval k ↦
            aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
        ENNReal.ofReal B * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :
    aux_variationBound (8 * B + 2 * A) (fun x ↦ phi x) f.1 := by
  unfold aux_variationBound
  intro J hJ t
  let a : ℝ → Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    aux_leftBumpOne_averageLp hn phi f
  obtain ⟨κ, hκ, hsplit⟩ :=
    (shortlongJumps a J 2 (by norm_num : (1 : ℝ) ≤ 2)).1 t.1 t.2.1.monotone t.2.2
  let S : ℝ≥0∞ := ∑ k ∈ κ,
    (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) 2 J) ^ (2 : ℝ)
  let V : ℝ≥0∞ := finiteVariationSeminorm
    (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) 2 J
  have henergy :
      (∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ≤
        8 * S + 2 * V ^ (2 : ℝ) := by
    exact aux_leftBumpOne_energy_of_root_le _ S V hsplit
  have hlocal' : S ≤ ENNReal.ofReal B *
      ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    have hcard : κ.card ≤ J + 1 :=
      aux_leftBumpOne_kappa_card_le t.1 t.2.2 κ hκ
    dsimp [S, a]
    exact hlocal J hJ κ hcard
  have hlong' : V ^ (2 : ℝ) ≤
      ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    dsimp [V, a]
    exact aux_leftBumpOne_long_variation_sq_le hn phi f J hJ A hA
  have htarget :
      8 * S + 2 * V ^ (2 : ℝ) ≤
        ENNReal.ofReal (8 * B + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    calc
      8 * S + 2 * V ^ (2 : ℝ) ≤
          8 * (ENNReal.ofReal B * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) +
          2 * (ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) := by
            gcongr
      _ = (8 * ENNReal.ofReal B + 2 * ENNReal.ofReal A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by ring
      _ = ENNReal.ofReal (8 * B + 2 * A) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
        rw [ENNReal.ofReal_add]
        · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        · exact mul_nonneg (by norm_num) hBnonneg
        · exact mul_nonneg (by norm_num) hAnonneg
  have hjump : aux_jumpEnergy (fun x ↦ phi x) f.1 J t =
      ∑ j : Fin J,
        (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ) := by
    unfold aux_jumpEnergy twistedJumpEnergy
    simp only [ENNReal.rpow_two]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [← enorm_eq_nnnorm, ENNReal.rpow_two] using
      (congrArg (fun z : ℝ≥0∞ ↦ z ^ (2 : ℕ))
        (aux_leftBumpOne_averageLp_enorm_sub hn phi f (t.1 j.succ) (t.1 j.castSucc))).symm
  rw [hjump]
  exact henergy.trans htarget

theorem aux_leftBumpOne_twistedAverageAtScale_oneRescaled {n : ℕ}
    (phi : ℝ → ℝ) (f : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (t lambda : ℝ) (ht : 0 < t) (hlambda : 0 < lambda) :
    twistedAverageAtScale t (aux_oneRescaled lambda phi) f =
      twistedAverageAtScale (t * lambda) phi f := by
  unfold twistedAverageAtScale
  unfold aux_twistedAverageAtScale aux_twistedAverage aux_oneRescaled
  funext x
  congr 1
  funext s
  congr 1
  field_simp [ht.ne', hlambda.ne']

def aux_leftBumpOne_scaleMul (lambda : ℝ) (hlambda : 0 < lambda)
    {J : ℕ} (t : aux_scaleChain J) : aux_scaleChain J :=
  ⟨fun j ↦ lambda * t.1 j,
    ⟨by
      intro i j hij
      exact mul_lt_mul_of_pos_left (t.2.1 hij) hlambda,
    by
      intro j
      exact mul_pos hlambda (t.2.2 j)⟩⟩

theorem aux_leftBumpOne_variationBound_of_oneRescaled {n : ℕ} (lambda : ℝ)
    (hlambda : 0 < lambda) (A : ℝ) (phi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_variationBound A (aux_oneRescaled lambda phi) f) :
    aux_variationBound A phi f := by
  intro J hJ t
  let t' : aux_scaleChain J := aux_leftBumpOne_scaleMul lambda⁻¹ (inv_pos.mpr hlambda) t
  have hscale (j : Fin (J + 1)) : t'.1 j * lambda = t.1 j := by
    dsimp [t', aux_leftBumpOne_scaleMul]
    field_simp [hlambda.ne']
  have hEq : aux_jumpEnergy (aux_oneRescaled lambda phi) f J t' =
      aux_jumpEnergy phi f J t := by
    unfold aux_jumpEnergy twistedJumpEnergy
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    funext x
    rw [aux_leftBumpOne_twistedAverageAtScale_oneRescaled phi (fun i y ↦ f i y)
      (t'.1 j.succ) lambda (t'.2.2 j.succ) hlambda,
      aux_leftBumpOne_twistedAverageAtScale_oneRescaled phi (fun i y ↦ f i y)
        (t'.1 j.castSucc) lambda (t'.2.2 j.castSucc) hlambda,
      hscale j.succ, hscale j.castSucc]
  calc
    aux_jumpEnergy phi f J t = aux_jumpEnergy (aux_oneRescaled lambda phi) f J t' :=
      hEq.symm
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
      hA J hJ t'

theorem aux_leftBumpOne_twistedAverageAtScale_neg {n : ℕ}
    (phi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) (t : ℝ) :
    twistedAverageAtScale t (-phi) (fun i y ↦ f i y) =
      -twistedAverageAtScale t phi (fun i y ↦ f i y) := by
  unfold twistedAverageAtScale
  unfold aux_twistedAverageAtScale aux_twistedAverage
  have hkernel : (fun s : ℝ ↦ t⁻¹ * (-phi) (t⁻¹ * s)) =
      -(fun s : ℝ ↦ t⁻¹ * phi (t⁻¹ * s)) := by
    funext s
    change t⁻¹ * (-(phi (t⁻¹ * s))) = -(t⁻¹ * phi (t⁻¹ * s))
    ring
  rw [hkernel]
  exact aux_twistedAverage_neg f _

theorem aux_leftBumpOne_variationBound_neg {n : ℕ} (A : ℝ) (phi : ℝ → ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (hA : aux_variationBound A phi f) :
    aux_variationBound A (-phi) f := by
  intro J hJ t
  calc
    aux_jumpEnergy (-phi) f J t = aux_jumpEnergy phi f J t := by
      unfold aux_jumpEnergy twistedJumpEnergy
      apply Finset.sum_congr rfl
      intro j _
      rw [aux_leftBumpOne_twistedAverageAtScale_neg phi f,
        aux_leftBumpOne_twistedAverageAtScale_neg phi f]
      have hfun :
          (fun x ↦ (-twistedAverageAtScale (t.1 j.succ) phi (fun i y ↦ f i y)) x -
              (-twistedAverageAtScale (t.1 j.castSucc) phi (fun i y ↦ f i y)) x) =
            fun x ↦ -(twistedAverageAtScale (t.1 j.succ) phi (fun i y ↦ f i y) x -
              twistedAverageAtScale (t.1 j.castSucc) phi (fun i y ↦ f i y) x) := by
            funext x
            simp only [Pi.neg_apply]
            ring
      rw [hfun]
      calc
        eLpNorm
            (fun x ↦ -(twistedAverageAtScale (t.1 j.succ) phi (fun i y ↦ f i y) x -
              twistedAverageAtScale (t.1 j.castSucc) phi (fun i y ↦ f i y) x)) 2 volume ^ 2 =
            eLpNorm
              (-(fun x ↦ twistedAverageAtScale (t.1 j.succ) phi
                  (fun i y ↦ f i y) x -
                twistedAverageAtScale (t.1 j.castSucc) phi
                  (fun i y ↦ f i y) x)) 2 volume ^ 2 := by
              rfl
        _ = eLpNorm
              (fun x ↦ twistedAverageAtScale (t.1 j.succ) phi (fun i y ↦ f i y) x -
                twistedAverageAtScale (t.1 j.castSucc) phi (fun i y ↦ f i y) x) 2 volume ^ 2 := by
              rw [eLpNorm_neg]
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) :=
      hA J hJ t

theorem aux_leftBumpOne_conv_Ici_one_eq_conv_Ici_zero_shift (g : ℝ → ℝ) (x : ℝ) :
    Auto.aux_realConvolution
      (Auto.aux_indicator (Set.Ici 1)) g x =
      Auto.aux_realConvolution
        (Auto.aux_indicator (Set.Ici 0)) g (x - 1) := by
  unfold Auto.aux_realConvolution
  let G : ℝ → ℝ := fun y =>
    Auto.aux_indicator (Set.Ici 1) y * g (x - y)
  have hemb : MeasurableEmbedding (fun z : ℝ => (1 : ℝ) + z) := by
    apply Continuous.measurableEmbedding
    · fun_prop
    · intro u v huv
      linarith
  have hmp := measurePreserving_add_left (volume : Measure ℝ) (1 : ℝ)
  have h := hmp.integral_comp hemb G
  calc
    (∫ y : ℝ, Auto.aux_indicator (Set.Ici 1) y *
        g (x - y)) = ∫ z : ℝ, G (1 + z) := h.symm
    _ = ∫ z : ℝ,
        Auto.aux_indicator (Set.Ici 0) z *
          g ((x - 1) - z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      dsimp [G]
      have hind : Auto.aux_indicator (Set.Ici 1) (1 + z) =
          Auto.aux_indicator (Set.Ici 0) z := by
        unfold Auto.aux_indicator
        by_cases hz : 0 ≤ z <;> simp [hz]
      rw [hind]
      congr 1
      ring_nf

theorem aux_leftBumpOne_conv_Ici_zero_rescaled_theta_eq (b : windowBasedBumpFunctions)
    (a x : ℝ) (ha : 0 < a) :
    Auto.aux_realConvolution
      (Auto.aux_indicator (Set.Ici 0))
      (Auto.aux_realRescaled a
        (windowBasedBumpFunctions.theta b)) x =
      a * aux_oneRescaled a (windowBasedBumpFunctions.thetaTilde b) x := by
  let g : ℝ → ℝ := fun z =>
    Auto.aux_indicator (Set.Ici 0) z *
      windowBasedBumpFunctions.theta b (a⁻¹ * x - z)
  have hind (y : ℝ) :
      Auto.aux_indicator (Set.Ici 0) (a⁻¹ * y) =
        Auto.aux_indicator (Set.Ici 0) y := by
    have hmem : a⁻¹ * y ∈ Set.Ici (0 : ℝ) ↔ y ∈ Set.Ici (0 : ℝ) := by
      change 0 ≤ a⁻¹ * y ↔ 0 ≤ y
      exact mul_nonneg_iff_of_pos_left (inv_pos.mpr ha)
    unfold Auto.aux_indicator
    by_cases hy : y ∈ Set.Ici (0 : ℝ)
    · have hy' : a⁻¹ * y ∈ Set.Ici (0 : ℝ) := hmem.mpr hy
      simp [hy, hy']
    · have hy' : a⁻¹ * y ∉ Set.Ici (0 : ℝ) := fun h => hy (hmem.mp h)
      simp [hy, hy']
  have hleft :
      (∫ y : ℝ, Auto.aux_indicator (Set.Ici 0) y *
        Auto.aux_realRescaled a
          (windowBasedBumpFunctions.theta b) (x - y)) =
        a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := by
    calc
      (∫ y : ℝ, Auto.aux_indicator (Set.Ici 0) y *
          Auto.aux_realRescaled a
            (windowBasedBumpFunctions.theta b) (x - y)) =
          ∫ y : ℝ, a⁻¹ * g (a⁻¹ * y) := by
            apply integral_congr_ae
            filter_upwards [] with y
            dsimp [g, Auto.aux_realRescaled]
            rw [hind]
            ring_nf
      _ = a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := by
        rw [integral_const_mul]
  have hchange := Measure.integral_comp_inv_mul_left g a
  rw [abs_of_pos ha, smul_eq_mul] at hchange
  change (∫ y : ℝ,
      Auto.aux_indicator (Set.Ici 0) y *
      Auto.aux_realRescaled a
        (windowBasedBumpFunctions.theta b) (x - y)) =
    a * (a⁻¹ * ∫ y : ℝ,
      Auto.aux_indicator (Set.Ici 0) y *
        windowBasedBumpFunctions.theta b (a⁻¹ * x - y))
  calc
    (∫ y : ℝ, Auto.aux_indicator (Set.Ici 0) y *
        Auto.aux_realRescaled a
          (windowBasedBumpFunctions.theta b) (x - y)) =
        a⁻¹ * ∫ y : ℝ, g (a⁻¹ * y) := hleft
    _ = a⁻¹ * (a * ∫ y : ℝ, g y) := by rw [hchange]
    _ = ∫ y : ℝ, g y := by field_simp [ha.ne']
    _ = a * (a⁻¹ * ∫ y : ℝ,
        Auto.aux_indicator (Set.Ici 0) y *
          windowBasedBumpFunctions.theta b (a⁻¹ * x - y)) := by
          dsimp [g]
          field_simp [ha.ne']

theorem aux_leftBumpOne_phiTwo_eq_neg_oneRescaled_phiFour (b : windowBasedBumpFunctions)
    (k : ℤ) :
    windowBasedBumpFunctions.phiTwo b k =
      -aux_oneRescaled ((2 : ℝ) ^ k) (windowBasedBumpFunctions.phiFour b k) := by
  funext x
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  rw [show windowBasedBumpFunctions.phiTwo b k x =
      -Auto.aux_realConvolution
        (Auto.aux_indicator (Set.Ici 0))
        (Auto.aux_realRescaled a
          (windowBasedBumpFunctions.theta b)) (x - 1) by
          dsimp [windowBasedBumpFunctions.phiTwo, a]
          rw [aux_leftBumpOne_conv_Ici_one_eq_conv_Ici_zero_shift]
    , aux_leftBumpOne_conv_Ici_zero_rescaled_theta_eq b a (x - 1) ha]
  have hprod : (2 : ℝ) ^ k * (2 : ℝ) ^ (-k) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  dsimp [a, windowBasedBumpFunctions.phiFour, aux_oneRescaled]
  field_simp [ha.ne']
  rw [hprod]

theorem aux_leftBumpOne_leftBumpOne {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_variationBound (C_leftBumpOne n * Real.rpow 2 ((k : ℝ) / 2))
      (windowBasedBumpFunctions.phiTwo b k) f.1 := by
  let phi : SchwartzMap ℝ ℝ := phiFourSchwartz b k
  let B : ℝ := 16 * Real.sqrt (C_leftBumpOneShortOne n) *
    Real.sqrt (C_leftBumpOneShortTwo n) * Real.rpow 2 ((k : ℝ) / 2)
  let A : ℝ := C_leftBumpOneLong n * Real.rpow 2 ((k : ℝ) / 2)
  have hphi : (fun x : ℝ ↦ phi x) = windowBasedBumpFunctions.phiFour b k := by
    funext x
    exact phiFourSchwartz_apply b k x
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (by norm_num) _)
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (aux_leftBumpOne_long_nonneg n) (Real.rpow_nonneg (by norm_num) _)
  have hlong : aux_dyadicVariationBound A (fun x ↦ phi x) f.1 := by
    simpa [A, hphi] using leftBumpOneLong hn b f k hk
  have hlocal : ∀ (J : ℕ), 0 < J → ∀ κ : Finset ℤ, κ.card ≤ J + 1 →
      ∑ ell ∈ κ,
        (finiteVariationSeminorm
          (fun s : aux_dyadicInterval ell ↦
            aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
        ENNReal.ofReal B * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
    intro J hJ κ hcard
    let Q : ℝ := Real.sqrt (C_leftBumpOneShortOne n) *
      Real.sqrt (C_leftBumpOneShortTwo n) * Real.rpow 2 ((k : ℝ) / 2)
    have hlocal0 := aux_leftBumpOne_leftBumpOne_local_finset_bound hn b f k hk J hJ κ hcard
    calc
      ∑ ell ∈ κ,
        (finiteVariationSeminorm
          (fun s : aux_dyadicInterval ell ↦
            aux_leftBumpOne_averageLp hn phi f (s : ℝ)) 2 J) ^ (2 : ℝ) ≤
          16 * ENNReal.ofReal Q * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
            simpa [phi, Q] using hlocal0
      _ = ENNReal.ofReal B * ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
            have hBsplit : B = 16 * Q := by
              dsimp [B, Q]
              ring
            rw [hBsplit, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
            norm_num
  have hshort := aux_leftBumpOne_shortLong_finish_of_local hn phi f B A
    hBnonneg hAnonneg hlong hlocal
  have hcoef : 8 * B + 2 * A =
      C_leftBumpOne n * Real.rpow 2 ((k : ℝ) / 2) := by
    dsimp [B, A, C_leftBumpOne]
    ring
  rw [hcoef] at hshort
  let a : ℝ := (2 : ℝ) ^ k
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hcomp : aux_oneRescaled a⁻¹ (aux_oneRescaled a (fun x ↦ phi x)) =
      fun x ↦ phi x := by
    funext x
    unfold aux_oneRescaled
    field_simp [ha.ne']
  rw [← hcomp] at hshort
  have hrescaled := aux_leftBumpOne_variationBound_of_oneRescaled a⁻¹ (inv_pos.mpr ha)
    (C_leftBumpOne n * Real.rpow 2 ((k : ℝ) / 2))
    (aux_oneRescaled a (fun x ↦ phi x)) f.1 hshort
  have hneg := aux_leftBumpOne_variationBound_neg
    (C_leftBumpOne n * Real.rpow 2 ((k : ℝ) / 2))
    (aux_oneRescaled a (fun x ↦ phi x)) f.1 hrescaled
  have hphiTwo : windowBasedBumpFunctions.phiTwo b k =
      -aux_oneRescaled a (fun x ↦ phi x) := by
    calc
      windowBasedBumpFunctions.phiTwo b k =
          -aux_oneRescaled ((2 : ℝ) ^ k) (windowBasedBumpFunctions.phiFour b k) :=
            aux_leftBumpOne_phiTwo_eq_neg_oneRescaled_phiFour b k
      _ = -aux_oneRescaled a (fun x ↦ phi x) := by
            rw [← hphi]
  rw [hphiTwo]
  exact hneg

/--
**Lemma.**

Let $\gamma=\frac12$. For every $k\le -1$,

$$
\|A_{t}(\varphi_{2,k})\|_{V_{2,J}(t\in(0,\infty);L^2)}^2  \le C_{\text{lem:leftbump1}} 2^{\gamma k}
J^{\alpha(n)},
$$

where  $C_{\text{lem:leftbump1}}
=2^7C_{\text{lem:leftbump1\_short1}}^{1/2}C_{\text{lem:leftbump1\_short2}}^{1/2}
+2C_{\text{lem:leftbump1\_long}}$.

See also `Auto.leftBumpOne`,
`Auto.leftBumpOneShortOne`,
`Auto.leftBumpOneShortTwo`,
`Auto.leftBumpOneLong`.
-/
theorem leftBumpOne {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n) (k : ℤ)
    (hk : k ≤ -1) :
    aux_variationBound (C_leftBumpOne n * Real.rpow 2 ((k : ℝ) / 2))
      (windowBasedBumpFunctions.phiTwo b k) f.1 := by
  exact aux_leftBumpOne_leftBumpOne hn b f k hk

/-- The numerical estimate in Lemma `Auto.constantLeftBumpOne`. -/
theorem aux_leftBumpOne_whitney_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_inductPositiveTermsReductionWhitney n <
      (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
  unfold C_inductPositiveTermsReductionWhitney
  calc
    11 * C_inductPositiveTermsReductionWhitneyGap n <
        11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553) :=
      mul_lt_mul_of_pos_left (constantWhitneyGapReduction hn) (by norm_num)
    _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by
      calc
        11 * ((127 / 128 : ℝ) * (2 : ℝ) ^ 553) =
            ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 4) * (2 : ℝ) ^ 553 := by
              norm_num
              set_option exponentiation.threshold 1000 in
                ring
        _ = (1397 / 2048 : ℝ) * ((2 : ℝ) ^ 4 * (2 : ℝ) ^ 553) := by
          set_option exponentiation.threshold 1000 in
            ring
        _ = (1397 / 2048 : ℝ) * (2 : ℝ) ^ 557 := by rw [← pow_add]

theorem aux_leftBumpOne_short_two_aux_le :
    C_leftBumpOneShortTwoAuxiliary ≤ (2 : ℝ) ^ 31 := by
  unfold C_leftBumpOneShortTwoAuxiliary
  apply max_le
  · exact (constantThetaPrimitive 2 (by norm_num) (by norm_num [N_uniPair])).2
  · apply max_le
    · calc
        C_thetaDecay 2 ≤ (2 : ℝ) ^ (2 * 2 + 17) :=
          constantThetaDecay 2 (by norm_num) (by norm_num)
        _ ≤ (2 : ℝ) ^ 31 := by norm_num
    · calc
        C_thetaDecay 3 ≤ (2 : ℝ) ^ (2 * 3 + 17) :=
          constantThetaDecay 3 (by norm_num) (by norm_num)
        _ ≤ (2 : ℝ) ^ 31 := by norm_num

theorem aux_leftBumpOne_short_two_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOneShortTwo n <
      (185801 / 262144 : ℝ) * (2 : ℝ) ^ 630 := by
  have hW := aux_leftBumpOne_whitney_sharp hn
  have hAux := aux_leftBumpOne_short_two_aux_le
  have hO := constantOffCenterBump
  have hOnonneg : 0 ≤ C_thetaTOffcenter := by
    norm_num [C_thetaTOffcenter]
  have hOpos : 0 < C_thetaTOffcenter := by
    norm_num [C_thetaTOffcenter]
  have hAuxpos : 0 < C_leftBumpOneShortTwoAuxiliary := by
    unfold C_leftBumpOneShortTwoAuxiliary
    exact lt_of_lt_of_le
      (by norm_num [C_thetaPrimitive, Auto.C_uniPair])
      (le_max_left _ _)
  unfold C_leftBumpOneShortTwo
  calc
    (2 : ℝ) ^ 4 * C_inductPositiveTermsReductionWhitney n * C_thetaTOffcenter *
        C_leftBumpOneShortTwoAuxiliary ^ 2 <
      (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) * C_thetaTOffcenter *
        C_leftBumpOneShortTwoAuxiliary ^ 2 := by
          gcongr
    _ ≤ (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) * C_thetaTOffcenter *
        ((2 : ℝ) ^ 31) ^ 2 := by
          gcongr
    _ ≤ (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) * 133 *
        ((2 : ℝ) ^ 31) ^ 2 := by
          gcongr
    _ = (185801 / 262144 : ℝ) * (2 : ℝ) ^ 630 := by
      rw [show ((2 : ℝ) ^ 31) ^ 2 = (2 : ℝ) ^ 62 by rw [← pow_mul]]
      calc
        (2 : ℝ) ^ 4 * ((1397 / 2048 : ℝ) * (2 : ℝ) ^ 557) * 133 *
            (2 : ℝ) ^ 62 =
            (185801 / 262144 : ℝ) *
              ((2 : ℝ) ^ 11 * (2 : ℝ) ^ 557 * (2 : ℝ) ^ 62) := by
                set_option exponentiation.threshold 1000 in
                  norm_num
        _ = (185801 / 262144 : ℝ) * (2 : ℝ) ^ 630 := by
          rw [← pow_add, ← pow_add]

theorem aux_leftBumpOne_constant_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOne n < (23 / 32 : ℝ) * (2 : ℝ) ^ 636 := by
  let q : ℝ := 185801 / 262144
  have h1 : C_leftBumpOneShortOne n < q * (2 : ℝ) ^ 628 := by
    simpa [q] using constantLeftBumpOneShortOne hn
  have h2 : C_leftBumpOneShortTwo n < q * (2 : ℝ) ^ 630 := by
    simpa [q] using aux_leftBumpOne_short_two_sharp hn
  have hL : C_leftBumpOneLong n < (2 : ℝ) ^ 625 :=
    constantLeftBumpOneLong hn
  have h1nonneg := aux_leftBumpOne_short_one_nonneg n
  have h2nonneg := aux_leftBumpOne_short_two_nonneg n
  have hproduct : C_leftBumpOneShortOne n * C_leftBumpOneShortTwo n <
      (q * (2 : ℝ) ^ 629) ^ 2 := by
    calc
      C_leftBumpOneShortOne n * C_leftBumpOneShortTwo n <
          (q * (2 : ℝ) ^ 628) * (q * (2 : ℝ) ^ 630) :=
        mul_lt_mul_of_nonneg h1 h2 h1nonneg h2nonneg
      _ = q ^ 2 * ((2 : ℝ) ^ 628 * (2 : ℝ) ^ 630) := by
        set_option exponentiation.threshold 1000 in
          ring
      _ = q ^ 2 * ((2 : ℝ) ^ 629) ^ 2 := by
        congr 1
        rw [← pow_add, ← pow_mul]
      _ = (q * (2 : ℝ) ^ 629) ^ 2 := by rw [mul_pow]
  have hroot : Real.sqrt (C_leftBumpOneShortOne n) *
      Real.sqrt (C_leftBumpOneShortTwo n) < q * (2 : ℝ) ^ 629 := by
    apply (sq_lt_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt h1nonneg, Real.sq_sqrt h2nonneg]
    exact hproduct
  have hshort : (2 : ℝ) ^ 7 * Real.sqrt (C_leftBumpOneShortOne n) *
      Real.sqrt (C_leftBumpOneShortTwo n) < q * (2 : ℝ) ^ 636 := by
    calc
      (2 : ℝ) ^ 7 * Real.sqrt (C_leftBumpOneShortOne n) *
          Real.sqrt (C_leftBumpOneShortTwo n) =
          (2 : ℝ) ^ 7 *
            (Real.sqrt (C_leftBumpOneShortOne n) *
              Real.sqrt (C_leftBumpOneShortTwo n)) := by ring
      _ < (2 : ℝ) ^ 7 * (q * (2 : ℝ) ^ 629) :=
        mul_lt_mul_of_pos_left hroot (by positivity)
      _ = q * (2 : ℝ) ^ 636 := by
        calc
          (2 : ℝ) ^ 7 * (q * (2 : ℝ) ^ 629) =
              q * ((2 : ℝ) ^ 7 * (2 : ℝ) ^ 629) := by
                set_option exponentiation.threshold 1000 in
                  ring
          _ = q * (2 : ℝ) ^ 636 := by rw [← pow_add]
  have hlong : 2 * C_leftBumpOneLong n <
      (1 / 1024 : ℝ) * (2 : ℝ) ^ 636 := by
    calc
      2 * C_leftBumpOneLong n < 2 * (2 : ℝ) ^ 625 :=
        mul_lt_mul_of_pos_left hL (by norm_num)
      _ = (1 / 1024 : ℝ) * (2 : ℝ) ^ 636 := by
        rw [show (1024 : ℝ) = (2 : ℝ) ^ 10 by norm_num]
        field_simp
  unfold C_leftBumpOne
  calc
    (2 : ℝ) ^ 7 * Real.sqrt (C_leftBumpOneShortOne n) *
          Real.sqrt (C_leftBumpOneShortTwo n) + 2 * C_leftBumpOneLong n <
        q * (2 : ℝ) ^ 636 + (1 / 1024 : ℝ) * (2 : ℝ) ^ 636 :=
      add_lt_add hshort hlong
    _ = (q + 1 / 1024 : ℝ) * (2 : ℝ) ^ 636 := by
      set_option exponentiation.threshold 1000 in
        ring
    _ < (23 / 32 : ℝ) * (2 : ℝ) ^ 636 := by
      apply mul_lt_mul_of_pos_right
      · dsimp [q]
        norm_num
      · positivity

/--
**Lemma (constant $C_{\text{lem:leftbump1}}$).**

$$
C_{\text{lem:leftbump1}}<\tfrac{23}{32}2^{636}<2^{636}.
$$

See also `Auto.leftBumpOne`.
-/
theorem constantLeftBumpOne {n : ℕ} (hn : 2 ≤ n) :
    C_leftBumpOne n < (23 / 32 : ℝ) * (2 : ℝ) ^ 636 := by
  exact aux_leftBumpOne_constant_sharp hn

/-- The final constant in the proof of Theorem `Auto.aux_main_twisted_theorem`. -/
noncomputable def C_mainTwistedTheorem (n : ℕ) : ℝ :=
  (2 : ℝ) ^ 2 *
    (C_mainBumpOne n + (2 : ℝ) ^ 6 * C_mainBumpTwo n + C_leftBump n +
      (2 : ℝ) ^ 6 * C_leftBumpOne n)

theorem aux_constantMainTwistedTheoremReduction_sharp {n : ℕ} (hn : 2 ≤ n) :
    C_mainTwistedTheorem n < (7 / 8 : ℝ) * (2 : ℝ) ^ 666 := by
  have h1 := constantMainBumpOne hn
  have h2 := constantMainBumpTwo hn
  have h3 := constantLeftBump hn
  have h4 := constantLeftBumpOne hn
  have h2' : (2 : ℝ) ^ 6 * C_mainBumpTwo n <
      (2 : ℝ) ^ 6 * ((27 / 32 : ℝ) * (2 : ℝ) ^ 658) :=
    mul_lt_mul_of_pos_left h2 (by positivity)
  have h4' : (2 : ℝ) ^ 6 * C_leftBumpOne n <
      (2 : ℝ) ^ 6 * ((23 / 32 : ℝ) * (2 : ℝ) ^ 636) :=
    mul_lt_mul_of_pos_left h4 (by positivity)
  have hinter :
      C_mainBumpOne n + (2 : ℝ) ^ 6 * C_mainBumpTwo n + C_leftBump n +
          (2 : ℝ) ^ 6 * C_leftBumpOne n <
        (7 / 8 : ℝ) * (2 : ℝ) ^ 610 +
          (2 : ℝ) ^ 6 * ((27 / 32 : ℝ) * (2 : ℝ) ^ 658) +
          (33 / 64 : ℝ) * (2 : ℝ) ^ 636 +
          (2 : ℝ) ^ 6 * ((23 / 32 : ℝ) * (2 : ℝ) ^ 636) := by
    exact add_lt_add (add_lt_add (add_lt_add h1 h2') h3) h4'
  unfold C_mainTwistedTheorem
  calc
    (2 : ℝ) ^ 2 *
        (C_mainBumpOne n + (2 : ℝ) ^ 6 * C_mainBumpTwo n + C_leftBump n +
          (2 : ℝ) ^ 6 * C_leftBumpOne n) <
        (2 : ℝ) ^ 2 *
          ((7 / 8 : ℝ) * (2 : ℝ) ^ 610 +
            (2 : ℝ) ^ 6 * ((27 / 32 : ℝ) * (2 : ℝ) ^ 658) +
            (33 / 64 : ℝ) * (2 : ℝ) ^ 636 +
            (2 : ℝ) ^ 6 * ((23 / 32 : ℝ) * (2 : ℝ) ^ 636)) :=
      mul_lt_mul_of_pos_left hinter (by positivity)
    _ < (7 / 8 : ℝ) * (2 : ℝ) ^ 666 := by
      set_option exponentiation.threshold 1000 in
        norm_num

theorem constantMainTwistedTheoremReduction {n : ℕ} (hn : 2 ≤ n) :
    C_mainTwistedTheorem n < (2 : ℝ) ^ 666 := by
  calc
    C_mainTwistedTheorem n < (7 / 8 : ℝ) * (2 : ℝ) ^ 666 :=
      aux_constantMainTwistedTheoremReduction_sharp hn
    _ < (2 : ℝ) ^ 666 := by
      apply mul_lt_of_lt_one_left
      · positivity
      · norm_num

/-! ### Terminal smoothing and aggregation helpers -/

open Filter Finset Topology

noncomputable def aux_mainTwisted_delta
    (b : windowBasedBumpFunctions) (N : ℕ) : ℝ → ℝ :=
  fun x => b.smoothingPartialSum (N + 1) x - b.smoothingPartialSum N x

theorem aux_mainTwisted_delta_sum (b : windowBasedBumpFunctions) (N : ℕ) :
    ∑ q ∈ Finset.range N, aux_mainTwisted_delta b q =
      b.smoothingPartialSum N - b.smoothingPartialSum 0 := by
  funext x
  simp only [Finset.sum_apply, aux_mainTwisted_delta]
  exact Finset.sum_range_sub (fun N => b.smoothingPartialSum N x) N

theorem aux_mainTwisted_delta_expand (b : windowBasedBumpFunctions) (N : ℕ) :
    aux_mainTwisted_delta b N =
      fun x => windowBasedBumpFunctions.phiZero b ((N + 1 : ℕ) : ℤ) x +
        (windowBasedBumpFunctions.phiOne b (-((N + 1 : ℕ) : ℤ)) x +
          windowBasedBumpFunctions.phiTwo b (-((N + 1 : ℕ) : ℤ)) x) := by
  funext x
  simp only [aux_mainTwisted_delta, windowBasedBumpFunctions.smoothingPartialSum,
    aux_integerIntervalSum]
  rw [show ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 by omega]
  have hzeroSet :
      insert ((N : ℤ) + 1) (Finset.Icc (-2 : ℤ) (N : ℤ)) =
        Finset.Icc (-2 : ℤ) ((N : ℤ) + 1) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotzero : ((N : ℤ) + 1) ∉ Finset.Icc (-2 : ℤ) (N : ℤ) := by
    simp only [Finset.mem_Icc]
    omega
  rw [← hzeroSet, Finset.sum_insert hnotzero]
  have honeSet :
      insert (-((N : ℤ) + 1)) (Finset.Icc (-(N : ℤ)) (-1)) =
        Finset.Icc (-((N : ℤ) + 1) : ℤ) (-1) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnotone : -((N : ℤ) + 1) ∉ Finset.Icc (-(N : ℤ)) (-1) := by
    simp only [Finset.mem_Icc]
    omega
  rw [← honeSet, Finset.sum_insert hnotone]
  simp
  ring

theorem aux_mainTwisted_delta_converges (b : windowBasedBumpFunctions) :
    Tendsto (fun N => eLpNorm
      ((aux_indicator (Set.Icc 0 1) - b.smoothingPartialSum 0) -
        ∑ q ∈ Finset.range N, aux_mainTwisted_delta b q) 2 volume)
      atTop (nhds 0) := by
  have h := smoothingDecomp b
  have heq (N : ℕ) :
      ((aux_indicator (Set.Icc 0 1) - b.smoothingPartialSum 0) -
        ∑ q ∈ Finset.range N, aux_mainTwisted_delta b q) =
        aux_indicator (Set.Icc 0 1) - b.smoothingPartialSum N := by
    rw [aux_mainTwisted_delta_sum]
    funext x
    simp
  have h' : Tendsto (fun N => eLpNorm
      (aux_indicator (Set.Icc 0 1) - b.smoothingPartialSum N) 2 volume)
      atTop (nhds 0) := by
    unfold aux_convergesInL2 at h
    convert h using 1
    funext N
    rw [show (aux_indicator (Set.Icc 0 1) - b.smoothingPartialSum N) =
        -(fun x => b.smoothingPartialSum N x - aux_indicator (Set.Icc 0 1) x) by
          funext x
          simp]
    exact eLpNorm_neg _ _ _
  simpa only [heq] using h'

theorem aux_mainTwisted_oneRescaled_memLp {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    {t : ℝ} (ht : 0 < t) :
    MemLp (aux_oneRescaled t g) 2 volume := by
  let m : ℝ → ℝ := fun x => t⁻¹ * x
  have hm : AEMeasurable m volume := by
    dsimp [m]
    fun_prop
  have hmap : Measure.map m volume = ENNReal.ofReal t • volume := by
    rw [show m = fun x : ℝ => t⁻¹ * x by rfl,
      Real.map_volume_mul_left (inv_ne_zero ht.ne')]
    simp [abs_of_pos ht]
  have hgscaled : MemLp g 2 (ENNReal.ofReal t • volume) :=
    hg.smul_measure (by simp)
  have hgmap : MemLp g 2 (Measure.map m volume) := by
    rw [hmap]
    exact hgscaled
  have hmeas : AEStronglyMeasurable (g ∘ m) volume := by
    apply AEStronglyMeasurable.comp_aemeasurable
      hgmap.aestronglyMeasurable
    exact hm
  have hnorm : eLpNorm (g ∘ m) 2 volume < ∞ := by
    rw [← eLpNorm_map_measure hgmap.aestronglyMeasurable hm, hmap]
    exact hgscaled.2
  have hcomp : MemLp (g ∘ m) 2 volume := ⟨hmeas, hnorm⟩
  have heq : aux_oneRescaled t g = (t⁻¹) • (g ∘ m) := by
    funext x
    simp [aux_oneRescaled, m, Pi.smul_apply]
  rw [heq]
  exact hcomp.const_smul _

theorem aux_mainTwisted_oneRescaled_eLpNorm_eq {g : ℝ → ℝ} (hg : MemLp g 2 volume)
    {t : ℝ} (ht : 0 < t) :
    eLpNorm (aux_oneRescaled t g) 2 volume =
      ‖t⁻¹‖ₑ * ((ENNReal.ofReal t) ^ (1 / (2 : ℝ≥0∞)).toReal) *
        eLpNorm g 2 volume := by
  let m : ℝ → ℝ := fun x => t⁻¹ * x
  have hm : AEMeasurable m volume := by
    dsimp [m]
    fun_prop
  have hmap : Measure.map m volume = ENNReal.ofReal t • volume := by
    rw [show m = fun x : ℝ => t⁻¹ * x by rfl,
      Real.map_volume_mul_left (inv_ne_zero ht.ne')]
    simp [abs_of_pos ht]
  have hgscaled : MemLp g 2 (ENNReal.ofReal t • volume) :=
    hg.smul_measure (by simp)
  have hgmap : MemLp g 2 (Measure.map m volume) := by
    rw [hmap]
    exact hgscaled
  have heq : aux_oneRescaled t g = (t⁻¹) • (g ∘ m) := by
    funext x
    simp [aux_oneRescaled, m, Pi.smul_apply]
  rw [heq, eLpNorm_const_smul, ← eLpNorm_map_measure hgmap.aestronglyMeasurable hm,
    hmap, eLpNorm_smul_measure_of_ne_zero]
  · rw [smul_eq_mul]
    rw [mul_assoc]
  · exact ENNReal.ofReal_ne_zero_iff.mpr ht

theorem aux_mainTwisted_memLp_of_const_oneRescaled
    {psi chi : ℝ → ℝ} {a lambda : ℝ}
    (hpsi : MemLp psi 2 volume) (ha : a ≠ 0) (hlambda : 0 < lambda)
    (heq : psi = fun x ↦ a * aux_oneRescaled lambda chi x) :
    MemLp chi 2 volume := by
  have hscaled : MemLp (aux_oneRescaled lambda⁻¹ psi) 2 volume :=
    aux_mainTwisted_oneRescaled_memLp hpsi (inv_pos.mpr hlambda)
  have hfun : chi = a⁻¹ • aux_oneRescaled lambda⁻¹ psi := by
    funext x
    rw [heq]
    simp only [Pi.smul_apply, smul_eq_mul, aux_oneRescaled]
    field_simp [ha, hlambda.ne']
  rw [hfun]
  exact hscaled.const_smul _

theorem aux_mainTwisted_phiZero_memLp_of_phiThree_eq
    (b : windowBasedBumpFunctions) (k : ℤ)
    (heq : windowBasedBumpFunctions.phiThree b k =
      fun x ↦ (2 : ℝ) ^ k * aux_oneRescaled ((2 : ℝ) ^ (-k))
        (windowBasedBumpFunctions.phiZero b k) x) :
    MemLp (windowBasedBumpFunctions.phiZero b k) 2 volume := by
  have hthree : MemLp (windowBasedBumpFunctions.phiThree b k) 2 volume := by
    let p := phiThreeSchwartz b k
    have hp : MemLp (fun x ↦ p x) 2 volume := p.memLp 2
    convert hp using 1
    funext x
    exact (phiThreeSchwartz_apply b k x).symm
  exact aux_mainTwisted_memLp_of_const_oneRescaled hthree (by positivity) (by positivity) heq

theorem aux_mainTwisted_phiOne_memLp_of_thetaTilde_eq
    (b : windowBasedBumpFunctions) (k : ℤ)
    (heq : windowBasedBumpFunctions.phiOne b k =
      fun x ↦ (2 : ℝ) ^ k * aux_oneRescaled ((2 : ℝ) ^ k)
        (windowBasedBumpFunctions.thetaTilde b) x) :
    MemLp (windowBasedBumpFunctions.phiOne b k) 2 volume := by
  have htheta : MemLp (windowBasedBumpFunctions.thetaTilde b) 2 volume := by
    let p := thetaTildeSchwartz b
    have hp : MemLp (fun x ↦ p x) 2 volume := p.memLp 2
    convert hp using 1
    funext x
    exact (thetaTildeSchwartz_apply b x).symm
  rw [heq]
  have h := (aux_mainTwisted_oneRescaled_memLp htheta
    (by positivity : 0 < (2 : ℝ) ^ k)).const_smul ((2 : ℝ) ^ k)
  convert h using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]

theorem aux_mainTwisted_phiTwo_memLp_of_phiFour_eq
    (b : windowBasedBumpFunctions) (k : ℤ)
    (heq : windowBasedBumpFunctions.phiTwo b k =
      -aux_oneRescaled ((2 : ℝ) ^ k) (windowBasedBumpFunctions.phiFour b k)) :
    MemLp (windowBasedBumpFunctions.phiTwo b k) 2 volume := by
  have hfour : MemLp (windowBasedBumpFunctions.phiFour b k) 2 volume := by
    let p := phiFourSchwartz b k
    have hp : MemLp (fun x ↦ p x) 2 volume := p.memLp 2
    convert hp using 1
    funext x
    exact (phiFourSchwartz_apply b k x).symm
  rw [heq]
  exact (aux_mainTwisted_oneRescaled_memLp hfour (by positivity : 0 < (2 : ℝ) ^ k)).neg

theorem aux_mainTwisted_scaleDiff_tendsto_zero_L2
    {g : ℕ → ℝ → ℝ} (hmem : ∀ N, MemLp (g N) 2 volume)
    (hconv : Tendsto (fun N ↦ eLpNorm (g N) 2 volume) atTop (nhds 0))
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    Tendsto (fun N ↦ eLpNorm
      (aux_oneRescaled s (g N) - aux_oneRescaled r (g N)) 2 volume)
      atTop (nhds 0) := by
  let cs : ℝ≥0∞ := ‖s⁻¹‖ₑ * ((ENNReal.ofReal s) ^ (1 / (2 : ℝ≥0∞)).toReal)
  let cr : ℝ≥0∞ := ‖r⁻¹‖ₑ * ((ENNReal.ofReal r) ^ (1 / (2 : ℝ≥0∞)).toReal)
  have hnorms (N : ℕ) :
      eLpNorm (aux_oneRescaled s (g N)) 2 volume = cs * eLpNorm (g N) 2 volume := by
    simpa only [cs] using aux_mainTwisted_oneRescaled_eLpNorm_eq (hmem N) hs
  have hnormr (N : ℕ) :
      eLpNorm (aux_oneRescaled r (g N)) 2 volume = cr * eLpNorm (g N) 2 volume := by
    simpa only [cr] using aux_mainTwisted_oneRescaled_eLpNorm_eq (hmem N) hr
  have hcs : cs ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  have hcr : cr ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  have hss : Tendsto (fun N ↦ eLpNorm (aux_oneRescaled s (g N)) 2 volume)
      atTop (nhds 0) := by
    have hmul := ENNReal.Tendsto.const_mul hconv (Or.inr hcs)
    simpa only [hnorms, mul_zero] using hmul
  have hrr : Tendsto (fun N ↦ eLpNorm (aux_oneRescaled r (g N)) 2 volume)
      atTop (nhds 0) := by
    have hmul := ENNReal.Tendsto.const_mul hconv (Or.inr hcr)
    simpa only [hnormr, mul_zero] using hmul
  have hsum : Tendsto (fun N ↦ eLpNorm (aux_oneRescaled s (g N)) 2 volume +
      eLpNorm (aux_oneRescaled r (g N)) 2 volume) atTop (nhds 0) := by
    simpa using hss.add hrr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro N
    exact bot_le
  · intro N
    exact eLpNorm_sub_le
      (aux_mainTwisted_oneRescaled_memLp (hmem N) hs).aestronglyMeasurable
      (aux_mainTwisted_oneRescaled_memLp (hmem N) hr).aestronglyMeasurable (by norm_num)

theorem aux_mainTwisted_jump_norm_le_tsum {n : ℕ} (hn : 2 ≤ n)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (phi : ℝ → ℝ) (phiJ : ℕ → ℝ → ℝ)
    (hphi : MemLp phi 2 volume) (hphiJ : ∀ q, MemLp (phiJ q) 2 volume)
    (hconv : Tendsto (fun N ↦ eLpNorm
      (phi - ∑ q ∈ Finset.range N, phiJ q) 2 volume) atTop (nhds 0))
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    eLpNorm
      (fun x ↦ twistedAverageAtScale s phi (fun i y ↦ f i y) x -
        twistedAverageAtScale r phi (fun i y ↦ f i y) x)
      2 volume ≤
      ∑' q, eLpNorm
        (fun x ↦ twistedAverageAtScale s (phiJ q) (fun i y ↦ f i y) x -
          twistedAverageAtScale r (phiJ q) (fun i y ↦ f i y) x)
        2 volume := by
  let g : ℕ → ℝ → ℝ := fun N ↦ phi - ∑ q ∈ Finset.range N, phiJ q
  have hgmem (N : ℕ) : MemLp (g N) 2 volume := by
    dsimp [g]
    convert hphi.sub (memLp_finsetSum (Finset.range N) (fun q _ ↦ hphiJ q)) using 1
    ext x
    simp only [Pi.sub_apply, Finset.sum_apply]
  have hgconv : Tendsto (fun N ↦ eLpNorm (g N) 2 volume) atTop (nhds 0) := by
    simpa only [g] using hconv
  let delta : (ℝ → ℝ) → ℝ → ℝ := fun u ↦
    aux_oneRescaled s u - aux_oneRescaled r u
  have hdmem : MemLp (delta phi) 2 volume := by
    exact (aux_mainTwisted_oneRescaled_memLp hphi hs).sub
      (aux_mainTwisted_oneRescaled_memLp hphi hr)
  have hdmemJ (q : ℕ) : MemLp (delta (phiJ q)) 2 volume := by
    exact (aux_mainTwisted_oneRescaled_memLp (hphiJ q) hs).sub
      (aux_mainTwisted_oneRescaled_memLp (hphiJ q) hr)
  have hdelta (N : ℕ) :
      delta phi - ∑ q ∈ Finset.range N, delta (phiJ q) =
        aux_oneRescaled s (g N) - aux_oneRescaled r (g N) := by
    funext x
    simp only [delta, g, Pi.sub_apply, Finset.sum_apply, aux_oneRescaled]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hdconv : Tendsto (fun N ↦ eLpNorm
      (delta phi - ∑ q ∈ Finset.range N, delta (phiJ q)) 2 volume)
      atTop (nhds 0) := by
    rw [show (fun N ↦ eLpNorm
      (delta phi - ∑ q ∈ Finset.range N, delta (phiJ q)) 2 volume) =
      fun N ↦ eLpNorm (aux_oneRescaled s (g N) - aux_oneRescaled r (g N)) 2 volume by
        funext N
        rw [hdelta]]
    exact aux_mainTwisted_scaleDiff_tendsto_zero_L2 hgmem hgconv hs hr
  have hsum := normASumLeSum hn (delta phi) (fun q ↦ delta (phiJ q)) f
    hdmem hdmemJ hdconv
  change eLpNorm
      (twistedAverage (aux_oneRescaled s phi) (fun i y ↦ f i y) -
        twistedAverage (aux_oneRescaled r phi) (fun i y ↦ f i y))
      2 volume ≤ _
  rw [← aux_twistedAverage_sub_of_memLp hn f
    (aux_oneRescaled s phi) (aux_oneRescaled r phi)
    (aux_mainTwisted_oneRescaled_memLp hphi hs) (aux_mainTwisted_oneRescaled_memLp hphi hr)]
  calc
    eLpNorm (twistedAverage (delta phi) (fun i y ↦ f i y)) 2 volume ≤
        ∑' q, eLpNorm (twistedAverage (delta (phiJ q))
          (fun i y ↦ f i y)) 2 volume := hsum
    _ = ∑' q, eLpNorm
        (fun x ↦ twistedAverageAtScale s (phiJ q) (fun i y ↦ f i y) x -
          twistedAverageAtScale r (phiJ q) (fun i y ↦ f i y) x)
        2 volume := by
      apply tsum_congr
      intro q
      change eLpNorm
          (twistedAverage (aux_oneRescaled s (phiJ q) - aux_oneRescaled r (phiJ q))
            (fun i y ↦ f i y)) 2 volume =
          eLpNorm
            (twistedAverage (aux_oneRescaled s (phiJ q)) (fun i y ↦ f i y) -
              twistedAverage (aux_oneRescaled r (phiJ q)) (fun i y ↦ f i y))
            2 volume
      rw [aux_twistedAverage_sub_of_memLp hn f
        (aux_oneRescaled s (phiJ q)) (aux_oneRescaled r (phiJ q))
        (aux_mainTwisted_oneRescaled_memLp (hphiJ q) hs)
        (aux_mainTwisted_oneRescaled_memLp (hphiJ q) hr)]

theorem aux_mainTwisted_jump_norm_add_le {n J : ℕ} (hn : 2 ≤ n)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (t : aux_scaleChain J) (j : Fin J) (u v : ℝ → ℝ)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    eLpNorm
      (fun x ↦ twistedAverageAtScale (t.1 j.succ) (u + v) (fun i y ↦ f i y) x -
        twistedAverageAtScale (t.1 j.castSucc) (u + v) (fun i y ↦ f i y) x)
      2 volume ≤
      eLpNorm
        (fun x ↦ twistedAverageAtScale (t.1 j.succ) u (fun i y ↦ f i y) x -
          twistedAverageAtScale (t.1 j.castSucc) u (fun i y ↦ f i y) x)
        2 volume +
      eLpNorm
        (fun x ↦ twistedAverageAtScale (t.1 j.succ) v (fun i y ↦ f i y) x -
          twistedAverageAtScale (t.1 j.castSucc) v (fun i y ↦ f i y) x)
        2 volume := by
  let s : ℝ := t.1 j.succ
  let r : ℝ := t.1 j.castSucc
  have hs : 0 < s := t.2.2 _
  have hr : 0 < r := t.2.2 _
  have hus : MemLp (aux_oneRescaled s u) 2 volume :=
    aux_mainTwisted_oneRescaled_memLp hu hs
  have hvs : MemLp (aux_oneRescaled s v) 2 volume :=
    aux_mainTwisted_oneRescaled_memLp hv hs
  have hur : MemLp (aux_oneRescaled r u) 2 volume :=
    aux_mainTwisted_oneRescaled_memLp hu hr
  have hvr : MemLp (aux_oneRescaled r v) 2 volume :=
    aux_mainTwisted_oneRescaled_memLp hv hr
  have hscale_add (a : ℝ) :
      aux_oneRescaled a (u + v) = aux_oneRescaled a u + aux_oneRescaled a v := by
    funext x
    simp only [aux_oneRescaled, Pi.add_apply]
    ring
  have hsumS : twistedAverage (aux_oneRescaled s (u + v)) (fun i y ↦ f i y) =
      twistedAverage (aux_oneRescaled s u) (fun i y ↦ f i y) +
        twistedAverage (aux_oneRescaled s v) (fun i y ↦ f i y) := by
    rw [hscale_add]
    exact aux_twistedAverage_add_of_memLp hn f
      (aux_oneRescaled s u) (aux_oneRescaled s v) hus hvs
  have hsumR : twistedAverage (aux_oneRescaled r (u + v)) (fun i y ↦ f i y) =
      twistedAverage (aux_oneRescaled r u) (fun i y ↦ f i y) +
        twistedAverage (aux_oneRescaled r v) (fun i y ↦ f i y) := by
    rw [hscale_add]
    exact aux_twistedAverage_add_of_memLp hn f
      (aux_oneRescaled r u) (aux_oneRescaled r v) hur hvr
  change eLpNorm
      (twistedAverage (aux_oneRescaled s (u + v)) (fun i y ↦ f i y) -
        twistedAverage (aux_oneRescaled r (u + v)) (fun i y ↦ f i y))
      2 volume ≤
      eLpNorm
        (twistedAverage (aux_oneRescaled s u) (fun i y ↦ f i y) -
          twistedAverage (aux_oneRescaled r u) (fun i y ↦ f i y))
        2 volume +
      eLpNorm
        (twistedAverage (aux_oneRescaled s v) (fun i y ↦ f i y) -
          twistedAverage (aux_oneRescaled r v) (fun i y ↦ f i y))
        2 volume
  rw [hsumS, hsumR]
  have hmeasU : AEStronglyMeasurable
      (twistedAverage (aux_oneRescaled s u) (fun i y ↦ f i y) -
        twistedAverage (aux_oneRescaled r u) (fun i y ↦ f i y)) volume :=
    ((aux_twistedAverage_memLp hn f (aux_oneRescaled s u) hus).sub
      (aux_twistedAverage_memLp hn f (aux_oneRescaled r u) hur)).aestronglyMeasurable
  have hmeasV : AEStronglyMeasurable
      (twistedAverage (aux_oneRescaled s v) (fun i y ↦ f i y) -
        twistedAverage (aux_oneRescaled r v) (fun i y ↦ f i y)) volume :=
    ((aux_twistedAverage_memLp hn f (aux_oneRescaled s v) hvs).sub
      (aux_twistedAverage_memLp hn f (aux_oneRescaled r v) hvr)).aestronglyMeasurable
  calc
    eLpNorm
        ((twistedAverage (aux_oneRescaled s u) (fun i y ↦ f i y) +
            twistedAverage (aux_oneRescaled s v) (fun i y ↦ f i y)) -
          (twistedAverage (aux_oneRescaled r u) (fun i y ↦ f i y) +
            twistedAverage (aux_oneRescaled r v) (fun i y ↦ f i y)))
        2 volume =
        eLpNorm
          ((twistedAverage (aux_oneRescaled s u) (fun i y ↦ f i y) -
              twistedAverage (aux_oneRescaled r u) (fun i y ↦ f i y)) +
            (twistedAverage (aux_oneRescaled s v) (fun i y ↦ f i y) -
              twistedAverage (aux_oneRescaled r v) (fun i y ↦ f i y)))
          2 volume := by
            congr 1
            funext x
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
    _ ≤ _ := eLpNorm_add_le hmeasU hmeasV (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem aux_mainTwisted_s0_expand (b : windowBasedBumpFunctions) :
    b.smoothingPartialSum 0 =
      fun x => b.phi0 x +
        (windowBasedBumpFunctions.phiZero b (-2) x +
          (windowBasedBumpFunctions.phiZero b (-1) x +
            windowBasedBumpFunctions.phiZero b 0 x)) := by
  funext x
  simp only [windowBasedBumpFunctions.smoothingPartialSum, aux_integerIntervalSum]
  have hset : Finset.Icc (-2 : ℤ) 0 = {-2, -1, 0} := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  change b.phi0 x + (∑ j ∈ Finset.Icc (-2 : ℤ) 0, b.phiZero j x) +
      (∑ j ∈ Finset.Icc (0 : ℤ) (-1),
        (b.phiOne j x + b.phiTwo j x)) = _
  rw [hset]
  simp

noncomputable def aux_mainTwisted_jumpNorm {n J : ℕ}
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (t : aux_scaleChain J) (j : Fin J) (chi : ℝ → ℝ) : ℝ≥0∞ :=
  eLpNorm
    (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi (fun i y ↦ f i y) x -
      twistedAverageAtScale (t.1 j.castSucc) chi (fun i y ↦ f i y) x)
    2 volume

theorem aux_mainTwisted_jumpNorm_add_le {n J : ℕ} (hn : 2 ≤ n)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (t : aux_scaleChain J) (j : Fin J) (u v : ℝ → ℝ)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    aux_mainTwisted_jumpNorm f t j (u + v) ≤
      aux_mainTwisted_jumpNorm f t j u + aux_mainTwisted_jumpNorm f t j v := by
  simpa only [aux_mainTwisted_jumpNorm] using
    aux_mainTwisted_jump_norm_add_le hn f t j u v hu hv

/-- Pointwise smoothing decomposition for one adjacent pair of scales. -/
theorem aux_mainTwisted_pointwise_smoothing_bound {n J : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (t : aux_scaleChain J) (j : Fin J)
    (hI : MemLp (aux_indicator (Set.Icc (0 : ℝ) 1)) 2 volume)
    (hphi0 : MemLp (fun x ↦ b.phi0 x) 2 volume)
    (hzero : ∀ k : ℤ, MemLp (windowBasedBumpFunctions.phiZero b k) 2 volume)
    (hone : ∀ k : ℤ, MemLp (windowBasedBumpFunctions.phiOne b k) 2 volume)
    (htwo : ∀ k : ℤ, MemLp (windowBasedBumpFunctions.phiTwo b k) 2 volume) :
    aux_mainTwisted_jumpNorm f t j (aux_indicator (Set.Icc (0 : ℝ) 1)) ≤
      aux_mainTwisted_jumpNorm f t j (fun x ↦ b.phi0 x) +
        (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-2)) +
          (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-1)) +
            aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b 0)) +
          ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
            (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))) +
        ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
          (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ))) +
        ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
          (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ))) := by
  have hs0mem : MemLp (b.smoothingPartialSum 0) 2 volume := by
    rw [aux_mainTwisted_s0_expand]
    exact hphi0.add ((hzero (-2)).add ((hzero (-1)).add (hzero 0)))
  have hresmem : MemLp
      (aux_indicator (Set.Icc (0 : ℝ) 1) - b.smoothingPartialSum 0) 2 volume :=
    hI.sub hs0mem
  have hdeltamem (q : ℕ) : MemLp (aux_mainTwisted_delta b q) 2 volume := by
    rw [aux_mainTwisted_delta_expand]
    have hrest : MemLp
        (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)) +
          windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ))) 2 volume :=
      (hone (-((q + 1 : ℕ) : ℤ))).add (htwo (-((q + 1 : ℕ) : ℤ)))
    exact (hzero ((q + 1 : ℕ) : ℤ)).add hrest
  have hresidual : aux_mainTwisted_jumpNorm f t j
      (aux_indicator (Set.Icc (0 : ℝ) 1) - b.smoothingPartialSum 0) ≤
      ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j (aux_mainTwisted_delta b q) := by
    simpa only [aux_mainTwisted_jumpNorm] using
      aux_mainTwisted_jump_norm_le_tsum hn f
        (aux_indicator (Set.Icc (0 : ℝ) 1) - b.smoothingPartialSum 0)
        (aux_mainTwisted_delta b) hresmem hdeltamem (aux_mainTwisted_delta_converges b)
        (t.2.2 _) (t.2.2 _)
  have hdelta (q : ℕ) : aux_mainTwisted_jumpNorm f t j (aux_mainTwisted_delta b q) ≤
      aux_mainTwisted_jumpNorm f t j
          (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ)) +
        (aux_mainTwisted_jumpNorm f t j
            (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ))) +
          aux_mainTwisted_jumpNorm f t j
            (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))) := by
    rw [aux_mainTwisted_delta_expand]
    let z : ℝ → ℝ := windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ)
    let o : ℝ → ℝ := windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ))
    let w : ℝ → ℝ := windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ))
    have hz : MemLp z 2 volume := by
      dsimp [z]
      exact hzero _
    have ho : MemLp o 2 volume := by
      dsimp [o]
      exact hone _
    have hw : MemLp w 2 volume := by
      dsimp [w]
      exact htwo _
    change aux_mainTwisted_jumpNorm f t j (z + (o + w)) ≤
      aux_mainTwisted_jumpNorm f t j z +
        (aux_mainTwisted_jumpNorm f t j o + aux_mainTwisted_jumpNorm f t j w)
    exact (aux_mainTwisted_jumpNorm_add_le hn f t j z (o + w) hz (ho.add hw)).trans
      (add_le_add_right (aux_mainTwisted_jumpNorm_add_le hn f t j o w ho hw) _)
  have hsumdelta : ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j (aux_mainTwisted_delta b q) ≤
      (∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
          (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))) +
        ((∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
            (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))) +
          ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
            (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))) := by
    let z : ℕ → ℝ≥0∞ := fun q ↦ aux_mainTwisted_jumpNorm f t j
      (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))
    let o : ℕ → ℝ≥0∞ := fun q ↦ aux_mainTwisted_jumpNorm f t j
      (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))
    let w : ℕ → ℝ≥0∞ := fun q ↦ aux_mainTwisted_jumpNorm f t j
      (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))
    change (∑' q : ℕ, aux_mainTwisted_jumpNorm f t j (aux_mainTwisted_delta b q)) ≤
      (∑' q : ℕ, z q) + ((∑' q : ℕ, o q) + ∑' q : ℕ, w q)
    calc
      ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j (aux_mainTwisted_delta b q) ≤
          ∑' q : ℕ, (z q + (o q + w q)) := by
        apply ENNReal.tsum_le_tsum
        intro q
        exact hdelta q
      _ = _ := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
  have hs0bound : aux_mainTwisted_jumpNorm f t j (b.smoothingPartialSum 0) ≤
      aux_mainTwisted_jumpNorm f t j (fun x ↦ b.phi0 x) +
        (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-2)) +
          (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-1)) +
            aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b 0))) := by
    rw [aux_mainTwisted_s0_expand]
    let p : ℝ → ℝ := fun x ↦ b.phi0 x
    let z2 : ℝ → ℝ := windowBasedBumpFunctions.phiZero b (-2)
    let z1 : ℝ → ℝ := windowBasedBumpFunctions.phiZero b (-1)
    let z0 : ℝ → ℝ := windowBasedBumpFunctions.phiZero b 0
    have hp : MemLp p 2 volume := by
      dsimp [p]
      exact hphi0
    have hz2 : MemLp z2 2 volume := by
      dsimp [z2]
      exact hzero _
    have hz1 : MemLp z1 2 volume := by
      dsimp [z1]
      exact hzero _
    have hz0 : MemLp z0 2 volume := by
      dsimp [z0]
      exact hzero _
    change aux_mainTwisted_jumpNorm f t j (p + (z2 + (z1 + z0))) ≤
      aux_mainTwisted_jumpNorm f t j p +
        (aux_mainTwisted_jumpNorm f t j z2 +
          (aux_mainTwisted_jumpNorm f t j z1 + aux_mainTwisted_jumpNorm f t j z0))
    exact (aux_mainTwisted_jumpNorm_add_le hn f t j p (z2 + (z1 + z0)) hp
      (hz2.add (hz1.add hz0))).trans
      (add_le_add_right
        ((aux_mainTwisted_jumpNorm_add_le hn f t j z2 (z1 + z0) hz2 (hz1.add hz0)).trans
          (add_le_add_right
            (aux_mainTwisted_jumpNorm_add_le hn f t j z1 z0 hz1 hz0) _)) _)
  have hsplit : aux_mainTwisted_jumpNorm f t j
      (aux_indicator (Set.Icc (0 : ℝ) 1)) ≤
      aux_mainTwisted_jumpNorm f t j (b.smoothingPartialSum 0) +
        aux_mainTwisted_jumpNorm f t j
          (aux_indicator (Set.Icc (0 : ℝ) 1) - b.smoothingPartialSum 0) := by
    calc
      aux_mainTwisted_jumpNorm f t j (aux_indicator (Set.Icc (0 : ℝ) 1)) =
          aux_mainTwisted_jumpNorm f t j (b.smoothingPartialSum 0 +
            (aux_indicator (Set.Icc (0 : ℝ) 1) - b.smoothingPartialSum 0)) := by
        congr 1
        funext x
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      _ ≤ _ := aux_mainTwisted_jumpNorm_add_le hn f t j _ _ hs0mem hresmem
  calc
    aux_mainTwisted_jumpNorm f t j (aux_indicator (Set.Icc (0 : ℝ) 1)) ≤
        aux_mainTwisted_jumpNorm f t j (b.smoothingPartialSum 0) +
          aux_mainTwisted_jumpNorm f t j
            (aux_indicator (Set.Icc (0 : ℝ) 1) - b.smoothingPartialSum 0) := hsplit
    _ ≤ (aux_mainTwisted_jumpNorm f t j (fun x ↦ b.phi0 x) +
          (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-2)) +
            (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-1)) +
              aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b 0)))) +
          ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j (aux_mainTwisted_delta b q) :=
      add_le_add hs0bound hresidual
    _ ≤ (aux_mainTwisted_jumpNorm f t j (fun x ↦ b.phi0 x) +
          (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-2)) +
            (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-1)) +
              aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b 0)))) +
          ((∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
              (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))) +
            ((∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
                (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))) +
              ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
                (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ))))) :=
      add_le_add_right hsumdelta _
    _ = _ := by ac_rfl

/-- Pure ENNReal bookkeeping for the final four-family square estimate. -/
theorem aux_mainTwisted_four_family_aggregation
    {R E0 E1 E2 E3 : ℝ≥0∞} {C0 C1 C2 C3 : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (h0 : E0 ≤ ENNReal.ofReal C0 * R)
    (h1 : E1 ≤ (64 : ℝ≥0∞) * (ENNReal.ofReal C1 * R))
    (h2 : E2 ≤ ENNReal.ofReal C2 * R)
    (h3 : E3 ≤ (64 : ℝ≥0∞) * (ENNReal.ofReal C3 * R)) :
    (4 : ℝ≥0∞) * (E0 + E1 + E2 + E3) ≤
      ENNReal.ofReal (4 * (C0 + 64 * C1 + C2 + 64 * C3)) * R := by
  have h64C1 : 0 ≤ 64 * C1 := mul_nonneg (by norm_num) hC1
  have h64C3 : 0 ≤ 64 * C3 := mul_nonneg (by norm_num) hC3
  have h01 : 0 ≤ C0 + 64 * C1 := add_nonneg hC0 h64C1
  have h012 : 0 ≤ C0 + 64 * C1 + C2 := add_nonneg h01 hC2
  have hsum :
      E0 + E1 + E2 + E3 ≤
        (ENNReal.ofReal C0 + 64 * ENNReal.ofReal C1 + ENNReal.ofReal C2 +
          64 * ENNReal.ofReal C3) * R := by
    calc
      E0 + E1 + E2 + E3 ≤
          (ENNReal.ofReal C0 * R) +
            (64 * (ENNReal.ofReal C1 * R)) +
            (ENNReal.ofReal C2 * R) +
            (64 * (ENNReal.ofReal C3 * R)) := by
              gcongr
      _ = (ENNReal.ofReal C0 + 64 * ENNReal.ofReal C1 + ENNReal.ofReal C2 +
          64 * ENNReal.ofReal C3) * R := by ring
  calc
    (4 : ℝ≥0∞) * (E0 + E1 + E2 + E3) ≤
        (4 : ℝ≥0∞) *
          ((ENNReal.ofReal C0 + 64 * ENNReal.ofReal C1 + ENNReal.ofReal C2 +
            64 * ENNReal.ofReal C3) * R) := by
              gcongr
    _ = ENNReal.ofReal (4 * (C0 + 64 * C1 + C2 + 64 * C3)) * R := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [ENNReal.ofReal_add h012 h64C3]
      rw [ENNReal.ofReal_add h01 hC2]
      rw [ENNReal.ofReal_add hC0 h64C1]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      norm_num
      ring

theorem aux_mainTwisted_four_family_aggregation_ofReal_weights
    {R E0 E1 E2 E3 : ℝ≥0∞} {C0 C1 C2 C3 : ℝ}
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (h0 : E0 ≤ ENNReal.ofReal C0 * R)
    (h1 : E1 ≤ ENNReal.ofReal (64 * C1) * R)
    (h2 : E2 ≤ ENNReal.ofReal C2 * R)
    (h3 : E3 ≤ ENNReal.ofReal (64 * C3) * R) :
    (4 : ℝ≥0∞) * (E0 + E1 + E2 + E3) ≤
      ENNReal.ofReal (4 * (C0 + 64 * C1 + C2 + 64 * C3)) * R := by
  apply aux_mainTwisted_four_family_aggregation hC0 hC1 hC2 hC3 h0
  · simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64), mul_assoc] using h1
  · exact h2
  · simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64), mul_assoc] using h3

theorem aux_mainTwisted_four_family_aggregation_main_constant {n : ℕ}
    {R E0 E1 E2 E3 : ℝ≥0∞}
    (hC0 : 0 ≤ C_mainBumpOne n) (hC1 : 0 ≤ C_mainBumpTwo n)
    (hC2 : 0 ≤ C_leftBump n) (hC3 : 0 ≤ C_leftBumpOne n)
    (h0 : E0 ≤ ENNReal.ofReal (C_mainBumpOne n) * R)
    (h1 : E1 ≤ ENNReal.ofReal (64 * C_mainBumpTwo n) * R)
    (h2 : E2 ≤ ENNReal.ofReal (C_leftBump n) * R)
    (h3 : E3 ≤ ENNReal.ofReal (64 * C_leftBumpOne n) * R) :
    (4 : ℝ≥0∞) * (E0 + E1 + E2 + E3) ≤
      ENNReal.ofReal (C_mainTwistedTheorem n) * R := by
  have hC : C_mainTwistedTheorem n =
      4 * (C_mainBumpOne n + 64 * C_mainBumpTwo n + C_leftBump n +
        64 * C_leftBumpOne n) := by
    norm_num [C_mainTwistedTheorem]
  rw [hC]
  exact aux_mainTwisted_four_family_aggregation_ofReal_weights hC0 hC1 hC2 hC3 h0 h1 h2 h3

theorem aux_mainTwisted_ennreal_add_sq_le (u v : ℝ≥0∞) :
    (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow u v (p := (2 : ℝ))
    (by norm_num)
  have htwo : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  simpa [ENNReal.rpow_two, htwo] using h

theorem aux_mainTwisted_ennreal_four_add_sq_le (a b c d : ℝ≥0∞) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  calc
    (a + b + c + d) ^ 2 = ((a + b) + (c + d)) ^ 2 := by ring
    _ ≤ 2 * ((a + b) ^ 2 + (c + d) ^ 2) :=
      aux_mainTwisted_ennreal_add_sq_le _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + 2 * (c ^ 2 + d ^ 2)) := by
      gcongr
      · exact aux_mainTwisted_ennreal_add_sq_le _ _
      · exact aux_mainTwisted_ennreal_add_sq_le _ _
    _ = 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by ring

theorem aux_mainTwisted_finset_four_family_square {ι : Type*} (s : Finset ι)
    (a b c d : ι → ℝ≥0∞) :
    (∑ i ∈ s, (a i + b i + c i + d i) ^ 2) ≤
      4 * ((∑ i ∈ s, a i ^ 2) + (∑ i ∈ s, b i ^ 2) +
        (∑ i ∈ s, c i ^ 2) + (∑ i ∈ s, d i ^ 2)) := by
  calc
    (∑ i ∈ s, (a i + b i + c i + d i) ^ 2) ≤
        ∑ i ∈ s, 4 * (a i ^ 2 + b i ^ 2 + c i ^ 2 + d i ^ 2) := by
          exact Finset.sum_le_sum fun i hi => aux_mainTwisted_ennreal_four_add_sq_le _ _ _ _
    _ = 4 * ((∑ i ∈ s, a i ^ 2) + (∑ i ∈ s, b i ^ 2) +
        (∑ i ∈ s, c i ^ 2) + (∑ i ∈ s, d i ^ 2)) := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The terminal reduction: pointwise smoothing plus four family energy bounds. -/
theorem aux_mainTwisted_terminal_aggregation {n J : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (t : aux_scaleChain J) (R : ℝ≥0∞)
    (hI : MemLp (aux_indicator (Set.Icc (0 : ℝ) 1)) 2 volume)
    (hphi0 : MemLp (fun x ↦ b.phi0 x) 2 volume)
    (hzero : ∀ k : ℤ, MemLp (windowBasedBumpFunctions.phiZero b k) 2 volume)
    (hone : ∀ k : ℤ, MemLp (windowBasedBumpFunctions.phiOne b k) 2 volume)
    (htwo : ∀ k : ℤ, MemLp (windowBasedBumpFunctions.phiTwo b k) 2 volume)
    (hC0 : 0 ≤ C_mainBumpOne n) (hC1 : 0 ≤ C_mainBumpTwo n)
    (hC2 : 0 ≤ C_leftBump n) (hC3 : 0 ≤ C_leftBumpOne n)
    (h0 : ∑ j : Fin J, (aux_mainTwisted_jumpNorm f t j (fun x ↦ b.phi0 x)) ^ 2 ≤
      ENNReal.ofReal (C_mainBumpOne n) * R)
    (h1 : ∑ j : Fin J,
        (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-2)) +
          (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-1)) +
            aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b 0)) +
          ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
            (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))) ^ 2 ≤
      ENNReal.ofReal (64 * C_mainBumpTwo n) * R)
    (h2 : ∑ j : Fin J,
        (∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
          (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))) ^ 2 ≤
      ENNReal.ofReal (C_leftBump n) * R)
    (h3 : ∑ j : Fin J,
        (∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
          (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))) ^ 2 ≤
      ENNReal.ofReal (64 * C_leftBumpOne n) * R) :
    ∑ j : Fin J,
      (aux_mainTwisted_jumpNorm f t j (aux_indicator (Set.Icc (0 : ℝ) 1))) ^ 2 ≤
      ENNReal.ofReal (C_mainTwistedTheorem n) * R := by
  let a : Fin J → ℝ≥0∞ := fun j ↦ aux_mainTwisted_jumpNorm f t j (fun x ↦ b.phi0 x)
  let z : Fin J → ℝ≥0∞ := fun j ↦
    aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-2)) +
      (aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b (-1)) +
        aux_mainTwisted_jumpNorm f t j (windowBasedBumpFunctions.phiZero b 0)) +
      ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
        (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))
  let o : Fin J → ℝ≥0∞ := fun j ↦ ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
    (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))
  let w : Fin J → ℝ≥0∞ := fun j ↦ ∑' q : ℕ, aux_mainTwisted_jumpNorm f t j
    (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))
  have hpoint (j : Fin J) :
      aux_mainTwisted_jumpNorm f t j (aux_indicator (Set.Icc (0 : ℝ) 1)) ≤
        a j + z j + o j + w j := by
    dsimp only [a, z, o, w]
    simpa only [add_assoc] using
      aux_mainTwisted_pointwise_smoothing_bound hn b f t j hI hphi0 hzero hone htwo
  have hsum : ∑ j : Fin J,
      (aux_mainTwisted_jumpNorm f t j (aux_indicator (Set.Icc (0 : ℝ) 1))) ^ 2 ≤
      ∑ j : Fin J, (a j + z j + o j + w j) ^ 2 := by
    exact Finset.sum_le_sum fun j _ => pow_le_pow_left' (hpoint j) 2
  have ha : (∑ j : Fin J, a j ^ 2) ≤ ENNReal.ofReal (C_mainBumpOne n) * R := by
    simpa only [a] using h0
  have hz : (∑ j : Fin J, z j ^ 2) ≤ ENNReal.ofReal (64 * C_mainBumpTwo n) * R := by
    simpa only [z] using h1
  have ho : (∑ j : Fin J, o j ^ 2) ≤ ENNReal.ofReal (C_leftBump n) * R := by
    simpa only [o] using h2
  have hw : (∑ j : Fin J, w j ^ 2) ≤ ENNReal.ofReal (64 * C_leftBumpOne n) * R := by
    simpa only [w] using h3
  calc
    ∑ j : Fin J,
        (aux_mainTwisted_jumpNorm f t j (aux_indicator (Set.Icc (0 : ℝ) 1))) ^ 2 ≤
        ∑ j : Fin J, (a j + z j + o j + w j) ^ 2 := hsum
    _ ≤ 4 * ((∑ j : Fin J, a j ^ 2) + (∑ j : Fin J, z j ^ 2) +
        (∑ j : Fin J, o j ^ 2) + (∑ j : Fin J, w j ^ 2)) :=
      aux_mainTwisted_finset_four_family_square Finset.univ a z o w
    _ ≤ ENNReal.ofReal (C_mainTwistedTheorem n) * R :=
      aux_mainTwisted_four_family_aggregation_main_constant hC0 hC1 hC2 hC3 ha hz ho hw

/-- Exact conversion of `mainBumpOne` to the terminal component-energy shape. -/
theorem aux_mainTwisted_mainBumpOne_energy {n J : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (t : aux_scaleChain J) (hJ : 0 < J) :
    ∑ j : Fin J, (aux_mainTwisted_jumpNorm f.1 t j (fun x ↦ b.phi0 x)) ^ 2 ≤
      ENNReal.ofReal (C_mainBumpOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  have h := mainBumpOne hn b.phi0 b.phi1 b.universalPair f J hJ t
  simpa only [aux_mainTwisted_jumpNorm, aux_jumpEnergy, twistedJumpEnergy] using h

open Filter Finset MeasureTheory
open scoped BigOperators ENNReal NNReal Real

theorem aux_mainTwisted_weighted_tsum_sq_of_sq_le {J : ℕ}
    (a : ℕ → Fin J → ℝ≥0∞) (u : ℕ → ℝ≥0∞) (e : ℕ → Fin J → ℝ≥0∞)
    (h : ∀ q j, (a q j) ^ 2 ≤ u q * e q j) :
    ∑ j, (∑' q, a q j) ^ 2 ≤
      (∑' q, u q) * ∑' q, ∑ j, e q j := by
  have hroot : ∀ q j, a q j ≤ (u q) ^ (1 / (2 : ℝ)) * (e q j) ^ (1 / (2 : ℝ)) := by
    intro q j
    calc
      a q j = ((a q j) ^ 2) ^ (1 / (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      _ ≤ (u q * e q j) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (h q j) (by positivity)
      _ = (u q) ^ (1 / (2 : ℝ)) * (e q j) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
  have hsquare : ∀ j : Fin J,
      (∑' q, a q j) ^ 2 ≤ (∑' q, u q) * ∑' q, e q j := by
    intro j
    have htsum : ∑' q, a q j ≤
        (∑' q, ((u q) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' q, ((e q j) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      apply ENNReal.tsum_le_of_sum_range_le
      intro N
      calc
        ∑ q ∈ Finset.range N, a q j ≤
            ∑ q ∈ Finset.range N, (u q) ^ (1 / (2 : ℝ)) *
              (e q j) ^ (1 / (2 : ℝ)) :=
          Finset.sum_le_sum fun q _ => hroot q j
        _ ≤ (∑ q ∈ Finset.range N, ((u q) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^
              (1 / (2 : ℝ)) *
            (∑ q ∈ Finset.range N, ((e q j) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^
              (1 / (2 : ℝ)) :=
          ENNReal.inner_le_Lp_mul_Lq (Finset.range N)
            (fun q => (u q) ^ (1 / (2 : ℝ)))
            (fun q => (e q j) ^ (1 / (2 : ℝ))) Real.HolderConjugate.two_two
        _ ≤ (∑' q, ((u q) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∑' q, ((e q j) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
          gcongr <;> exact ENNReal.sum_le_tsum _
    calc
      (∑' q, a q j) ^ 2 ≤
          ((∑' q, ((u q) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∑' q, ((e q j) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left' htsum 2
      _ = (∑' q, u q) * ∑' q, e q j := by
        simp only [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  calc
    ∑ j, (∑' q, a q j) ^ 2 ≤
        ∑ j, (∑' q, u q) * ∑' q, e q j :=
      Finset.sum_le_sum fun j _ => hsquare j
    _ = (∑' q, u q) * ∑ j, ∑' q, e q j := by rw [Finset.mul_sum]
    _ = (∑' q, u q) * ∑' q, ∑ j, e q j := by
      congr 1
      rw [← tsum_fintype (L := .unconditional _) (fun j : Fin J => ∑' q, e q j)]
      rw [← ENNReal.tsum_comm]
      apply tsum_congr
      intro q
      exact tsum_fintype (L := .unconditional _) _

theorem aux_mainTwisted_weighted_tsum_energy_bound {J : ℕ}
    (a : ℕ → Fin J → ℝ≥0∞) (v B : ℕ → ℝ≥0∞) (P U V : ℝ≥0∞)
    (hv0 : ∀ q, v q ≠ 0) (hvt : ∀ q, v q ≠ ∞)
    (henergy : ∀ q, ∑ j, (a q j) ^ 2 ≤ B q * P)
    (hU : (∑' q, (v q)⁻¹) ≤ U)
    (hV : (∑' q, v q * B q) ≤ V) :
    ∑ j, (∑' q, a q j) ^ 2 ≤ U * (V * P) := by
  let u : ℕ → ℝ≥0∞ := fun q ↦ (v q)⁻¹
  let e : ℕ → Fin J → ℝ≥0∞ := fun q j ↦ v q * (a q j) ^ 2
  have hpoint (q : ℕ) (j : Fin J) : (a q j) ^ 2 ≤ u q * e q j := by
    dsimp [u, e]
    rw [← mul_assoc, ENNReal.inv_mul_cancel (hv0 q) (hvt q), one_mul]
  have hmain := aux_mainTwisted_weighted_tsum_sq_of_sq_le a u e hpoint
  have hinner (q : ℕ) : ∑ j, e q j = v q * ∑ j, (a q j) ^ 2 := by
    dsimp [e]
    rw [← Finset.mul_sum]
  calc
    ∑ j, (∑' q, a q j) ^ 2 ≤ (∑' q, u q) * ∑' q, ∑ j, e q j := hmain
    _ = (∑' q, (v q)⁻¹) * ∑' q, v q * ∑ j, (a q j) ^ 2 := by
      dsimp [u]
      congr 1
      apply tsum_congr
      intro q
      exact hinner q
    _ ≤ (∑' q, (v q)⁻¹) * ∑' q, (v q * B q) * P := by
      have hterm (q : ℕ) : v q * ∑ j, (a q j) ^ 2 ≤ (v q * B q) * P := by
        calc
          v q * ∑ j, (a q j) ^ 2 ≤ v q * (B q * P) :=
            mul_le_mul_right (henergy q) (v q)
          _ = (v q * B q) * P := by ring
      apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      exact hterm
    _ = (∑' q, (v q)⁻¹) * ((∑' q, v q * B q) * P) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ U * (V * P) := by gcongr

theorem aux_mainTwisted_halfHeightTsum (C : ℝ) (hC : 0 ≤ C) :
    (∑' h : ℕ, ENNReal.ofReal (C * (1 / 2 : ℝ) ^ h)) ≤
      ENNReal.ofReal (2 * C) := by
  let r : ℝ := 1 / 2
  have hrlt : ‖r‖ < 1 := by
    dsimp [r]
    norm_num [Real.norm_eq_abs]
  have hrsum : Summable (fun h : ℕ => r ^ h) :=
    summable_geometric_of_norm_lt_one hrlt
  have hactual : Summable (fun h : ℕ => C * (1 / 2 : ℝ) ^ h) := by
    simpa only [r] using hrsum.mul_left C
  have hsum : (∑' h : ℕ, C * (1 / 2 : ℝ) ^ h) ≤ 2 * C := by
    calc
      (∑' h : ℕ, C * (1 / 2 : ℝ) ^ h) = C * (∑' h : ℕ, r ^ h) := by
        rw [tsum_mul_left]
      _ = C * ((1 - r)⁻¹) := by rw [tsum_geometric_of_norm_lt_one hrlt]
      _ = 2 * C := by dsimp [r]; norm_num; ring
      _ ≤ 2 * C := le_rfl
  have hnonneg (h : ℕ) : 0 ≤ C * (1 / 2 : ℝ) ^ h :=
    mul_nonneg hC (pow_nonneg (by norm_num) _)
  calc
    (∑' h : ℕ, ENNReal.ofReal (C * (1 / 2 : ℝ) ^ h)) =
        ENNReal.ofReal (∑' h : ℕ, C * (1 / 2 : ℝ) ^ h) :=
      (ENNReal.ofReal_tsum_of_nonneg hnonneg hactual).symm
    _ ≤ ENNReal.ofReal (2 * C) := ENNReal.ofReal_le_ofReal hsum

theorem aux_mainTwisted_high_dyadic_product (q : ℕ) :
    ((2 : ℝ) ^ q) * (2 : ℝ) ^ (-2 * ((q + 1 : ℕ) : ℤ)) =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ q := by
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hpow : ((q : ℤ) + -2 * ((q + 1 : ℕ) : ℤ)) = -2 + -(q : ℤ) := by
    push_cast
    ring
  rw [hpow, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [zpow_neg, zpow_neg, zpow_natCast, ← inv_pow]
  norm_num

theorem aux_mainTwisted_high_dyadic_ENNReal_product (C : ℝ) (q : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ q) *
      ENNReal.ofReal (C * (2 : ℝ) ^ (-2 * ((q + 1 : ℕ) : ℤ))) =
      ENNReal.ofReal ((C / 4) * (1 / 2 : ℝ) ^ q) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    (2 : ℝ) ^ q * (C * (2 : ℝ) ^ (-2 * ((q + 1 : ℕ) : ℤ))) =
        C * ((2 : ℝ) ^ q * (2 : ℝ) ^ (-2 * ((q + 1 : ℕ) : ℤ))) := by ring
    _ = C * ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ q) := by
      rw [aux_mainTwisted_high_dyadic_product]
    _ = (C / 4) * (1 / 2 : ℝ) ^ q := by ring

theorem aux_mainTwisted_inv_dyadic_ENNReal (q : ℕ) :
    (ENNReal.ofReal ((2 : ℝ) ^ q))⁻¹ = ENNReal.ofReal ((1 / 2 : ℝ) ^ q) := by
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  rw [← inv_pow]
  norm_num

theorem aux_mainTwisted_high_phiZero_energy {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (J : ℕ) (hJ : 0 < J) (t : aux_scaleChain J)
    (hC : 0 ≤ C_mainBumpTwo n) :
    ∑ j : Fin J, (∑' q : ℕ, eLpNorm
      (fun x ↦ twistedAverageAtScale (t.1 j.succ)
          (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))
          (fun i y ↦ f.1 i y) x -
        twistedAverageAtScale (t.1 j.castSucc)
          (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))
          (fun i y ↦ f.1 i y) x) 2 volume) ^ 2 ≤
      ENNReal.ofReal (C_mainBumpTwo n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let a : ℕ → Fin J → ℝ≥0∞ := fun q j ↦ eLpNorm
    (fun x ↦ twistedAverageAtScale (t.1 j.succ)
        (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))
        (fun i y ↦ f.1 i y) x -
      twistedAverageAtScale (t.1 j.castSucc)
        (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))
        (fun i y ↦ f.1 i y) x) 2 volume
  let v : ℕ → ℝ≥0∞ := fun q ↦ ENNReal.ofReal ((2 : ℝ) ^ q)
  let B : ℕ → ℝ≥0∞ := fun q ↦ ENNReal.ofReal
    (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * ((q + 1 : ℕ) : ℤ)))
  let P : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  have hv0 (q : ℕ) : v q ≠ 0 := by
    dsimp [v]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvt (q : ℕ) : v q ≠ ∞ := by
    dsimp [v]
    exact ENNReal.ofReal_ne_top
  have henergy (q : ℕ) : ∑ j, (a q j) ^ 2 ≤ B q * P := by
    have h := mainBumpTwo hn b f ((q + 1 : ℕ) : ℤ) (by omega) J hJ t
    simpa only [a, B, P, aux_jumpEnergy, twistedJumpEnergy] using h
  have hU : (∑' q, (v q)⁻¹) ≤ (2 : ℝ≥0∞) := by
    calc
      (∑' q, (v q)⁻¹) = ∑' q, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) := by
        apply tsum_congr
        intro q
        exact aux_mainTwisted_inv_dyadic_ENNReal q
      _ ≤ ENNReal.ofReal (2 * 1) := by
        simpa using aux_mainTwisted_halfHeightTsum 1 (by norm_num)
      _ = 2 := by norm_num
  have hV : (∑' q, v q * B q) ≤ ENNReal.ofReal (C_mainBumpTwo n / 2) := by
    calc
      (∑' q, v q * B q) =
          ∑' q, ENNReal.ofReal ((C_mainBumpTwo n / 4) * (1 / 2 : ℝ) ^ q) := by
        apply tsum_congr
        intro q
        exact aux_mainTwisted_high_dyadic_ENNReal_product _ q
      _ ≤ ENNReal.ofReal (2 * (C_mainBumpTwo n / 4)) :=
        aux_mainTwisted_halfHeightTsum _ (div_nonneg hC (by norm_num))
      _ = ENNReal.ofReal (C_mainBumpTwo n / 2) := by ring_nf
  have hmain := aux_mainTwisted_weighted_tsum_energy_bound a v B P (2 : ℝ≥0∞)
    (ENNReal.ofReal (C_mainBumpTwo n / 2)) hv0 hvt henergy hU hV
  change ∑ j : Fin J, (∑' q : ℕ, a q j) ^ 2 ≤
    ENNReal.ofReal (C_mainBumpTwo n) * P
  calc
    ∑ j : Fin J, (∑' q : ℕ, a q j) ^ 2 ≤
        2 * (ENNReal.ofReal (C_mainBumpTwo n / 2) * P) := hmain
    _ = ENNReal.ofReal (C_mainBumpTwo n) * P := by
      have hcoef : (2 : ℝ≥0∞) * ENNReal.ofReal (C_mainBumpTwo n / 2) =
          ENNReal.ofReal (C_mainBumpTwo n) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [← mul_assoc, hcoef]

theorem aux_mainTwisted_high_phiOne_energy {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (J : ℕ) (hJ : 0 < J) (t : aux_scaleChain J)
    (hC : 0 ≤ C_leftBump n) :
    ∑ j : Fin J, (∑' q : ℕ, eLpNorm
      (fun x ↦ twistedAverageAtScale (t.1 j.succ)
          (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))
          (fun i y ↦ f.1 i y) x -
        twistedAverageAtScale (t.1 j.castSucc)
          (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))
          (fun i y ↦ f.1 i y) x) 2 volume) ^ 2 ≤
      ENNReal.ofReal (C_leftBump n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let a : ℕ → Fin J → ℝ≥0∞ := fun q j ↦ eLpNorm
    (fun x ↦ twistedAverageAtScale (t.1 j.succ)
        (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))
        (fun i y ↦ f.1 i y) x -
      twistedAverageAtScale (t.1 j.castSucc)
        (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))
        (fun i y ↦ f.1 i y) x) 2 volume
  let v : ℕ → ℝ≥0∞ := fun q ↦ ENNReal.ofReal ((2 : ℝ) ^ q)
  let B : ℕ → ℝ≥0∞ := fun q ↦ ENNReal.ofReal
    (C_leftBump n * (2 : ℝ) ^ (-2 * ((q + 1 : ℕ) : ℤ)))
  let P : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  have hv0 (q : ℕ) : v q ≠ 0 := by
    dsimp [v]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hvt (q : ℕ) : v q ≠ ∞ := by
    dsimp [v]
    exact ENNReal.ofReal_ne_top
  have henergy (q : ℕ) : ∑ j, (a q j) ^ 2 ≤ B q * P := by
    have h := leftBump hn b f (-((q + 1 : ℕ) : ℤ)) (by omega) J hJ t
    have hpow : (2 * -((q + 1 : ℕ) : ℤ)) = -2 * ((q + 1 : ℕ) : ℤ) := by ring
    rw [hpow] at h
    simpa only [a, B, P, aux_jumpEnergy, twistedJumpEnergy] using h
  have hU : (∑' q, (v q)⁻¹) ≤ (2 : ℝ≥0∞) := by
    calc
      (∑' q, (v q)⁻¹) = ∑' q, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) := by
        apply tsum_congr
        intro q
        exact aux_mainTwisted_inv_dyadic_ENNReal q
      _ ≤ ENNReal.ofReal (2 * 1) := by
        simpa using aux_mainTwisted_halfHeightTsum 1 (by norm_num)
      _ = 2 := by norm_num
  have hV : (∑' q, v q * B q) ≤ ENNReal.ofReal (C_leftBump n / 2) := by
    calc
      (∑' q, v q * B q) =
          ∑' q, ENNReal.ofReal ((C_leftBump n / 4) * (1 / 2 : ℝ) ^ q) := by
        apply tsum_congr
        intro q
        exact aux_mainTwisted_high_dyadic_ENNReal_product _ q
      _ ≤ ENNReal.ofReal (2 * (C_leftBump n / 4)) :=
        aux_mainTwisted_halfHeightTsum _ (div_nonneg hC (by norm_num))
      _ = ENNReal.ofReal (C_leftBump n / 2) := by ring_nf
  have hmain := aux_mainTwisted_weighted_tsum_energy_bound a v B P (2 : ℝ≥0∞)
    (ENNReal.ofReal (C_leftBump n / 2)) hv0 hvt henergy hU hV
  change ∑ j : Fin J, (∑' q : ℕ, a q j) ^ 2 ≤
    ENNReal.ofReal (C_leftBump n) * P
  calc
    ∑ j : Fin J, (∑' q : ℕ, a q j) ^ 2 ≤
        2 * (ENNReal.ofReal (C_leftBump n / 2) * P) := hmain
    _ = ENNReal.ofReal (C_leftBump n) * P := by
      have hcoef : (2 : ℝ≥0∞) * ENNReal.ofReal (C_leftBump n / 2) =
          ENNReal.ofReal (C_leftBump n) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      rw [← mul_assoc, hcoef]

theorem aux_mainTwisted_rpow_inv (q : ℕ) :
    (ENNReal.ofReal (Real.rpow 2 ((q : ℝ) / 4)))⁻¹ =
      ENNReal.ofReal (Real.rpow 2 (-((q : ℝ) / 4))) := by
  rw [show Real.rpow 2 (-((q : ℝ) / 4)) =
      (Real.rpow 2 ((q : ℝ) / 4))⁻¹ by
        exact Real.rpow_neg (by norm_num) _]
  exact (ENNReal.ofReal_inv_of_pos
    (Real.rpow_pos_of_pos (by norm_num) ((q : ℝ) / 4))).symm

theorem aux_mainTwisted_rpow_weighted_product (C : ℝ) (q : ℕ) :
    ENNReal.ofReal (Real.rpow 2 ((q : ℝ) / 4)) *
      ENNReal.ofReal (C * Real.rpow 2 (-(((q + 1 : ℕ) : ℝ) / 2))) =
      ENNReal.ofReal (C * Real.rpow 2 (-(1 / 2 : ℝ) - ((q : ℝ) / 4))) := by
  rw [← ENNReal.ofReal_mul
    (p := Real.rpow 2 ((q : ℝ) / 4))
    (q := C * Real.rpow 2 (-(((q + 1 : ℕ) : ℝ) / 2)))
    (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  calc
    Real.rpow 2 ((q : ℝ) / 4) *
        (C * Real.rpow 2 (-(((q + 1 : ℕ) : ℝ) / 2))) =
        C * (Real.rpow 2 ((q : ℝ) / 4) *
          Real.rpow 2 (-(((q + 1 : ℕ) : ℝ) / 2))) := by ring
    _ = C * Real.rpow 2 ((q : ℝ) / 4 - ((q + 1 : ℕ) : ℝ) / 2) := by
      change C * ((2 : ℝ) ^ ((q : ℝ) / 4) *
        (2 : ℝ) ^ (-(((q + 1 : ℕ) : ℝ) / 2))) =
          C * (2 : ℝ) ^ ((q : ℝ) / 4 - ((q + 1 : ℕ) : ℝ) / 2)
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
    _ = C * Real.rpow 2 (-(1 / 2 : ℝ) - ((q : ℝ) / 4)) := by
      congr 2
      push_cast
      ring

theorem aux_mainTwisted_rpow_weighted_product_le (C : ℝ) (hC : 0 ≤ C) (q : ℕ) :
    ENNReal.ofReal (Real.rpow 2 ((q : ℝ) / 4)) *
      ENNReal.ofReal (C * Real.rpow 2 (-(((q + 1 : ℕ) : ℝ) / 2))) ≤
      ENNReal.ofReal (C * Real.rpow 2 (-((q : ℝ) / 4))) := by
  rw [aux_mainTwisted_rpow_weighted_product]
  apply ENNReal.ofReal_le_ofReal
  have hfactor : Real.rpow 2 (-(1 / 2 : ℝ) - ((q : ℝ) / 4)) ≤
      Real.rpow 2 (-((q : ℝ) / 4)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  exact mul_le_mul_of_nonneg_left hfactor hC

theorem aux_mainTwisted_high_phiTwo_energy {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (J : ℕ) (hJ : 0 < J) (t : aux_scaleChain J)
    (hC : 0 ≤ C_leftBumpOne n) :
    ∑ j : Fin J, (∑' q : ℕ, eLpNorm
      (fun x ↦ twistedAverageAtScale (t.1 j.succ)
          (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))
          (fun i y ↦ f.1 i y) x -
        twistedAverageAtScale (t.1 j.castSucc)
          (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))
          (fun i y ↦ f.1 i y) x) 2 volume) ^ 2 ≤
      ENNReal.ofReal (64 * C_leftBumpOne n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let a : ℕ → Fin J → ℝ≥0∞ := fun q j ↦ eLpNorm
    (fun x ↦ twistedAverageAtScale (t.1 j.succ)
        (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))
        (fun i y ↦ f.1 i y) x -
      twistedAverageAtScale (t.1 j.castSucc)
        (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))
        (fun i y ↦ f.1 i y) x) 2 volume
  let v : ℕ → ℝ≥0∞ := fun q ↦ ENNReal.ofReal (Real.rpow 2 ((q : ℝ) / 4))
  let B : ℕ → ℝ≥0∞ := fun q ↦ ENNReal.ofReal
    (C_leftBumpOne n * Real.rpow 2 (-(((q + 1 : ℕ) : ℝ) / 2)))
  let P : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  have hv0 (q : ℕ) : v q ≠ 0 := by
    dsimp [v]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hvt (q : ℕ) : v q ≠ ∞ := by
    dsimp [v]
    exact ENNReal.ofReal_ne_top
  have henergy (q : ℕ) : ∑ j, (a q j) ^ 2 ≤ B q * P := by
    have h := leftBumpOne hn b f (-((q + 1 : ℕ) : ℤ)) (by omega) J hJ t
    have hscale : ((-((q + 1 : ℕ) : ℤ) : ℝ) / 2) =
        -(((q + 1 : ℕ) : ℝ) / 2) := by
      push_cast
      ring
    simp only [Int.cast_neg] at h
    rw [hscale] at h
    simpa only [a, B, P, aux_jumpEnergy, twistedJumpEnergy] using h
  have hU : (∑' q, (v q)⁻¹) ≤ (8 : ℝ≥0∞) := by
    calc
      (∑' q, (v q)⁻¹) =
          ∑' q : ℕ, ENNReal.ofReal (Real.rpow 2 (-((q : ℝ) / 4))) := by
        apply tsum_congr
        intro q
        exact aux_mainTwisted_rpow_inv q
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ 3 * 1) := by
        simpa using quarterHeightTsum 1 (by norm_num)
      _ = 8 := by norm_num
  have hV : (∑' q, v q * B q) ≤ ENNReal.ofReal (8 * C_leftBumpOne n) := by
    calc
      (∑' q, v q * B q) ≤
          ∑' q : ℕ, ENNReal.ofReal
            (C_leftBumpOne n * Real.rpow 2 (-((q : ℝ) / 4))) := by
          apply ENNReal.tsum_le_tsum
          intro q
          exact aux_mainTwisted_rpow_weighted_product_le _ hC q
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ 3 * C_leftBumpOne n) :=
        quarterHeightTsum _ hC
      _ = ENNReal.ofReal (8 * C_leftBumpOne n) := by norm_num
  have hmain := aux_mainTwisted_weighted_tsum_energy_bound a v B P (8 : ℝ≥0∞)
    (ENNReal.ofReal (8 * C_leftBumpOne n)) hv0 hvt henergy hU hV
  change ∑ j : Fin J, (∑' q : ℕ, a q j) ^ 2 ≤
    ENNReal.ofReal (64 * C_leftBumpOne n) * P
  calc
    ∑ j : Fin J, (∑' q : ℕ, a q j) ^ 2 ≤
        8 * (ENNReal.ofReal (8 * C_leftBumpOne n) * P) := hmain
    _ = ENNReal.ofReal (64 * C_leftBumpOne n) * P := by
      have hcoef : (8 : ℝ≥0∞) * ENNReal.ofReal (8 * C_leftBumpOne n) =
          ENNReal.ofReal (64 * C_leftBumpOne n) := by
        rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
        congr 1
        ring
      rw [← mul_assoc, hcoef]


noncomputable def aux_mainTwisted_low_jumpNorm {n J : ℕ}
    (t : aux_scaleChain J)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ)
    (chi : ℝ → ℝ) (j : Fin J) : ℝ≥0∞ :=
  eLpNorm
    (fun x ↦ twistedAverageAtScale (t.1 j.succ) chi (fun i y ↦ f i y) x -
      twistedAverageAtScale (t.1 j.castSucc) chi (fun i y ↦ f i y) x)
    2 volume

theorem aux_mainTwisted_weighted_finset_energy {ι : Type*} [Fintype ι] {J : ℕ}
    (a : ι → Fin J → ℝ≥0∞) (v B : ι → ℝ≥0∞) (P : ℝ≥0∞)
    (hv0 : ∀ i, v i ≠ 0) (hvt : ∀ i, v i ≠ ∞)
    (henergy : ∀ i, ∑ j, (a i j) ^ 2 ≤ B i * P) :
    ∑ j, (∑ i, a i j) ^ 2 ≤
      (∑ i, (v i)⁻¹) * ((∑ i, v i * B i) * P) := by
  let u : ι → ℝ≥0∞ := fun i ↦ (v i)⁻¹
  let e : ι → Fin J → ℝ≥0∞ := fun i j ↦ v i * (a i j) ^ 2
  have hroot (i : ι) (j : Fin J) :
      a i j ≤ (u i) ^ (1 / (2 : ℝ)) * (e i j) ^ (1 / (2 : ℝ)) := by
    calc
      a i j = ((a i j) ^ 2) ^ (1 / (2 : ℝ)) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
      _ ≤ (u i * e i j) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (by
          dsimp [u, e]
          rw [← mul_assoc, ENNReal.inv_mul_cancel (hv0 i) (hvt i), one_mul]) (by positivity)
      _ = (u i) ^ (1 / (2 : ℝ)) * (e i j) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
  have hsquare (j : Fin J) :
      (∑ i, a i j) ^ 2 ≤ (∑ i, u i) * ∑ i, e i j := by
    have hinter :
        ∑ i, a i j ≤
          (∑ i, ((u i) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∑ i, ((e i j) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      calc
        ∑ i, a i j ≤ ∑ i, (u i) ^ (1 / (2 : ℝ)) *
            (e i j) ^ (1 / (2 : ℝ)) :=
          Finset.sum_le_sum fun i _ => hroot i j
        _ ≤ (∑ i, ((u i) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∑ i, ((e i j) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
          ENNReal.inner_le_Lp_mul_Lq Finset.univ
            (fun i => (u i) ^ (1 / (2 : ℝ)))
            (fun i => (e i j) ^ (1 / (2 : ℝ))) Real.HolderConjugate.two_two
    calc
      (∑ i, a i j) ^ 2 ≤
          ((∑ i, ((u i) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∑ i, ((e i j) ^ (1 / (2 : ℝ))) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left' hinter 2
      _ = (∑ i, u i) * ∑ i, e i j := by
        simp only [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  have hinner (i : ι) : ∑ j, e i j = v i * ∑ j, (a i j) ^ 2 := by
    dsimp [e]
    rw [← Finset.mul_sum]
  calc
    ∑ j, (∑ i, a i j) ^ 2 ≤ ∑ j, (∑ i, u i) * ∑ i, e i j :=
      Finset.sum_le_sum fun j _ => hsquare j
    _ = (∑ i, u i) * ∑ j, ∑ i, e i j := by rw [Finset.mul_sum]
    _ = (∑ i, u i) * ∑ i, ∑ j, e i j := by
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ i, (v i)⁻¹) * ∑ i, v i * ∑ j, (a i j) ^ 2 := by
      dsimp [u]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact hinner i
    _ ≤ (∑ i, (v i)⁻¹) * (∑ i, (v i * B i) * P) := by
      have hterm (i : ι) : v i * ∑ j, (a i j) ^ 2 ≤ (v i * B i) * P := by
        calc
          v i * ∑ j, (a i j) ^ 2 ≤ v i * (B i * P) :=
            mul_le_mul_right (henergy i) (v i)
          _ = (v i * B i) * P := by ring
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro i _
      exact hterm i
    _ = (∑ i, (v i)⁻¹) * ((∑ i, v i * B i) * P) := by
      congr 1
      simpa using
        (Finset.sum_mul Finset.univ (fun i : ι => v i * B i) P).symm

theorem aux_mainTwisted_low_high_phiZero_energy {n : ℕ} (hn : 2 ≤ n)
    (b : windowBasedBumpFunctions) (f : ReductionNormalizedTuple n)
    (J : ℕ) (hJ : 0 < J) (t : aux_scaleChain J)
    (hC : 0 ≤ C_mainBumpTwo n)
    (hhigh : ∑ j : Fin J, (∑' q : ℕ,
      aux_mainTwisted_low_jumpNorm t f.1
        (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ)) j) ^ 2 ≤
        ENNReal.ofReal (C_mainBumpTwo n) *
          ENNReal.ofReal ((J : ℝ) ^ variationExponent n)) :
    ∑ j : Fin J,
        (aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b (-2)) j +
          aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b (-1)) j +
          aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b 0) j +
          ∑' q : ℕ,
            aux_mainTwisted_low_jumpNorm t f.1
              (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ)) j) ^ 2 ≤
      ENNReal.ofReal (64 * C_mainBumpTwo n) *
        ENNReal.ofReal ((J : ℝ) ^ variationExponent n) := by
  let P : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  let a : Fin 4 → Fin J → ℝ≥0∞ := ![
    aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b (-2)) ,
    aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b (-1)) ,
    aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b 0) ,
    fun j ↦ ∑' q : ℕ,
      aux_mainTwisted_low_jumpNorm t f.1
        (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ)) j]
  let v : Fin 4 → ℝ≥0∞ := ![(1 / 4 : ℝ≥0∞), (1 / 2 : ℝ≥0∞), 1, 1]
  let B : Fin 4 → ℝ≥0∞ := ![
    16 * ENNReal.ofReal (C_mainBumpTwo n),
    4 * ENNReal.ofReal (C_mainBumpTwo n),
    ENNReal.ofReal (C_mainBumpTwo n),
    ENNReal.ofReal (C_mainBumpTwo n)]
  have hv0 (i : Fin 4) : v i ≠ 0 := by
    fin_cases i <;> simp [v]
  have hvt (i : Fin 4) : v i ≠ ∞ := by
    fin_cases i <;> simp [v]
  have henergy (i : Fin 4) : ∑ j, (a i j) ^ 2 ≤ B i * P := by
    fin_cases i
    · have h := mainBumpTwo hn b f (-2) (by omega) J hJ t
      have h' : ∑ j, (a 0 j) ^ 2 ≤
          ENNReal.ofReal (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * (-2 : ℤ))) * P := by
        simpa [a, P, aux_mainTwisted_low_jumpNorm, aux_jumpEnergy, twistedJumpEnergy] using h
      calc
        ∑ j, (a 0 j) ^ 2 ≤
            ENNReal.ofReal (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * (-2 : ℤ))) * P := h'
        _ = B 0 * P := by
          rw [ENNReal.ofReal_mul hC]
          norm_num [B]
          ac_rfl
    · have h := mainBumpTwo hn b f (-1) (by omega) J hJ t
      have h' : ∑ j, (a 1 j) ^ 2 ≤
          ENNReal.ofReal (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * (-1 : ℤ))) * P := by
        simpa [a, P, aux_mainTwisted_low_jumpNorm, aux_jumpEnergy, twistedJumpEnergy] using h
      calc
        ∑ j, (a 1 j) ^ 2 ≤
            ENNReal.ofReal (C_mainBumpTwo n * (2 : ℝ) ^ (-2 * (-1 : ℤ))) * P := h'
        _ = B 1 * P := by
          rw [ENNReal.ofReal_mul hC]
          norm_num [B]
          ac_rfl
    · have h := mainBumpTwo hn b f 0 (by omega) J hJ t
      simpa [a, B, P, aux_mainTwisted_low_jumpNorm, aux_jumpEnergy, twistedJumpEnergy] using h
    · simpa [a, B, P] using hhigh
  have hmain := aux_mainTwisted_weighted_finset_energy a v B P hv0 hvt henergy
  calc
    ∑ j : Fin J,
        (aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b (-2)) j +
          aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b (-1)) j +
          aux_mainTwisted_low_jumpNorm t f.1 (windowBasedBumpFunctions.phiZero b 0) j +
          ∑' q : ℕ,
            aux_mainTwisted_low_jumpNorm t f.1
              (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ)) j) ^ 2 =
        ∑ j : Fin J, (∑ i : Fin 4, a i j) ^ 2 := by
          congr 1
          funext j
          simp [a, Fin.sum_univ_succ]
          ac_rfl
    _ ≤
        (∑ i : Fin 4, (v i)⁻¹) * ((∑ i : Fin 4, v i * B i) * P) := hmain
    _ = ENNReal.ofReal (64 * C_mainBumpTwo n) * P := by
      have hinv : (∑ i : Fin 4, (v i)⁻¹) = (8 : ℝ≥0∞) := by
        norm_num [v, Fin.sum_univ_succ]
      have hB : (∑ i : Fin 4, v i * B i) =
          8 * ENNReal.ofReal (C_mainBumpTwo n) := by
        have h4 : (4 : ℝ≥0∞)⁻¹ * 4 = 1 :=
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        have h2 : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        have hcalc :
          (4 : ℝ≥0∞)⁻¹ * (16 * ENNReal.ofReal (C_mainBumpTwo n)) +
              (2 : ℝ≥0∞)⁻¹ * (4 * ENNReal.ofReal (C_mainBumpTwo n)) +
                (ENNReal.ofReal (C_mainBumpTwo n) + ENNReal.ofReal (C_mainBumpTwo n)) =
              8 * ENNReal.ofReal (C_mainBumpTwo n) := by
          calc
            (4 : ℝ≥0∞)⁻¹ * (16 * ENNReal.ofReal (C_mainBumpTwo n)) +
                (2 : ℝ≥0∞)⁻¹ * (4 * ENNReal.ofReal (C_mainBumpTwo n)) +
                  (ENNReal.ofReal (C_mainBumpTwo n) + ENNReal.ofReal (C_mainBumpTwo n)) =
              ((4 : ℝ≥0∞)⁻¹ * 4) * (4 * ENNReal.ofReal (C_mainBumpTwo n)) +
                ((2 : ℝ≥0∞)⁻¹ * 2) * (2 * ENNReal.ofReal (C_mainBumpTwo n)) +
                  (ENNReal.ofReal (C_mainBumpTwo n) + ENNReal.ofReal (C_mainBumpTwo n)) := by ring
            _ = 8 * ENNReal.ofReal (C_mainBumpTwo n) := by rw [h4, h2]; ring
        calc
          (∑ i : Fin 4, v i * B i) =
              (4 : ℝ≥0∞)⁻¹ * (16 * ENNReal.ofReal (C_mainBumpTwo n)) +
                (2 : ℝ≥0∞)⁻¹ * (4 * ENNReal.ofReal (C_mainBumpTwo n)) +
                  (ENNReal.ofReal (C_mainBumpTwo n) + ENNReal.ofReal (C_mainBumpTwo n)) := by
                    simp [v, B, Fin.sum_univ_succ]
                    ac_rfl
          _ = 8 * ENNReal.ofReal (C_mainBumpTwo n) := hcalc
      rw [hinv, hB, ← mul_assoc]
      rw [← mul_assoc]
      norm_num


/--
The fixed-constant reduction-side form of Theorem
`Auto.aux_main_twisted_theorem`.
It is stated over the shared `Auto` twisted-average definitions to
keep imports acyclic.
-/
theorem mainTwistedTheoremReductionBound {n : ℕ} (hn : 2 ≤ n) :
    ∀ (J : ℕ), 0 < J → ∀ (t : Fin (J + 1) → ℝ),
      StrictMono t → (∀ j, 0 < t j) →
      ∀ f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ,
        (∀ i, eLpNorm (f i) ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2)) volume = 1) →
        ∑ j : Fin J, eLpNorm
            (fun x ↦ twistedAverageAtScale (t j.succ) unitIntervalIndicator
                (fun i y ↦ f i y) x -
              twistedAverageAtScale (t j.castSucc) unitIntervalIndicator
                (fun i y ↦ f i y) x)
            2 volume ^ 2 ≤
          ENNReal.ofReal ((2 : ℝ) ^ 666) * ENNReal.ofReal
            ((J : ℝ) ^ (1 - (2 : ℝ) ^ (-(n : ℝ) + 2))) := by
  classical
  intro J hJ t ht htpos f hf
  obtain ⟨phi0, phi1, hpair⟩ := existsUniversalPair
  let b : windowBasedBumpFunctions := ⟨phi0, phi1, hpair⟩
  let F : ReductionNormalizedTuple n := ⟨f, hf⟩
  let T : aux_scaleChain J := ⟨t, ht, htpos⟩
  let R : ℝ≥0∞ := ENNReal.ofReal ((J : ℝ) ^ variationExponent n)
  have hI : MemLp (aux_indicator (Set.Icc (0 : ℝ) 1)) 2 volume :=
    memLp_indicator_const 2 measurableSet_Icc (1 : ℝ)
      (Or.inr measure_Icc_lt_top.ne)
  have hphi0 : MemLp (fun x ↦ b.phi0 x) 2 volume := b.phi0.memLp 2 volume
  have hzero (k : ℤ) : MemLp (windowBasedBumpFunctions.phiZero b k) 2 volume :=
    aux_mainTwisted_phiZero_memLp_of_phiThree_eq b k
      (aux_mainBumpTwo_phiThree_eq_rescaled b k)
  have hone (k : ℤ) : MemLp (windowBasedBumpFunctions.phiOne b k) 2 volume :=
    aux_mainTwisted_phiOne_memLp_of_thetaTilde_eq b k
      (aux_leftBump_phiOne_eq_scaled_thetaTilde b k)
  have htwo (k : ℤ) : MemLp (windowBasedBumpFunctions.phiTwo b k) 2 volume :=
    aux_mainTwisted_phiTwo_memLp_of_phiFour_eq b k
      (aux_leftBumpOne_phiTwo_eq_neg_oneRescaled_phiFour b k)
  have hAuxOne : 0 ≤ C_mainAuxOne n := aux_C_mainAuxOne_nonneg n
  have hAuxTwo : 0 ≤ C_mainAuxTwo n := by
    unfold C_mainAuxTwo
    exact mul_nonneg (by norm_num) hAuxOne
  have hC0 : 0 ≤ C_mainBumpOne n := by
    unfold C_mainBumpOne
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hAuxOne)
      (mul_nonneg (by norm_num) (aux_mainBumpOne_C_long_pos n).le)
  have hC1 : 0 ≤ C_mainBumpTwo n := by
    unfold C_mainBumpTwo
    exact mul_nonneg hAuxTwo (sq_nonneg _)
  have hC2 : 0 ≤ C_leftBump n := by
    unfold C_leftBump
    exact mul_nonneg hAuxTwo (sq_nonneg _)
  have hC3 : 0 ≤ C_leftBumpOne n := by
    unfold C_leftBumpOne
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
      (mul_nonneg (by norm_num) (aux_leftBumpOne_long_nonneg n))
  have h0 : ∑ j : Fin J, (aux_mainTwisted_jumpNorm F.1 T j (fun x ↦ b.phi0 x)) ^ 2 ≤
      ENNReal.ofReal (C_mainBumpOne n) * R := by
    simpa only [R] using aux_mainTwisted_mainBumpOne_energy hn b F T hJ
  have hhighZero := aux_mainTwisted_high_phiZero_energy hn b F J hJ T hC1
  have hlowZero := aux_mainTwisted_low_high_phiZero_energy hn b F J hJ T hC1 hhighZero
  have h1 : ∑ j : Fin J,
      (aux_mainTwisted_jumpNorm F.1 T j (windowBasedBumpFunctions.phiZero b (-2)) +
        (aux_mainTwisted_jumpNorm F.1 T j (windowBasedBumpFunctions.phiZero b (-1)) +
          aux_mainTwisted_jumpNorm F.1 T j (windowBasedBumpFunctions.phiZero b 0)) +
        ∑' q : ℕ, aux_mainTwisted_jumpNorm F.1 T j
          (windowBasedBumpFunctions.phiZero b ((q + 1 : ℕ) : ℤ))) ^ 2 ≤
      ENNReal.ofReal (64 * C_mainBumpTwo n) * R := by
    simpa only [aux_mainTwisted_jumpNorm, aux_mainTwisted_low_jumpNorm, R, add_assoc] using hlowZero
  have hhighOne := aux_mainTwisted_high_phiOne_energy hn b F J hJ T hC2
  have h2 : ∑ j : Fin J,
      (∑' q : ℕ, aux_mainTwisted_jumpNorm F.1 T j
        (windowBasedBumpFunctions.phiOne b (-((q + 1 : ℕ) : ℤ)))) ^ 2 ≤
      ENNReal.ofReal (C_leftBump n) * R := by
    simpa only [aux_mainTwisted_jumpNorm, R] using hhighOne
  have hhighTwo := aux_mainTwisted_high_phiTwo_energy hn b F J hJ T hC3
  have h3 : ∑ j : Fin J,
      (∑' q : ℕ, aux_mainTwisted_jumpNorm F.1 T j
        (windowBasedBumpFunctions.phiTwo b (-((q + 1 : ℕ) : ℤ)))) ^ 2 ≤
      ENNReal.ofReal (64 * C_leftBumpOne n) * R := by
    simpa only [aux_mainTwisted_jumpNorm, R] using hhighTwo
  have hmain := aux_mainTwisted_terminal_aggregation hn b F.1 T R hI hphi0 hzero hone htwo
    hC0 hC1 hC2 hC3 h0 h1 h2 h3
  have hconst : C_mainTwistedTheorem n < (2 : ℝ) ^ 666 :=
    constantMainTwistedTheoremReduction hn
  calc
    ∑ j : Fin J, eLpNorm
        (fun x ↦ twistedAverageAtScale (t j.succ) unitIntervalIndicator
            (fun i y ↦ f i y) x -
          twistedAverageAtScale (t j.castSucc) unitIntervalIndicator
            (fun i y ↦ f i y) x)
        2 volume ^ 2 =
        ∑ j : Fin J,
          (aux_mainTwisted_jumpNorm F.1 T j (aux_indicator (Set.Icc (0 : ℝ) 1))) ^ 2 := by
            rfl
    _ ≤ ENNReal.ofReal (C_mainTwistedTheorem n) * R := hmain
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ 666) * R := by
      simpa [mul_comm] using
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hconst.le) R
    _ = ENNReal.ofReal ((2 : ℝ) ^ 666) * ENNReal.ofReal
        ((J : ℝ) ^ (1 - (2 : ℝ) ^ (-(n : ℝ) + 2))) := by
          rfl

/--
The existentially packaged compatibility form of
`mainTwistedTheoremReductionBound`.
-/
theorem mainTwistedTheoremReduction {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ), 0 < J → ∀ (t : Fin (J + 1) → ℝ),
      StrictMono t → (∀ j, 0 < t j) →
      ∀ f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ,
        (∀ i, eLpNorm (f i) ((2 : ℝ≥0∞) ^ (i.val + min (n - i.val) 2)) volume = 1) →
        ∑ j : Fin J, eLpNorm
            (fun x ↦ twistedAverageAtScale (t j.succ) unitIntervalIndicator
                (fun i y ↦ f i y) x -
              twistedAverageAtScale (t j.castSucc) unitIntervalIndicator
                (fun i y ↦ f i y) x)
            2 volume ^ 2 ≤
          ENNReal.ofReal C * ENNReal.ofReal
            ((J : ℝ) ^ (1 - (2 : ℝ) ^ (-(n : ℝ) + 2))) := by
  refine ⟨(2 : ℝ) ^ 666, by positivity, mainTwistedTheoremReductionBound hn⟩

end

end Auto
