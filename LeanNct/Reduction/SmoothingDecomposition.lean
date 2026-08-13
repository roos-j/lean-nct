import LeanNct.Reduction.WindowsAndPairs
import LeanNct.Reduction.BumpFunctions
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# A smoothing decomposition

Formalization of the ``A smoothing decomposition'' subsection of the reduction
argument.
-/

namespace Codex.Reduction.SmoothingDecomposition

open MeasureTheory Filter Set
open scoped BigOperators FourierTransform Real ENNReal DomAddAct Convolution

open Codex.Preliminaries.Notation
open Codex.Reduction.WindowsAndPairs
open Codex.Reduction.BumpFunctions

noncomputable section

/-- The raw one-dimensional, $L^1$-normalized rescaling used throughout
Definition \ref{defn:window based bump functions}. -/
noncomputable def aux_realRescaled (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ t⁻¹ * f (t⁻¹ * x)

/-- The raw scalar convolution used to state the bump-function definitions. -/
noncomputable def aux_realConvolution (f g : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ ∫ y : ℝ, f y * g (x - y)

/-- The real-valued characteristic function of a set. -/
noncomputable def aux_indicator (s : Set ℝ) : ℝ → ℝ :=
  s.indicator (fun _ : ℝ ↦ 1)

/-- The compact frequency annulus occurring in this subsection. -/
def aux_frequencyAnnulus : Set ℝ :=
  Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1

/-- The one-dimensional annulus convention shared with the integral-kernel estimates. -/
abbrev aux_annulusOne (r R : ℝ) : Set ℝ :=
  Codex.Reduction.BumpFunctions.aux_annulusOne r R

/-- The raw operator $T f=(x f(x))'$ needed in the Fourier estimates below. -/
noncomputable def aux_T (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ deriv (fun y ↦ y * f y) x

/-- Uniform convergence of a sequence of real functions, expressed directly through
the epsilon--$N$ condition. -/
def aux_uniformlyConverges (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |f n x - g x| < ε

/-- Convergence in the $L^2$ sense used for the two decomposition identities. -/
def aux_convergesInL2 (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) : Prop :=
  Tendsto (fun N ↦ eLpNorm (fun x ↦ f N x - g x) 2 volume) atTop (nhds 0)

/-- A finite integer-indexed sum of scalar functions. -/
noncomputable def aux_integerIntervalSum (f : ℤ → ℝ → ℝ) (a b : ℤ) : ℝ → ℝ :=
  fun x ↦ ∑ j ∈ Finset.Icc a b, f j x

/--
\begin{definition}[Window-based bump functions]\label{defn:window based bump functions}
Let $(\phi_0,\phi_1)$ be a universal pair.  The fields of this structure fix that
pair; the associated functions below are the functions in
\eqref{eqn:thetadef}--\eqref{eqn:varphi4kdef}.
\end{definition}
-/
structure windowBasedBumpFunctions where
  phi0 : SchwartzMap ℝ ℝ
  phi1 : SchwartzMap ℝ ℝ
  universalPair : uniPair phi0 phi1

namespace windowBasedBumpFunctions

/-- The function $\theta=\phi_0-(\phi_0)_{(2)}$ from
\eqref{eqn:thetadef}. -/
noncomputable def theta (b : windowBasedBumpFunctions) : ℝ → ℝ :=
  fun x ↦ b.phi0 x - aux_realRescaled 2 (fun y ↦ b.phi0 y) x

/-- The primitive $\widetilde\theta=\mathbf 1_{[0,\infty)}*\theta$ fixed in
Definition \ref{defn:window based bump functions}. -/
noncomputable def thetaTilde (b : windowBasedBumpFunctions) : ℝ → ℝ :=
  aux_realConvolution (aux_indicator (Set.Ici 0)) (theta b)

/-- The function $\varphi_{0,k}$ from \eqref{eqn:varphi0kdef}. -/
noncomputable def phiZero (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  aux_realConvolution
    (fun x ↦
      aux_realConvolution (aux_indicator (Set.Ico 0 1)) (fun y ↦ b.phi0 y) x - b.phi0 x)
    (aux_realRescaled ((2 : ℝ) ^ k) (theta b))

/-- The function $\varphi_{1,k}$ from \eqref{eqn:varphi1kdef}. -/
noncomputable def phiOne (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  aux_realConvolution (aux_indicator (Set.Ici 0))
    (aux_realRescaled ((2 : ℝ) ^ k) (theta b))

/-- The function $\varphi_{2,k}$ from \eqref{eqn:varphi2kdef}. -/
noncomputable def phiTwo (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  fun x ↦ -aux_realConvolution (aux_indicator (Set.Ici 1))
    (aux_realRescaled ((2 : ℝ) ^ k) (theta b)) x

/-- The function $\varphi_{3,k}$ from \eqref{eqn:varphi3def}. -/
noncomputable def phiThree (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  fun x ↦ ((2 : ℝ) ^ k) *
    aux_realRescaled ((2 : ℝ) ^ (-k)) (phiZero b k) x

/-- The function $\varphi_{4,k}$ from \eqref{eqn:varphi4kdef}. -/
noncomputable def phiFour (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  fun u ↦ ((2 : ℝ) ^ k) * thetaTilde b (u - (2 : ℝ) ^ (-k))

/-- The simultaneous partial sum in the smoothing decomposition. -/
noncomputable def smoothingPartialSum (b : windowBasedBumpFunctions) (N : ℕ) : ℝ → ℝ :=
  fun x ↦
    b.phi0 x +
      aux_integerIntervalSum (phiZero b) (-2) (N : ℤ) x +
      aux_integerIntervalSum (fun k ↦ fun y ↦ phiOne b k y + phiTwo b k y)
        (-(N : ℤ)) (-1) x

end windowBasedBumpFunctions

/-- The constant in Lemma \ref{lem:theta_decay}. -/
def C_thetaDecay (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * N + 2) * C_uniPair

/-- The four explicit constants in Lemma \ref{lem:abs_deriv_ft_phi3_le}. -/
def C_absDerivFourierPhiThreeLe : ℕ → ℝ
  | 0 => 4
  | 1 => 28 * C_uniPair + 4
  | 2 => 96 * C_uniPair ^ 2 + 140 * C_uniPair + 86
  | 3 => 69 * (2 : ℝ) ^ 4 * C_uniPair ^ 2 + 47 * 2 * 5 ^ 2 * C_uniPair + 2 ^ 11
  | _ + 4 => 0

/-- The constants in Lemma \ref{lem:abs_deriv_ft_Tphi3_le}. -/
def C_absDerivFourierTPhiThreeLe (m : ℕ) : ℝ :=
  m * C_absDerivFourierPhiThreeLe m + C_absDerivFourierPhiThreeLe (m + 1)

/-- The constant in Lemma \ref{lem:theta_prim}. -/
def C_thetaPrimitive (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (5 * N + 6) * C_uniPair

/-- The generic two-scale difference used to prove the telescoping assertion in `bumpBasic`. -/
private noncomputable def aux_thetaBasic (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ f x - aux_realRescaled 2 f x

private theorem aux_two_zpow_ne_zero (z : ℤ) : (2 : ℝ) ^ z ≠ 0 := by
  positivity

private theorem aux_realRescaled_thetaBasic (f : ℝ → ℝ) (ell : ℤ) :
    aux_realRescaled ((2 : ℝ) ^ ell) (aux_thetaBasic f) =
      fun x ↦ aux_realRescaled ((2 : ℝ) ^ ell) f x -
        aux_realRescaled ((2 : ℝ) ^ (ell + 1)) f x := by
  funext x
  simp only [aux_thetaBasic, aux_realRescaled]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  field_simp [aux_two_zpow_ne_zero]

private theorem aux_sum_Ico_int_telescope {A : Type*} [AddCommGroup A] (f : ℤ → A)
    (a : ℤ) (N : ℕ) :
    (∑ r ∈ Finset.Ico a (a + (N : ℤ)), (f r - f (r + 1))) =
      f a - f (a + (N : ℤ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ha : a ≤ a + (N : ℤ) := by omega
    rw [show a + ((N + 1 : ℕ) : ℤ) = (a + (N : ℤ)) + 1 by omega]
    rw [← Finset.sum_Ico_add_eq_sum_Ico_add_one ha]
    rw [ih]
    abel

private theorem aux_sum_Icc_int_telescope {A : Type*} [AddCommGroup A] (f : ℤ → A)
    (a : ℤ) (N : ℕ) :
    (∑ r ∈ Finset.Icc a (a + (N : ℤ)), (f r - f (r + 1))) =
      f a - f (a + (N : ℤ) + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  have h := aux_sum_Ico_int_telescope f a (N + 1)
  convert h using 1 <;> push_cast <;> ring

private theorem aux_bumpBasic_partial_sum_eq (f : ℝ → ℝ) (m : ℤ) (N : ℕ) :
    aux_integerIntervalSum
      (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell) (aux_thetaBasic f))
      m (m + (N : ℤ)) =
      fun x ↦ aux_realRescaled ((2 : ℝ) ^ m) f x -
        aux_realRescaled ((2 : ℝ) ^ (m + (N : ℤ) + 1)) f x := by
  funext x
  unfold aux_integerIntervalSum
  simp_rw [aux_realRescaled_thetaBasic]
  exact aux_sum_Icc_int_telescope
    (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell) f x) m N

private theorem aux_bumpBasic_rescale_abs_le (f : ℝ → ℝ) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (t x : ℝ) (ht : 0 < t) :
    |aux_realRescaled t f x| ≤ C * t⁻¹ := by
  unfold aux_realRescaled
  rw [abs_mul, abs_of_pos (inv_pos.mpr ht)]
  calc
    t⁻¹ * |f (t⁻¹ * x)| ≤ t⁻¹ * C :=
      mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr ht.le)
    _ = C * t⁻¹ := mul_comm _ _

private theorem aux_bumpBasic_zpow_tail_factor (C : ℝ) (m : ℤ) (n : ℕ) :
    C * ((2 : ℝ) ^ (m + (n : ℤ) + 1))⁻¹ =
      (C * ((2 : ℝ) ^ m)⁻¹ * (2 : ℝ)⁻¹) * ((1 / 2 : ℝ) ^ n) := by
  rw [show m + (n : ℤ) + 1 = m + ((n : ℤ) + 1) by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) m ((n : ℤ) + 1),
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) (n : ℤ) 1,
    zpow_natCast, div_pow]
  field_simp [aux_two_zpow_ne_zero]
  ring

private theorem aux_bumpBasic_uniform_partial_sum (f : ℝ → ℝ) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (m : ℤ) :
    aux_uniformlyConverges
      (fun N ↦ aux_integerIntervalSum
        (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell) (aux_thetaBasic f))
        m (m + (N : ℤ)))
      (aux_realRescaled ((2 : ℝ) ^ m) f) := by
  intro ε hε
  let A : ℝ := C * ((2 : ℝ) ^ m)⁻¹ * (2 : ℝ)⁻¹
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Tendsto (fun n : ℕ => A * (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    by simpa using hpow.const_mul A
  have hevent : ∀ᶠ n : ℕ in atTop, A * (1 / 2 : ℝ) ^ n ∈ Metric.ball 0 ε :=
    hlim.eventually (Metric.ball_mem_nhds _ hε)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x
  have hsmall : |A * (1 / 2 : ℝ) ^ n| < ε := by
    simpa [Metric.mem_ball, Real.dist_eq] using hN n hn
  have hscale : 0 < (2 : ℝ) ^ (m + (n : ℤ) + 1) :=
    zpow_pos (by norm_num) _
  have hcoef : C * ((2 : ℝ) ^ (m + (n : ℤ) + 1))⁻¹ < ε := by
    rw [aux_bumpBasic_zpow_tail_factor]
    exact (le_abs_self _).trans_lt (by simpa [A] using hsmall)
  change |aux_integerIntervalSum
    (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell) (aux_thetaBasic f))
    m (m + (n : ℤ)) x - aux_realRescaled ((2 : ℝ) ^ m) f x| < ε
  rw [aux_bumpBasic_partial_sum_eq]
  have hdiff :
      (aux_realRescaled ((2 : ℝ) ^ m) f x -
        aux_realRescaled ((2 : ℝ) ^ (m + (n : ℤ) + 1)) f x) -
          aux_realRescaled ((2 : ℝ) ^ m) f x =
        -aux_realRescaled ((2 : ℝ) ^ (m + (n : ℤ) + 1)) f x := by
    ring
  rw [hdiff, abs_neg]
  exact (aux_bumpBasic_rescale_abs_le f C hC _ x hscale).trans_lt hcoef

private theorem aux_bumpBasic_rescale_integrable (f : SchwartzMap ℝ ℝ) (t : ℝ)
    (ht : 0 < t) :
    Integrable (aux_realRescaled t (fun x ↦ f x)) := by
  unfold aux_realRescaled
  convert (f.integrable.comp_mul_left' (inv_ne_zero ht.ne')).const_mul t⁻¹ using 1

private theorem aux_bumpBasic_fourier_sub_of_integrable (f g : ℝ → ℝ)
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

private theorem aux_bumpBasic_rescale_fourier (t : ℝ) (ht : 0 < t)
    (f : ℝ → ℝ) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ => (aux_realRescaled t f x : ℂ)) xi =
      FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) (t * xi) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun q => (f q : ℂ) *
    Complex.exp (-((2 : ℂ) * Real.pi * Complex.I * (q : ℂ) * ((t * xi : ℝ) : ℂ)))
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) •
        (aux_realRescaled t f x : ℂ)) = ∫ x : ℝ, (t⁻¹ : ℂ) * g (t⁻¹ * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [g, aux_realRescaled]
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
        (f x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [g]
      push_cast
      ring

private theorem aux_bumpBasic_fourier_theta (f : SchwartzMap ℝ ℝ) (xi : ℝ) :
    FourierTransform.fourier (fun x : ℝ ↦ (aux_thetaBasic (fun y ↦ f y) x : ℂ)) xi =
      FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ)) xi -
        FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ)) (2 * xi) := by
  rw [show (fun x : ℝ ↦ (aux_thetaBasic (fun y ↦ f y) x : ℂ)) =
      (fun x : ℝ ↦ (((fun y ↦ f y) x -
        aux_realRescaled 2 (fun y ↦ f y) x : ℝ) : ℂ)) by rfl,
    aux_bumpBasic_fourier_sub_of_integrable _ _ f.integrable
      (aux_bumpBasic_rescale_integrable f 2 (by norm_num)),
    aux_bumpBasic_rescale_fourier 2 (by norm_num)]

private theorem aux_bumpBasic_fourier_theta_support (f : SchwartzMap ℝ ℝ)
    (hsupp : Function.support (FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ))) ⊆
      Set.Icc (-1 : ℝ) 1)
    (hone : ∀ xi ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
      FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ)) xi = 1) :
    Function.support (FourierTransform.fourier (fun x : ℝ ↦
      (aux_thetaBasic (fun y ↦ f y) x : ℂ))) ⊆ aux_frequencyAnnulus := by
  intro xi hxi
  by_contra hxann
  apply (Function.mem_support.mp hxi)
  rw [aux_bumpBasic_fourier_theta]
  have hzero (u : ℝ) (hu : u ∉ Set.Icc (-1 : ℝ) 1) :
      FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ)) u = 0 := by
    by_cases hz : FourierTransform.fourier (fun x : ℝ ↦ (f x : ℂ)) u = 0
    · exact hz
    exfalso
    exact hu (hsupp (Function.mem_support.mpr hz))
  by_cases hleft : -(1 / 4 : ℝ) < xi
  · by_cases hright : xi < 1 / 4
    · rw [hone xi ⟨by linarith, by linarith⟩,
        hone (2 * xi) ⟨by linarith, by linarith⟩]
      norm_num
    · have htail : 1 < xi := by
        by_contra h
        apply hxann
        exact Or.inr ⟨le_of_not_gt hright, le_of_not_gt h⟩
      rw [hzero xi (by rintro ⟨_, hupper⟩; linarith),
        hzero (2 * xi) (by rintro ⟨_, hupper⟩; linarith)]
      ring
  · have htail : xi < -1 := by
      by_contra h
      apply hxann
      exact Or.inl ⟨le_of_not_gt h, le_of_not_gt hleft⟩
    rw [hzero xi (by rintro ⟨hlower, _⟩; linarith),
      hzero (2 * xi) (by rintro ⟨hlower, _⟩; linarith)]
    ring

/--
\begin{lemma}\label{lem:bumpbasic}
Let $\theta$ be as in \eqref{eqn:thetadef}.  Its Fourier transform is supported in
$[-1,-2^{-2}]\cup[2^{-2},1]$, and for every $m\in\mathbb Z$ the uniformly
convergent series $\sum_{\ell=m}^\infty\theta_{(2^\ell)}$ equals
$(\phi_0)_{(2^m)}$.
\end{lemma}
-/
theorem bumpBasic (b : windowBasedBumpFunctions) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.theta b x : ℂ))) ⊆ aux_frequencyAnnulus ∧
    ∀ m : ℤ,
      aux_uniformlyConverges
        (fun N ↦ aux_integerIntervalSum
          (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell)
            (windowBasedBumpFunctions.theta b)) m (m + (N : ℤ)))
        (aux_realRescaled ((2 : ℝ) ^ m) (fun x ↦ b.phi0 x)) := by
  have hwindow : cnWindow C_uniPair N_uniPair b.phi0 := b.universalPair.1
  have hsupp := hwindow.2.2.1
  have hone := hwindow.2.2.2.1
  have htheta : windowBasedBumpFunctions.theta b =
      aux_thetaBasic (fun x ↦ b.phi0 x) := by
    rfl
  constructor
  · rw [htheta]
    exact aux_bumpBasic_fourier_theta_support b.phi0 hsupp hone
  · intro m
    rw [htheta]
    apply aux_bumpBasic_uniform_partial_sum (fun x ↦ b.phi0 x)
      (SchwartzMap.seminorm ℝ 0 0 b.phi0)
    intro x
    simpa [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ b.phi0 x

/-! ### Finite identities for the characteristic-function decomposition -/

private theorem aux_char_realRescaled_continuous (t : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (aux_realRescaled t f) := by
  unfold aux_realRescaled
  fun_prop

private theorem aux_char_indicator_mul_integrable (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    Integrable (fun y : ℝ => aux_indicator (Set.Icc 0 1) y * f (x - y)) := by
  have hcont : Continuous (fun y : ℝ => f (x - y)) :=
    hf.comp (continuous_const.sub continuous_id)
  rw [show (fun y : ℝ => aux_indicator (Set.Icc 0 1) y * f (x - y)) =
      Set.indicator (Set.Icc (0 : ℝ) 1) (fun y => f (x - y)) by
        funext y
        simp [aux_indicator, Set.indicator_apply],
    MeasureTheory.integrable_indicator_iff measurableSet_Icc]
  exact hcont.integrableOn_Icc

private theorem aux_char_convolution_integer_sum_eq (b : windowBasedBumpFunctions)
    (a c : ℤ) :
    aux_integerIntervalSum
      (fun ell ↦ aux_realConvolution (aux_indicator (Set.Icc 0 1))
        (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b))) a c =
      aux_realConvolution (aux_indicator (Set.Icc 0 1))
        (aux_integerIntervalSum
          (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell)
            (windowBasedBumpFunctions.theta b)) a c) := by
  funext x
  have htheta : Continuous (windowBasedBumpFunctions.theta b) := by
    unfold windowBasedBumpFunctions.theta
    apply b.phi0.continuous.sub
    apply aux_char_realRescaled_continuous 2
    exact b.phi0.continuous
  have hscale (ell : ℤ) : Continuous
      (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b)) := by
    apply aux_char_realRescaled_continuous
    exact htheta
  unfold aux_integerIntervalSum aux_realConvolution
  change (∑ j ∈ Finset.Icc a c,
      ∫ y : ℝ, aux_indicator (Set.Icc 0 1) y *
        aux_realRescaled ((2 : ℝ) ^ j) (windowBasedBumpFunctions.theta b) (x - y)) =
      ∫ y : ℝ, aux_indicator (Set.Icc 0 1) y *
        ∑ j ∈ Finset.Icc a c,
          aux_realRescaled ((2 : ℝ) ^ j) (windowBasedBumpFunctions.theta b) (x - y)
  rw [show (fun y : ℝ => aux_indicator (Set.Icc 0 1) y *
      ∑ j ∈ Finset.Icc a c,
        aux_realRescaled ((2 : ℝ) ^ j) (windowBasedBumpFunctions.theta b) (x - y)) =
      fun y : ℝ => ∑ j ∈ Finset.Icc a c,
        aux_indicator (Set.Icc 0 1) y *
          aux_realRescaled ((2 : ℝ) ^ j) (windowBasedBumpFunctions.theta b) (x - y) by
        funext y
        rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finset_sum]
  intro ell _
  exact aux_char_indicator_mul_integrable _ (hscale ell) x

private theorem aux_char_convolution_sub_right (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    aux_realConvolution (aux_indicator (Set.Icc 0 1)) (fun x ↦ f x - g x) =
      fun x ↦ aux_realConvolution (aux_indicator (Set.Icc 0 1)) f x -
        aux_realConvolution (aux_indicator (Set.Icc 0 1)) g x := by
  funext x
  unfold aux_realConvolution
  rw [show (fun y : ℝ => aux_indicator (Set.Icc 0 1) y * (f (x - y) - g (x - y))) =
      fun y ↦ aux_indicator (Set.Icc 0 1) y * f (x - y) -
        aux_indicator (Set.Icc 0 1) y * g (x - y) by
        funext y
        ring,
    integral_sub (aux_char_indicator_mul_integrable f hf x)
      (aux_char_indicator_mul_integrable g hg x)]

private theorem aux_char_partial_sum_eq_rescaled (b : windowBasedBumpFunctions) (N : ℕ)
    (hN : 1 ≤ N) :
    (fun x ↦
      aux_realConvolution (aux_indicator (Set.Icc 0 1)) (fun y ↦ b.phi0 y) x +
        aux_integerIntervalSum
          (fun ell ↦ aux_realConvolution (aux_indicator (Set.Icc 0 1))
            (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b)))
          (-(N : ℤ)) (-1) x) =
      aux_realConvolution (aux_indicator (Set.Icc 0 1))
        (aux_realRescaled ((2 : ℝ) ^ (-(N : ℤ))) (fun y ↦ b.phi0 y)) := by
  have htheta : windowBasedBumpFunctions.theta b =
      aux_thetaBasic (fun y ↦ b.phi0 y) := by
    rfl
  have hphi : Continuous (fun y ↦ b.phi0 y) := b.phi0.continuous
  have hrescale : Continuous
      (aux_realRescaled ((2 : ℝ) ^ (-(N : ℤ))) (fun y ↦ b.phi0 y)) := by
    apply aux_char_realRescaled_continuous
    exact hphi
  have hone : (-(N : ℤ) + ((N - 1 : ℕ) : ℤ)) = -1 := by omega
  have hsum := aux_bumpBasic_partial_sum_eq (fun y ↦ b.phi0 y) (-(N : ℤ)) (N - 1)
  rw [hone] at hsum
  have hzeroScale : aux_realRescaled ((2 : ℝ) ^ ((-1 : ℤ) + 1))
      (fun y ↦ b.phi0 y) = fun y ↦ b.phi0 y := by
    funext y
    simp [aux_realRescaled]
  rw [hzeroScale] at hsum
  rw [aux_char_convolution_integer_sum_eq, htheta, hsum,
    aux_char_convolution_sub_right _ _ hrescale hphi]
  funext x
  simp [aux_realRescaled]

/-! ### A bounded approximate identity in `L²` -/

private theorem aux_char_translation_integral_norm_continuous {f : ℝ → ℝ}
    (hf : Integrable f) :
    Continuous (fun p : ℝ => ∫ x : ℝ, ‖f (x - p) - f x‖) := by
  let Traw : C(ℝ × ℝ, ℝ) :=
    ⟨fun z => z.2 - z.1, by fun_prop⟩
  let T : ℝ → C(ℝ, ℝ) := fun p => Traw.curry p
  have hT : Continuous T := Traw.curry.continuous
  let hmem : MemLp f 1 volume := memLp_one_iff_integrable.mpr hf
  let u : Lp ℝ 1 volume := hmem.toLp
  let F : ℝ → Lp ℝ 1 volume := fun p =>
    Lp.compMeasurePreserving (T p) (measurePreserving_sub_right volume p) u
  have hF : Continuous F := by
    exact continuous_const.compMeasurePreservingLp hT
      (fun p => measurePreserving_sub_right volume p) (by simp)
  have hFnorm (p : ℝ) : ‖F p - u‖ = ∫ x : ℝ, ‖f (x - p) - f x‖ := by
    have hcomp : ((F p - u : Lp ℝ 1 volume) : ℝ → ℝ) =ᵐ[volume]
        fun x => f (x - p) - f x := by
      filter_upwards [Lp.coeFn_sub (F p) u,
        Lp.coeFn_compMeasurePreserving u (measurePreserving_sub_right volume p),
        hmem.coeFn_toLp.comp_tendsto
          (Measure.QuasiMeasurePreserving.tendsto_ae
            (measurePreserving_sub_right volume p).quasiMeasurePreserving),
        hmem.coeFn_toLp] with x hsub hF hshift hu
      rw [hsub]
      change ((Lp.compMeasurePreserving (fun x : ℝ => x - p)
        (measurePreserving_sub_right volume p) u : Lp ℝ 1 volume) : ℝ → ℝ) x - u x = _
      rw [hF]
      simpa only [Function.comp_apply] using congrArg₂ (· - ·) hshift hu
    have hdiff : Integrable (fun x : ℝ => f (x - p) - f x) :=
      (hf.comp_sub_right p).sub hf
    rw [Lp.norm_def, eLpNorm_congr_ae hcomp, eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm hdiff,
      ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _)]
  have hFu : Continuous fun p => ‖F p - u‖ := (hF.sub continuous_const).norm
  simpa only [hFnorm] using hFu

private theorem aux_char_translation_integral_norm_tendsto {f : ℝ → ℝ}
    (hf : Integrable f) :
    Tendsto (fun p : ℝ => ∫ x : ℝ, ‖f (x - p) - f x‖) (nhds 0) (nhds 0) := by
  simpa using (aux_char_translation_integral_norm_continuous hf).tendsto 0

private theorem aux_integrable_shear_difference
    (f psi : ℝ → ℝ) (hf : Integrable f) (hfm : Measurable f)
    (hpsi : Integrable psi) (hpsim : Measurable psi) (t : ℝ) :
    Integrable (fun z : ℝ × ℝ =>
      psi z.2 * (f (z.1 - t * z.2) - f z.1)) := by
  let P : ℝ × ℝ → ℝ := fun z => psi z.2 * f (z.1 - t * z.2)
  let Q : ℝ × ℝ → ℝ := fun z => psi z.2 * f z.1
  have hPmeas : AEStronglyMeasurable P ((volume : Measure ℝ).prod volume) := by
    exact ((hpsim.comp measurable_snd).aestronglyMeasurable.mul
      (hfm.comp (measurable_fst.sub (measurable_const.mul measurable_snd))).aestronglyMeasurable)
  have hP : Integrable P ((volume : Measure ℝ).prod volume) := by
    rw [integrable_prod_iff' hPmeas]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · dsimp [P]
      simpa [mul_comm] using (hf.comp_sub_right (t * y)).mul_const (psi y)
    · have hnorm (y : ℝ) :
          (∫ x : ℝ, ‖P (x, y)‖) = ‖psi y‖ * ∫ x : ℝ, ‖f x‖ := by
        dsimp [P]
        simp only [Real.norm_eq_abs, abs_mul]
        rw [integral_const_mul]
        congr 1
        exact integral_sub_right_eq_self (fun x : ℝ => ‖f x‖) (t * y)
      convert hpsi.norm.const_mul (∫ x : ℝ, ‖f x‖) using 1
      ext y
      rw [hnorm]
      ring
  have hQ : Integrable Q ((volume : Measure ℝ).prod volume) := by
    simpa [Q, mul_comm] using hf.mul_prod hpsi
  have hdiff : Integrable (fun z : ℝ × ℝ =>
      psi z.2 * (f (z.1 - t * z.2) - f z.1)) ((volume : Measure ℝ).prod volume) := by
    convert hP.sub hQ using 1
    funext z
    dsimp [P, Q]
    ring
  simpa only [Measure.volume_eq_prod] using hdiff

private theorem aux_scaled_convolution_eq_shear
    (f psi : ℝ → ℝ) (hf : Integrable f) (hfm : Measurable f)
    (hpsi : Integrable psi) (hpsim : Measurable psi)
    (C : ℝ) (hC : ∀ z : ℝ, |f z| ≤ C)
    (hmass : ∫ y : ℝ, psi y = 1)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    (∫ p : ℝ, f (x - p) * aux_realRescaled t psi p) - f x =
      ∫ y : ℝ, psi y * (f (x - t * y) - f x) := by
  have hA : Integrable (fun y : ℝ => f (x - t * y) * psi y) := by
    have hshiftMeas : AEStronglyMeasurable (fun y : ℝ => f (x - t * y)) :=
      (hfm.comp (measurable_const.sub (measurable_const.mul measurable_id))).aestronglyMeasurable
    have hbound : ∀ᵐ y : ℝ, ‖f (x - t * y)‖ ≤ C := by
      filter_upwards [] with y
      simpa [Real.norm_eq_abs] using hC (x - t * y)
    simpa [mul_comm] using hpsi.bdd_mul hshiftMeas hbound
  have hB : Integrable (fun y : ℝ => f x * psi y) := hpsi.const_mul (f x)
  have hrescale :
      (∫ p : ℝ, f (x - p) * aux_realRescaled t psi p) =
      ∫ y : ℝ, f (x - t * y) * psi y := by
      let g : ℝ → ℝ := fun y => f (x - t * y) * psi y
      calc
        (∫ p : ℝ, f (x - p) * aux_realRescaled t psi p) =
            ∫ p : ℝ, t⁻¹ * g (t⁻¹ * p) := by
          apply integral_congr_ae
          filter_upwards [] with p
          dsimp [g, aux_realRescaled]
          field_simp
        _ = t⁻¹ * ∫ p : ℝ, g (t⁻¹ * p) := by rw [integral_const_mul]
        _ = t⁻¹ * (|t| * ∫ y : ℝ, g y) := by
          rw [Measure.integral_comp_inv_mul_left]
          simp only [smul_eq_mul]
        _ = ∫ y : ℝ, f (x - t * y) * psi y := by
          dsimp [g]
          rw [abs_of_pos ht]
          field_simp
  calc
    (∫ p : ℝ, f (x - p) * aux_realRescaled t psi p) - f x =
        (∫ y : ℝ, f (x - t * y) * psi y) - f x := by rw [hrescale]
    _ = (∫ y : ℝ, f (x - t * y) * psi y) - f x * ∫ y : ℝ, psi y := by
      rw [hmass, mul_one]
    _ = ∫ y : ℝ, f (x - t * y) * psi y - f x * psi y := by
      rw [← integral_const_mul]
      exact (integral_sub hA hB).symm
    _ = ∫ y : ℝ, psi y * (f (x - t * y) - f x) := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring

private theorem aux_realConvolution_swap (f g : ℝ → ℝ) (x : ℝ) :
    aux_realConvolution f g x = ∫ p : ℝ, f (x - p) * g p := by
  unfold aux_realConvolution
  calc
    (∫ y : ℝ, f y * g (x - y)) =
        ∫ y : ℝ, (fun p : ℝ => f (x - p) * g p) (x - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          congr 2 <;> ring
    _ = ∫ p : ℝ, f (x - p) * g p :=
      integral_sub_left_eq_self (fun p : ℝ => f (x - p) * g p) volume x

private theorem aux_translation_difference_bound
    (f : ℝ → ℝ) (hf : Integrable f) (p : ℝ) :
    (∫ x : ℝ, ‖f (x - p) - f x‖) ≤ 2 * ∫ x : ℝ, ‖f x‖ := by
  have hshift : Integrable (fun x : ℝ => f (x - p)) := hf.comp_sub_right p
  have hleft : Integrable (fun x : ℝ => ‖f (x - p) - f x‖) := (hshift.sub hf).norm
  have hright : Integrable (fun x : ℝ => ‖f (x - p)‖ + ‖f x‖) := hshift.norm.add hf.norm
  calc
    (∫ x : ℝ, ‖f (x - p) - f x‖) ≤
        ∫ x : ℝ, (‖f (x - p)‖ + ‖f x‖) := by
          exact integral_mono hleft hright (fun x => norm_sub_le _ _)
    _ = (∫ x : ℝ, ‖f (x - p)‖) + ∫ x : ℝ, ‖f x‖ := by
      rw [integral_add hshift.norm hf.norm]
    _ = 2 * ∫ x : ℝ, ‖f x‖ := by
      rw [integral_sub_right_eq_self (fun x : ℝ => ‖f x‖) p]
      ring

private theorem aux_raw_approximate_identity_L1
    (f psi : ℝ → ℝ) (hf : Integrable f) (hfm : Measurable f)
    (hpsi : Integrable psi) (hpsim : Measurable psi)
    (C : ℝ) (hC : ∀ z : ℝ, |f z| ≤ C)
    (hmass : ∫ y : ℝ, psi y = 1)
    (htrans : Tendsto (fun p : ℝ => ∫ x : ℝ, ‖f (x - p) - f x‖)
      (nhds 0) (nhds 0)) :
    Tendsto (fun t : ℝ => ∫ x : ℝ,
      |aux_realConvolution f (aux_realRescaled t psi) x - f x|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let B : ℝ → ℝ := fun y => (2 * ∫ x : ℝ, ‖f x‖) * |psi y|
  have hB : Integrable B := by
    exact hpsi.norm.const_mul _
  have hmeas : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (fun y : ℝ => ∫ x : ℝ,
        ‖psi y * (f (x - t * y) - f x)‖) := by
    filter_upwards [] with t
    exact (aux_integrable_shear_difference f psi hf hfm hpsi hpsim t).integral_norm_prod_right.aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ᵐ y : ℝ,
      ‖∫ x : ℝ, ‖psi y * (f (x - t * y) - f x)‖‖ ≤ B y := by
    filter_upwards [] with t
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have hnorm : (fun x : ℝ => ‖psi y * (f (x - t * y) - f x)‖) =
        fun x : ℝ => ‖psi y‖ * ‖f (x - t * y) - f x‖ := by
      funext x
      exact norm_mul _ _
    rw [hnorm]
    rw [integral_const_mul]
    calc
      ‖psi y‖ * (∫ x : ℝ, ‖f (x - t * y) - f x‖) ≤
          ‖psi y‖ * (2 * ∫ x : ℝ, ‖f x‖) := by
        exact mul_le_mul_of_nonneg_left (aux_translation_difference_bound f hf _) (norm_nonneg _)
      _ = B y := by
        dsimp [B]
        ring
  have hlim : ∀ᵐ y : ℝ, Tendsto (fun t : ℝ => ∫ x : ℝ,
      ‖psi y * (f (x - t * y) - f x)‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    filter_upwards [] with y
    have ht : Tendsto (fun t : ℝ => t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have harg : Tendsto (fun t : ℝ => t * y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using ht.mul (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => y) (nhdsWithin 0 (Set.Ioi 0)) (nhds y))
    have hmul : Tendsto (fun t : ℝ => ‖psi y‖ *
        ∫ x : ℝ, ‖f (x - t * y) - f x‖)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => ‖psi y‖)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ‖psi y‖)).mul (htrans.comp harg))
    simpa only [norm_mul, integral_const_mul] using hmul
  have houter : Tendsto (fun t : ℝ => ∫ y : ℝ, ∫ x : ℝ,
      ‖psi y * (f (x - t * y) - f x)‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using MeasureTheory.tendsto_integral_filter_of_dominated_convergence B hmeas
      hbound hB hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) houter
  · filter_upwards [] with t
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have hD : Integrable (fun z : ℝ × ℝ =>
        psi z.2 * (f (z.1 - t * z.2) - f z.1)) :=
      aux_integrable_shear_difference f psi hf hfm hpsi hpsim t
    have hleft : Integrable (fun x : ℝ =>
        |aux_realConvolution f (aux_realRescaled t psi) x - f x|) := by
      have hslice : Integrable (fun x : ℝ => ∫ y : ℝ,
          psi y * (f (x - t * y) - f x)) := by
        simpa only [Measure.volume_eq_prod] using hD.integral_prod_left
      convert hslice.norm using 1
      funext x
      rw [aux_realConvolution_swap]
      rw [aux_scaled_convolution_eq_shear f psi hf hfm hpsi hpsim C hC hmass t ht x]
      simp only [Real.norm_eq_abs]
    have hright : Integrable (fun x : ℝ => ∫ y : ℝ,
        ‖psi y * (f (x - t * y) - f x)‖) := by
      simpa only [Measure.volume_eq_prod] using hD.integral_norm_prod_left
    calc
      (∫ x : ℝ, |aux_realConvolution f (aux_realRescaled t psi) x - f x|) ≤
          ∫ x : ℝ, ∫ y : ℝ, ‖psi y * (f (x - t * y) - f x)‖ := by
        apply integral_mono hleft hright
        intro x
        dsimp
        rw [aux_realConvolution_swap]
        rw [← Real.norm_eq_abs,
          aux_scaled_convolution_eq_shear f psi hf hfm hpsi hpsim C hC hmass t ht x]
        exact norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, ∫ x : ℝ, ‖psi y * (f (x - t * y) - f x)‖ := by
        let D : ℝ → ℝ → ℝ := fun x y => ‖psi y * (f (x - t * y) - f x)‖
        simpa only [D, Function.uncurry, Measure.volume_eq_prod] using
          (integral_integral_swap hD.norm)

private theorem aux_l1_to_l2_tendsto_of_uniform_bound
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (e : ι → ℝ → ℝ) (D : ℝ)
    (hInt : ∀ᶠ i in l, Integrable (e i))
    (hMeas : ∀ᶠ i in l, AEStronglyMeasurable (e i))
    (hBound : ∀ᶠ i in l, ∀ᵐ x : ℝ, ‖e i x‖ ≤ D)
    (hL1 : Tendsto (fun i => ∫ x : ℝ, ‖e i x‖) l (nhds 0)) :
    Tendsto (fun i => eLpNorm (e i) 2 volume) l (nhds 0) := by
  let A : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (∫ x : ℝ, ‖e i x‖)
  let B : ℝ≥0∞ := ENNReal.ofReal D
  have hA : Tendsto A l (nhds 0) := by
    simpa [A] using ENNReal.tendsto_ofReal hL1
  have hAhalf : Tendsto (fun i => A i ^ ((2 : ℝ)⁻¹)) l (nhds 0) := by
    simpa using hA.ennrpow_const ((2 : ℝ)⁻¹)
  have hBfinite : B ^ (1 - (2 : ℝ)⁻¹) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp [B])
  have hRight : Tendsto (fun i => A i ^ ((2 : ℝ)⁻¹) *
      B ^ (1 - (2 : ℝ)⁻¹)) l (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hAhalf (Or.inr hBfinite)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0∞)) l (nhds 0)) hRight
  · filter_upwards [] with i
    exact bot_le
  · filter_upwards [hInt, hMeas, hBound] with i hiInt hiMeas hiBound
    have hOne : eLpNorm (e i) 1 volume ≤ A i := by
      exact Codex.aux_eLpNorm_one_le_of_integral_norm_le hiInt le_rfl
    have hTop : eLpNorm (e i) ∞ volume ≤ B := by
      exact Codex.aux_eLpNorm_top_le_of_bound hiBound
    simpa [A, B] using
      (Codex.aux_eLpNorm_le_of_l1_linf_bounds hiMeas (q := (2 : ℝ)) (by norm_num)
        hOne hTop)

private theorem aux_raw_approximate_identity_error_bound
    (f psi : ℝ → ℝ) (hf : Integrable f) (hfm : Measurable f)
    (hpsi : Integrable psi) (hpsim : Measurable psi)
    (C : ℝ) (hC : ∀ z : ℝ, |f z| ≤ C)
    (hmass : ∫ y : ℝ, psi y = 1)
    (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ‖aux_realConvolution f (aux_realRescaled t psi) x - f x‖ ≤
      2 * C * ∫ y : ℝ, ‖psi y‖ := by
  have hShift : Integrable (fun y : ℝ => f (x - t * y) * psi y) := by
    have hshiftMeas : AEStronglyMeasurable (fun y : ℝ => f (x - t * y)) :=
      (hfm.comp (measurable_const.sub (measurable_const.mul measurable_id))).aestronglyMeasurable
    have hbound : ∀ᵐ y : ℝ, ‖f (x - t * y)‖ ≤ C := by
      filter_upwards [] with y
      simpa [Real.norm_eq_abs] using hC (x - t * y)
    simpa [mul_comm] using hpsi.bdd_mul hshiftMeas hbound
  have hConst : Integrable (fun y : ℝ => f x * psi y) := hpsi.const_mul (f x)
  have hShear : Integrable (fun y : ℝ => psi y * (f (x - t * y) - f x)) := by
    convert hShift.sub hConst using 1
    funext y
    change psi y * (f (x - t * y) - f x) =
      f (x - t * y) * psi y - f x * psi y
    ring
  have hMajorant : Integrable (fun y : ℝ => (2 * C) * ‖psi y‖) :=
    hpsi.norm.const_mul _
  rw [aux_realConvolution_swap,
    aux_scaled_convolution_eq_shear f psi hf hfm hpsi hpsim C hC hmass t ht x]
  calc
    ‖∫ y : ℝ, psi y * (f (x - t * y) - f x)‖ ≤
        ∫ y : ℝ, ‖psi y * (f (x - t * y) - f x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, (2 * C) * ‖psi y‖ := by
      apply integral_mono hShear.norm hMajorant
      intro y
      change ‖psi y * (f (x - t * y) - f x)‖ ≤ (2 * C) * ‖psi y‖
      rw [norm_mul]
      calc
        ‖psi y‖ * ‖f (x - t * y) - f x‖ ≤ ‖psi y‖ * (2 * C) := by
          gcongr
          calc
            ‖f (x - t * y) - f x‖ ≤ ‖f (x - t * y)‖ + ‖f x‖ := norm_sub_le _ _
            _ ≤ C + C := add_le_add
              (by simpa [Real.norm_eq_abs] using hC (x - t * y))
              (by simpa [Real.norm_eq_abs] using hC x)
            _ = 2 * C := by ring
        _ = (2 * C) * ‖psi y‖ := by ring
    _ = 2 * C * ∫ y : ℝ, ‖psi y‖ := by
      rw [integral_const_mul]

private theorem aux_raw_approximate_identity_error_integrable
    (f psi : ℝ → ℝ) (hf : Integrable f) (hfm : Measurable f)
    (hpsi : Integrable psi) (hpsim : Measurable psi)
    (C : ℝ) (hC : ∀ z : ℝ, |f z| ≤ C)
    (hmass : ∫ y : ℝ, psi y = 1)
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ =>
      aux_realConvolution f (aux_realRescaled t psi) x - f x) := by
  have hD : Integrable (fun z : ℝ × ℝ =>
      psi z.2 * (f (z.1 - t * z.2) - f z.1)) :=
    aux_integrable_shear_difference f psi hf hfm hpsi hpsim t
  have hSlice : Integrable (fun x : ℝ => ∫ y : ℝ,
      psi y * (f (x - t * y) - f x)) := by
    simpa only [Measure.volume_eq_prod] using hD.integral_prod_left
  convert hSlice using 1
  funext x
  rw [aux_realConvolution_swap,
    aux_scaled_convolution_eq_shear f psi hf hfm hpsi hpsim C hC hmass t ht x]

private theorem aux_raw_approximate_identity_L2
    (f psi : ℝ → ℝ) (hf : Integrable f) (hfm : Measurable f)
    (hpsi : Integrable psi) (hpsim : Measurable psi)
    (C : ℝ) (hC : ∀ z : ℝ, |f z| ≤ C)
    (hmass : ∫ y : ℝ, psi y = 1)
    (htrans : Tendsto (fun p : ℝ => ∫ x : ℝ, ‖f (x - p) - f x‖)
      (nhds 0) (nhds 0)) :
    Tendsto (fun t : ℝ => eLpNorm (fun x : ℝ =>
      aux_realConvolution f (aux_realRescaled t psi) x - f x) 2 volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let e : ℝ → ℝ → ℝ := fun t x =>
    aux_realConvolution f (aux_realRescaled t psi) x - f x
  let D : ℝ := 2 * C * ∫ y : ℝ, ‖psi y‖
  have hInt : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), Integrable (e t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact aux_raw_approximate_identity_error_integrable f psi hf hfm hpsi hpsim C hC hmass t ht
  have hMeas : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), AEStronglyMeasurable (e t) := by
    filter_upwards [hInt] with t ht
    exact ht.aestronglyMeasurable
  have hBound : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ᵐ x : ℝ, ‖e t x‖ ≤ D := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards [] with x
    exact aux_raw_approximate_identity_error_bound f psi hf hfm hpsi hpsim C hC hmass t ht x
  have hL1 : Tendsto (fun t : ℝ => ∫ x : ℝ, ‖e t x‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [e, Real.norm_eq_abs] using
      aux_raw_approximate_identity_L1 f psi hf hfm hpsi hpsim C hC hmass htrans
  simpa [e] using aux_l1_to_l2_tendsto_of_uniform_bound e D hInt hMeas hBound hL1

private theorem aux_zpow_neg_nat_tendsto_zero_within :
    Tendsto (fun N : ℕ => (2 : ℝ) ^ (-(N : ℤ))) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
  have hpow : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have heq : (fun N : ℕ => (2 : ℝ) ^ (-(N : ℤ))) =
      fun N : ℕ => (1 / 2 : ℝ) ^ N := by
    funext N
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    norm_num
  have hzero : Tendsto (fun N : ℕ => (2 : ℝ) ^ (-(N : ℤ))) atTop (nhds 0) := by
    rw [heq]
    exact hpow
  refine tendsto_nhdsWithin_iff.2 ⟨hzero, ?_⟩
  filter_upwards [] with N
  change 0 < (2 : ℝ) ^ (-(N : ℤ))
  exact zpow_pos (by norm_num) _

private theorem aux_indicator_Icc_data :
    Integrable (aux_indicator (Set.Icc (0 : ℝ) 1)) ∧
    Measurable (aux_indicator (Set.Icc (0 : ℝ) 1)) ∧
    (∀ x : ℝ, |aux_indicator (Set.Icc (0 : ℝ) 1) x| ≤ 1) := by
  let f : ℝ → ℝ := aux_indicator (Set.Icc (0 : ℝ) 1)
  have hfmem : MemLp f 1 volume := by
    exact memLp_indicator_const 1 measurableSet_Icc (1 : ℝ)
      (Or.inr measure_Icc_lt_top.ne)
  have hf : Integrable f := memLp_one_iff_integrable.mp hfmem
  have hfm : Measurable f := by
    dsimp [f, aux_indicator]
    exact measurable_const.indicator measurableSet_Icc
  have hbound : ∀ x : ℝ, |f x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [f, aux_indicator, hx]
  exact ⟨hf, hfm, hbound⟩

private theorem aux_phi0_integral_one (b : windowBasedBumpFunctions) :
    ∫ x : ℝ, b.phi0 x = 1 := by
  have hwindow : cnWindow C_uniPair N_uniPair b.phi0 := b.universalPair.1
  have hfourier := hwindow.2.2.2.1 0 (by constructor <;> norm_num)
  rw [Real.fourier_real_eq_integral_exp_smul] at hfourier
  have hcomplex : (∫ x : ℝ, (b.phi0 x : ℂ)) = 1 := by
    simpa using hfourier
  exact_mod_cast hcomplex

/--
\begin{lemma}\label{lem:chardecomp}
With $\phi_0,\theta$ as in Definition \ref{defn:window based bump functions},
\[\mathbf 1_{[0,1]}=\mathbf 1_{[0,1]}*\phi_0+
\sum_{\ell=-\infty}^{-1}\mathbf 1_{[0,1]}*\theta_{(2^\ell)}\]
in $L^2$.
\end{lemma}
-/
theorem charDecomp (b : windowBasedBumpFunctions) :
    aux_convergesInL2
      (fun N ↦ fun x ↦
        aux_realConvolution (aux_indicator (Set.Icc 0 1)) (fun y ↦ b.phi0 y) x +
          aux_integerIntervalSum
            (fun ell ↦ aux_realConvolution (aux_indicator (Set.Icc 0 1))
              (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b)))
            (-(N : ℤ)) (-1) x)
      (aux_indicator (Set.Icc 0 1)) := by
  rcases aux_indicator_Icc_data with ⟨hI, hImeas, hIbound⟩
  have hphi : Integrable (fun x : ℝ ↦ b.phi0 x) := b.phi0.integrable
  have hphiMeas : Measurable (fun x : ℝ ↦ b.phi0 x) := b.phi0.continuous.measurable
  have hmass : ∫ x : ℝ, b.phi0 x = 1 := aux_phi0_integral_one b
  have htrans := aux_char_translation_integral_norm_tendsto hI
  have happrox := aux_raw_approximate_identity_L2
    (aux_indicator (Set.Icc 0 1)) (fun x : ℝ ↦ b.phi0 x)
    hI hImeas hphi hphiMeas 1 hIbound hmass htrans
  have hscaled := happrox.comp aux_zpow_neg_nat_tendsto_zero_within
  unfold aux_convergesInL2
  apply Tendsto.congr' ?_ hscaled
  filter_upwards [eventually_ge_atTop 1] with N hN
  change eLpNorm (fun x =>
    aux_realConvolution (aux_indicator (Set.Icc 0 1))
      (aux_realRescaled ((2 : ℝ) ^ (-(N : ℤ))) (fun y ↦ b.phi0 y)) x -
        aux_indicator (Set.Icc 0 1) x) 2 volume = _
  rw [← aux_char_partial_sum_eq_rescaled b N hN]

/-! ### The low-frequency projection used in the smoothing decomposition -/

private theorem aux_smoothing_realConvolution_complex (f g : ℝ → ℝ) (x : ℝ) :
    (aux_realConvolution f g x : ℂ) =
      ((fun y : ℝ => (f y : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        (fun y : ℝ => (g y : ℂ))) x := by
  unfold aux_realConvolution
  exact (integral_ofReal (𝕜 := ℂ)
    (f := fun y : ℝ => f y * g (x - y))).symm.trans (by
      apply integral_congr_ae
      filter_upwards [] with y
      push_cast
      rfl)

private theorem aux_phi0_reproduces (b : windowBasedBumpFunctions) :
    aux_realConvolution (fun x : ℝ => b.phi0 x)
      (aux_realRescaled (1 / 4 : ℝ) (fun x : ℝ => b.phi0 x)) =
      fun x => b.phi0 x := by
  let phi : ℝ → ℂ := fun x => (b.phi0 x : ℂ)
  let psi : ℝ → ℂ := fun x =>
    (aux_realRescaled (1 / 4 : ℝ) (fun y : ℝ => b.phi0 y) x : ℂ)
  let G : ℝ → ℂ := phi ⋆[ContinuousLinearMap.mul ℂ ℂ] psi
  have hphi : Integrable phi := by
    change Integrable (fun x : ℝ => (b.phi0 x : ℂ))
    exact b.phi0.integrable.ofReal
  have hpsi : Integrable psi := by
    dsimp [psi, aux_realRescaled]
    convert ((b.phi0.integrable.comp_mul_left'
      (by norm_num : ((1 / 4 : ℝ)⁻¹) ≠ 0)).const_mul ((1 / 4 : ℝ)⁻¹)).ofReal using 1 <;>
      norm_num
  have hG : Integrable G := hphi.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hpsi
  have hphiC : Continuous phi := by
    exact Complex.ofRealCLM.continuous.comp b.phi0.continuous
  have hGCont : Continuous G := by
    refine BddAbove.continuous_convolution_left_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) ?_ hphiC hpsi
    refine ⟨SchwartzMap.seminorm ℝ 0 0 b.phi0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa [phi, Complex.norm_real, Real.norm_eq_abs] using
      SchwartzMap.norm_le_seminorm ℝ b.phi0 x
  have hwin : cnWindow C_uniPair N_uniPair b.phi0 := b.universalPair.1
  have hFourier_eq : FourierTransform.fourier G = FourierTransform.fourier phi := by
    funext xi
    rw [show G = phi ⋆[ContinuousLinearMap.mul ℂ ℂ] psi by rfl,
      Real.fourier_mul_convolution_eq hphi hpsi,
      show psi = fun x : ℝ =>
        (aux_realRescaled (1 / 4 : ℝ) (fun y : ℝ => b.phi0 y) x : ℂ) by rfl,
      aux_bumpBasic_rescale_fourier (1 / 4 : ℝ) (by norm_num)]
    by_cases hzero : FourierTransform.fourier phi xi = 0
    · rw [hzero]
      ring
    have hmem := hwin.2.2.1 (Function.mem_support.mpr hzero)
    have hone := hwin.2.2.2.1 ((1 / 4 : ℝ) * xi)
      (by constructor <;> nlinarith [hmem.1, hmem.2])
    dsimp [phi] at hmem hone ⊢
    rw [hone]
    ring
  have hphiFcont : Continuous (FourierTransform.fourier phi) := by
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hphi
  have hphiFcompact : HasCompactSupport (FourierTransform.fourier phi) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    simpa [phi] using hwin.2.2.1
  have hphiFint : Integrable (FourierTransform.fourier phi) :=
    hphiFcont.integrable_of_hasCompactSupport hphiFcompact
  have hGFint : Integrable (FourierTransform.fourier G) := by
    rw [hFourier_eq]
    exact hphiFint
  funext x
  apply Complex.ofReal_injective
  rw [aux_smoothing_realConvolution_complex]
  change G x = phi x
  calc
    G x = FourierTransformInv.fourierInv (FourierTransform.fourier G) x :=
      congrFun (hGCont.fourierInv_fourier_eq hG hGFint).symm x
    _ = FourierTransformInv.fourierInv (FourierTransform.fourier phi) x := by rw [hFourier_eq]
    _ = phi x := congrFun (hphiC.fourierInv_fourier_eq hphi hphiFint) x

private theorem aux_smoothing_indicator_Ico_integrable :
    Integrable (aux_indicator (Set.Ico (0 : ℝ) 1)) := by
  rw [show aux_indicator (Set.Ico (0 : ℝ) 1) =
      Set.indicator (Set.Ico (0 : ℝ) 1) (fun _ : ℝ => 1) by rfl,
    MeasureTheory.integrable_indicator_iff measurableSet_Ico]
  exact (continuous_const.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ico_subset_Icc_self

private theorem aux_smoothing_indicator_Ico_ae_eq_Icc :
    aux_indicator (Set.Ico (0 : ℝ) 1) =ᵐ[volume]
      aux_indicator (Set.Icc (0 : ℝ) 1) := by
  filter_upwards [Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ))] with x hx
  by_cases h : x ∈ Set.Ico (0 : ℝ) 1
  · have h' : x ∈ Set.Icc (0 : ℝ) 1 := by
      change Set.Ico (0 : ℝ) 1 x at h
      change Set.Icc (0 : ℝ) 1 x
      exact hx ▸ h
    simp [aux_indicator, h, h']
  · have h' : x ∉ Set.Icc (0 : ℝ) 1 := by
      intro hi
      apply h
      change Set.Icc (0 : ℝ) 1 x at hi
      change Set.Ico (0 : ℝ) 1 x
      rw [hx]
      exact hi
    simp [aux_indicator, h, h']

private theorem aux_smoothing_convolution_Ico_eq_Icc (g : ℝ → ℝ) :
    aux_realConvolution (aux_indicator (Set.Ico (0 : ℝ) 1)) g =
      aux_realConvolution (aux_indicator (Set.Icc (0 : ℝ) 1)) g := by
  funext x
  unfold aux_realConvolution
  apply integral_congr_ae
  filter_upwards [aux_smoothing_indicator_Ico_ae_eq_Icc] with y hy
  rw [hy]

private theorem aux_smoothing_indicator_Ico_eq_sub_Ici :
    aux_indicator (Set.Ico (0 : ℝ) 1) =
      fun x : ℝ => aux_indicator (Set.Ici 0) x - aux_indicator (Set.Ici 1) x := by
  funext x
  by_cases h0 : 0 ≤ x <;> by_cases h1 : 1 ≤ x
  all_goals simp [aux_indicator, Set.indicator_apply, h0, h1] <;> linarith

private theorem aux_smoothing_convolution_Ici_sub_eq_Ico (g : ℝ → ℝ) (hg : Integrable g) :
    aux_realConvolution (aux_indicator (Set.Ici 0)) g +
        (-aux_realConvolution (aux_indicator (Set.Ici 1)) g) =
      aux_realConvolution (aux_indicator (Set.Ico 0 1)) g := by
  funext x
  have hshift : Integrable (fun y : ℝ => g (x - y)) := hg.comp_sub_left x
  have h0 : Integrable (fun y : ℝ => aux_indicator (Set.Ici 0) y * g (x - y)) := by
    rw [show (fun y : ℝ => aux_indicator (Set.Ici 0) y * g (x - y)) =
      Set.indicator (Set.Ici (0 : ℝ)) (fun y => g (x - y)) by
        funext y
        simp [aux_indicator, Set.indicator_apply]]
    exact hshift.indicator measurableSet_Ici
  have h1 : Integrable (fun y : ℝ => aux_indicator (Set.Ici 1) y * g (x - y)) := by
    rw [show (fun y : ℝ => aux_indicator (Set.Ici 1) y * g (x - y)) =
      Set.indicator (Set.Ici (1 : ℝ)) (fun y => g (x - y)) by
        funext y
        simp [aux_indicator, Set.indicator_apply]]
    exact hshift.indicator measurableSet_Ici
  unfold aux_realConvolution
  change (∫ y : ℝ, aux_indicator (Set.Ici 0) y * g (x-y)) +
      -(∫ y : ℝ, aux_indicator (Set.Ici 1) y * g (x-y)) =
        ∫ y : ℝ, aux_indicator (Set.Ico 0 1) y * g (x-y)
  rw [← sub_eq_add_neg, ← integral_sub h0 h1]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [aux_smoothing_indicator_Ico_eq_sub_Ici]
  ring

private noncomputable def aux_smoothing_R (b : windowBasedBumpFunctions) (k : ℤ) : ℝ → ℝ :=
  aux_realRescaled ((2 : ℝ) ^ k) (fun y ↦ b.phi0 y)

private noncomputable def aux_smoothing_G (b : windowBasedBumpFunctions) : ℝ → ℝ :=
  fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1))
    (fun y ↦ b.phi0 y) x - b.phi0 x

private theorem aux_smoothing_G_reproduces (b : windowBasedBumpFunctions) :
    aux_realConvolution
      (fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (fun y ↦ b.phi0 y) x - b.phi0 x)
      (aux_realRescaled (1 / 4 : ℝ) (fun y ↦ b.phi0 y)) =
      fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (fun y ↦ b.phi0 y) x - b.phi0 x := by
  let I : ℝ → ℝ := aux_indicator (Set.Ico 0 1)
  let K : ℝ → ℝ := fun x ↦ b.phi0 x
  let G : ℝ → ℝ := fun x ↦ aux_realConvolution I K x - K x
  let R : ℝ → ℝ := aux_realRescaled (1 / 4 : ℝ) K
  let gc : ℝ → ℂ := fun x ↦ (G x : ℂ)
  let rc : ℝ → ℂ := fun x ↦ (R x : ℂ)
  let H : ℝ → ℂ := gc ⋆[ContinuousLinearMap.mul ℂ ℂ] rc
  have hI : Integrable I := by simpa [I] using aux_smoothing_indicator_Ico_integrable
  have hK : Integrable K := by simpa [K] using b.phi0.integrable
  have hR : Integrable R := by
    dsimp [R, aux_realRescaled]
    convert ((b.phi0.integrable.comp_mul_left'
      (by norm_num : ((1 / 4 : ℝ)⁻¹) ≠ 0)).const_mul ((1 / 4 : ℝ)⁻¹)) using 1
    funext x
    simp [K, aux_realRescaled]
  have hIK : Integrable (aux_realConvolution I K) :=
    hI.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hK
  have hG : Integrable G := hIK.sub hK
  have hgc : Integrable gc := by
    change Integrable (fun x ↦ (G x : ℂ))
    exact hG.ofReal
  have hrc : Integrable rc := by
    change Integrable (fun x ↦ (R x : ℂ))
    exact hR.ofReal
  have hH : Integrable H :=
    hgc.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hrc
  have hKC : Continuous K := by simpa [K] using b.phi0.continuous
  have hKBound : BddAbove (Set.range fun x ↦ ‖K x‖) := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 b.phi0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa [K, Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ b.phi0 x
  have hGcCont : Continuous gc := by
    change Continuous (fun x ↦ ((aux_realConvolution I K x - K x : ℝ) : ℂ))
    apply Complex.ofRealCLM.continuous.comp
    exact (BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℝ ℝ) hKBound hI hKC).sub hKC
  have hRC : Continuous R := by
    apply aux_char_realRescaled_continuous
    exact hKC
  have hrcBound : BddAbove (Set.range fun x ↦ ‖rc x‖) := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 b.phi0 * (1 / 4 : ℝ)⁻¹, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa [rc, R, K, Complex.norm_real, Real.norm_eq_abs] using
      aux_bumpBasic_rescale_abs_le (fun y ↦ b.phi0 y)
        (SchwartzMap.seminorm ℝ 0 0 b.phi0)
        (fun y ↦ by simpa [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ b.phi0 y)
        (1 / 4 : ℝ) x (by norm_num)
  have hHC : Continuous H := by
    refine BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) hrcBound hgc ?_
    exact Complex.ofRealCLM.continuous.comp hRC
  have hwin : cnWindow C_uniPair N_uniPair b.phi0 := b.universalPair.1
  have hFG_formula (xi : ℝ) :
      FourierTransform.fourier gc xi =
        (FourierTransform.fourier (fun x ↦ (I x : ℂ)) xi - 1) *
          FourierTransform.fourier (fun x ↦ (K x : ℂ)) xi := by
    calc
      FourierTransform.fourier gc xi =
          FourierTransform.fourier (fun x ↦ (aux_realConvolution I K x : ℂ)) xi -
            FourierTransform.fourier (fun x ↦ (K x : ℂ)) xi := by
        rw [show gc = fun x ↦
          ((aux_realConvolution I K x - K x : ℝ) : ℂ) by rfl,
          aux_bumpBasic_fourier_sub_of_integrable _ _ hIK hK]
      _ = FourierTransform.fourier (fun x ↦ (I x : ℂ)) xi *
            FourierTransform.fourier (fun x ↦ (K x : ℂ)) xi -
            FourierTransform.fourier (fun x ↦ (K x : ℂ)) xi := by
        rw [show (fun x ↦ (aux_realConvolution I K x : ℂ)) =
          ((fun y ↦ (I y : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
            (fun y ↦ (K y : ℂ))) by
            funext x
            exact aux_smoothing_realConvolution_complex I K x]
        exact congrArg (fun z : ℂ ↦ z - FourierTransform.fourier (fun x ↦ (K x : ℂ)) xi)
          (Real.fourier_mul_convolution_eq (R := ℂ)
            (f₁ := fun x ↦ (I x : ℂ)) (f₂ := fun x ↦ (K x : ℂ))
            hI.ofReal hK.ofReal xi)
      _ = _ := by ring
  have hFGsupp : Function.support (FourierTransform.fourier gc) ⊆
      Set.Icc (-1 : ℝ) 1 := by
    intro xi hxi
    by_contra hx
    apply (Function.mem_support.mp hxi)
    rw [hFG_formula]
    have hzero : FourierTransform.fourier (fun x ↦ (K x : ℂ)) xi = 0 := by
      by_contra hnonzero
      apply hx
      simpa [K] using hwin.2.2.1 (Function.mem_support.mpr hnonzero)
    rw [hzero]
    ring
  have hFGcont : Continuous (FourierTransform.fourier gc) := by
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hgc
  have hFGcompact : HasCompactSupport (FourierTransform.fourier gc) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact hFGsupp
  have hFGint : Integrable (FourierTransform.fourier gc) :=
    hFGcont.integrable_of_hasCompactSupport hFGcompact
  have hFH_eq : FourierTransform.fourier H = FourierTransform.fourier gc := by
    funext xi
    rw [show H = gc ⋆[ContinuousLinearMap.mul ℂ ℂ] rc by rfl,
      Real.fourier_mul_convolution_eq hgc hrc,
      show rc = fun x ↦ (aux_realRescaled (1 / 4 : ℝ) K x : ℂ) by rfl,
      aux_bumpBasic_rescale_fourier (1 / 4 : ℝ) (by norm_num)]
    by_cases hzero : FourierTransform.fourier gc xi = 0
    · rw [hzero]
      ring
    have hmem := hFGsupp (Function.mem_support.mpr hzero)
    have hone := hwin.2.2.2.1 ((1 / 4 : ℝ) * xi)
      (by constructor <;> nlinarith [hmem.1, hmem.2])
    change FourierTransform.fourier gc xi *
        FourierTransform.fourier (fun x ↦ (K x : ℂ)) ((1 / 4 : ℝ) * xi) = _
    simpa [K] using congrArg (fun z : ℂ ↦ FourierTransform.fourier gc xi * z) hone
  have hFHint : Integrable (FourierTransform.fourier H) := by
    rw [hFH_eq]
    exact hFGint
  change aux_realConvolution G R = G
  funext x
  apply Complex.ofReal_injective
  rw [aux_smoothing_realConvolution_complex]
  change H x = gc x
  calc
    H x = FourierTransformInv.fourierInv (FourierTransform.fourier H) x :=
      congrFun (hHC.fourierInv_fourier_eq hH hFHint).symm x
    _ = FourierTransformInv.fourierInv (FourierTransform.fourier gc) x := by rw [hFH_eq]
    _ = gc x := congrFun (hGcCont.fourierInv_fourier_eq hgc hFGint) x

private theorem aux_smoothing_rescaled_theta_integrable
    (b : windowBasedBumpFunctions) (ell : ℤ) :
    Integrable (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b)) := by
  rw [show windowBasedBumpFunctions.theta b =
      aux_thetaBasic (fun y ↦ b.phi0 y) by rfl,
    aux_realRescaled_thetaBasic]
  exact (aux_bumpBasic_rescale_integrable b.phi0 ((2 : ℝ) ^ ell)
    (zpow_pos (by norm_num) _)).sub
    (aux_bumpBasic_rescale_integrable b.phi0 ((2 : ℝ) ^ (ell + 1))
      (zpow_pos (by norm_num) _))

private theorem aux_smoothing_rescaled_theta_continuous
    (b : windowBasedBumpFunctions) (ell : ℤ) :
    Continuous (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b)) := by
  rw [show windowBasedBumpFunctions.theta b =
      aux_thetaBasic (fun y ↦ b.phi0 y) by rfl,
    aux_realRescaled_thetaBasic]
  exact (aux_char_realRescaled_continuous _ _ b.phi0.continuous).sub
    (aux_char_realRescaled_continuous _ _ b.phi0.continuous)

private theorem aux_smoothing_rescaled_phi_norm_le
    (b : windowBasedBumpFunctions) (t x : ℝ) :
    ‖aux_realRescaled t (fun y ↦ b.phi0 y) x‖ ≤
      ‖t⁻¹‖ * SchwartzMap.seminorm ℝ 0 0 b.phi0 := by
  unfold aux_realRescaled
  rw [norm_mul]
  gcongr
  simpa [Real.norm_eq_abs] using
    SchwartzMap.norm_le_seminorm ℝ b.phi0 (t⁻¹ * x)

private theorem aux_smoothing_rescaled_theta_norm_le
    (b : windowBasedBumpFunctions) (ell : ℤ) (x : ℝ) :
    ‖aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b) x‖ ≤
      ‖((2 : ℝ) ^ ell)⁻¹‖ * SchwartzMap.seminorm ℝ 0 0 b.phi0 +
        ‖((2 : ℝ) ^ (ell + 1))⁻¹‖ * SchwartzMap.seminorm ℝ 0 0 b.phi0 := by
  rw [show windowBasedBumpFunctions.theta b =
      aux_thetaBasic (fun y ↦ b.phi0 y) by rfl,
    aux_realRescaled_thetaBasic]
  exact (norm_sub_le _ _).trans <| add_le_add
    (aux_smoothing_rescaled_phi_norm_le b ((2 : ℝ) ^ ell) x)
    (aux_smoothing_rescaled_phi_norm_le b ((2 : ℝ) ^ (ell + 1)) x)

private theorem aux_smoothing_G_integrable (b : windowBasedBumpFunctions) :
    Integrable (aux_smoothing_G b) := by
  have hconv : Integrable (aux_realConvolution (aux_indicator (Set.Ico 0 1))
      (fun y ↦ b.phi0 y)) := by
    change Integrable ((aux_indicator (Set.Ico (0 : ℝ) 1) ⋆[
      ContinuousLinearMap.mul ℝ ℝ, volume] fun y ↦ b.phi0 y) : ℝ → ℝ)
    exact aux_smoothing_indicator_Ico_integrable.integrable_convolution
      (ContinuousLinearMap.mul ℝ ℝ) b.phi0.integrable
  exact hconv.sub b.phi0.integrable

private theorem aux_smoothing_G_mul_rescaled_theta_integrable
    (b : windowBasedBumpFunctions) (ell : ℤ) (x : ℝ) :
    Integrable (fun y : ℝ => aux_smoothing_G b y *
      aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b) (x - y)) := by
  apply (aux_smoothing_G_integrable b).mul_bdd
  · exact ((aux_smoothing_rescaled_theta_continuous b ell).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [] with y
    exact aux_smoothing_rescaled_theta_norm_le b ell (x - y)

private theorem aux_smoothing_phiZero_partial_sum (b : windowBasedBumpFunctions) (N : ℕ) :
    aux_integerIntervalSum (windowBasedBumpFunctions.phiZero b) (-2) (N : ℤ) =
      aux_realConvolution (aux_smoothing_G b)
        (fun x ↦ aux_smoothing_R b (-2) x - aux_smoothing_R b ((N : ℤ) + 1) x) := by
  have hsum : aux_integerIntervalSum
      (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell)
        (windowBasedBumpFunctions.theta b)) (-2) (N : ℤ) =
      fun x ↦ aux_smoothing_R b (-2) x - aux_smoothing_R b ((N : ℤ) + 1) x := by
    have hraw := aux_bumpBasic_partial_sum_eq (fun y ↦ b.phi0 y) (-2 : ℤ) (N + 2)
    have hind : (-2 : ℤ) + ((N + 2 : ℕ) : ℤ) = (N : ℤ) := by omega
    rw [hind] at hraw
    rw [show windowBasedBumpFunctions.theta b = aux_thetaBasic (fun y ↦ b.phi0 y) by rfl]
    simpa [aux_smoothing_R] using hraw
  change aux_integerIntervalSum
    (fun ell ↦ aux_realConvolution (aux_smoothing_G b)
      (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b))) (-2) (N : ℤ) = _
  rw [show aux_integerIntervalSum
      (fun ell ↦ aux_realConvolution (aux_smoothing_G b)
        (aux_realRescaled ((2 : ℝ) ^ ell) (windowBasedBumpFunctions.theta b))) (-2) (N : ℤ) =
      aux_realConvolution (aux_smoothing_G b) (aux_integerIntervalSum
        (fun ell ↦ aux_realRescaled ((2 : ℝ) ^ ell)
          (windowBasedBumpFunctions.theta b)) (-2) (N : ℤ)) by
        funext x
        unfold aux_integerIntervalSum aux_realConvolution
        change (∑ j ∈ Finset.Icc (-2 : ℤ) (N : ℤ),
          ∫ y : ℝ, aux_smoothing_G b y * aux_realRescaled ((2 : ℝ) ^ j)
            (windowBasedBumpFunctions.theta b) (x - y)) =
          ∫ y : ℝ, aux_smoothing_G b y * ∑ j ∈ Finset.Icc (-2 : ℤ) (N : ℤ),
            aux_realRescaled ((2 : ℝ) ^ j) (windowBasedBumpFunctions.theta b) (x - y)
        rw [show (fun y : ℝ => aux_smoothing_G b y * ∑ j ∈ Finset.Icc (-2 : ℤ) (N : ℤ),
            aux_realRescaled ((2 : ℝ) ^ j) (windowBasedBumpFunctions.theta b) (x - y)) =
            fun y : ℝ => ∑ j ∈ Finset.Icc (-2 : ℤ) (N : ℤ), aux_smoothing_G b y *
              aux_realRescaled ((2 : ℝ) ^ j) (windowBasedBumpFunctions.theta b) (x - y) by
              funext y
              rw [Finset.mul_sum]]
        rw [MeasureTheory.integral_finset_sum]
        intro ell _
        exact aux_smoothing_G_mul_rescaled_theta_integrable b ell x]
  rw [hsum]

private theorem aux_smoothing_G_mul_R_integrable
    (b : windowBasedBumpFunctions) (ell : ℤ) (x : ℝ) :
    Integrable (fun y : ℝ => aux_smoothing_G b y * aux_smoothing_R b ell (x - y)) := by
  apply (aux_smoothing_G_integrable b).mul_bdd
  · dsimp [aux_smoothing_R]
    exact ((aux_char_realRescaled_continuous _ _ b.phi0.continuous).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [] with y
    dsimp [aux_smoothing_R]
    exact aux_smoothing_rescaled_phi_norm_le b ((2 : ℝ) ^ ell) (x - y)

private theorem aux_smoothing_G_convolution_sub_R
    (b : windowBasedBumpFunctions) (k l : ℤ) :
    aux_realConvolution (aux_smoothing_G b)
      (fun x ↦ aux_smoothing_R b k x - aux_smoothing_R b l x) =
      fun x ↦ aux_realConvolution (aux_smoothing_G b) (aux_smoothing_R b k) x -
        aux_realConvolution (aux_smoothing_G b) (aux_smoothing_R b l) x := by
  funext x
  unfold aux_realConvolution
  rw [show (fun y : ℝ => aux_smoothing_G b y *
      (aux_smoothing_R b k (x - y) - aux_smoothing_R b l (x - y))) =
      fun y ↦ aux_smoothing_G b y * aux_smoothing_R b k (x - y) -
        aux_smoothing_G b y * aux_smoothing_R b l (x - y) by
        funext y
        ring,
    integral_sub (aux_smoothing_G_mul_R_integrable b k x)
      (aux_smoothing_G_mul_R_integrable b l x)]

private theorem aux_smoothing_Ico_mul_R_integrable
    (b : windowBasedBumpFunctions) (ell : ℤ) (x : ℝ) :
    Integrable (fun y : ℝ => aux_indicator (Set.Ico 0 1) y *
      aux_smoothing_R b ell (x - y)) := by
  have hcont : Continuous (fun y : ℝ => aux_smoothing_R b ell (x - y)) := by
    dsimp [aux_smoothing_R]
    exact (aux_char_realRescaled_continuous _ _ b.phi0.continuous).comp
      (continuous_const.sub continuous_id)
  rw [show (fun y : ℝ => aux_indicator (Set.Ico 0 1) y *
      aux_smoothing_R b ell (x - y)) =
      Set.indicator (Set.Ico (0 : ℝ) 1) (fun y => aux_smoothing_R b ell (x - y)) by
        funext y
        simp [aux_indicator, Set.indicator_apply],
    MeasureTheory.integrable_indicator_iff measurableSet_Ico]
  exact (hcont.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set Ico_subset_Icc_self

private theorem aux_smoothing_Ico_convolution_sub_R
    (b : windowBasedBumpFunctions) (k l : ℤ) :
    aux_realConvolution (aux_indicator (Set.Ico 0 1))
      (fun x ↦ aux_smoothing_R b k x - aux_smoothing_R b l x) =
      fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1)) (aux_smoothing_R b k) x -
        aux_realConvolution (aux_indicator (Set.Ico 0 1)) (aux_smoothing_R b l) x := by
  funext x
  unfold aux_realConvolution
  rw [show (fun y : ℝ => aux_indicator (Set.Ico 0 1) y *
      (aux_smoothing_R b k (x - y) - aux_smoothing_R b l (x - y))) =
      fun y ↦ aux_indicator (Set.Ico 0 1) y * aux_smoothing_R b k (x - y) -
        aux_indicator (Set.Ico 0 1) y * aux_smoothing_R b l (x - y) by
        funext y
        ring,
    integral_sub (aux_smoothing_Ico_mul_R_integrable b k x)
      (aux_smoothing_Ico_mul_R_integrable b l x)]

private theorem aux_smoothing_G_RminusTwo_reproduces (b : windowBasedBumpFunctions) :
    aux_realConvolution (aux_smoothing_G b) (aux_smoothing_R b (-2)) = aux_smoothing_G b := by
  have hscale : aux_smoothing_R b (-2) =
      aux_realRescaled (1 / 4 : ℝ) (fun y ↦ b.phi0 y) := by
    funext x
    norm_num [aux_smoothing_R, aux_realRescaled]
  rw [hscale]
  change aux_realConvolution
      (fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (fun y ↦ b.phi0 y) x - b.phi0 x)
      (aux_realRescaled (1 / 4 : ℝ) (fun y ↦ b.phi0 y)) =
      fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (fun y ↦ b.phi0 y) x - b.phi0 x
  exact aux_smoothing_G_reproduces b

private theorem aux_smoothing_one_two_partial_sum (b : windowBasedBumpFunctions)
    (N : ℕ) (hN : 1 ≤ N) :
    aux_integerIntervalSum
      (fun k ↦ fun y ↦ windowBasedBumpFunctions.phiOne b k y +
        windowBasedBumpFunctions.phiTwo b k y)
      (-(N : ℤ)) (-1) =
      aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (fun x ↦ aux_smoothing_R b (-(N : ℤ)) x - aux_smoothing_R b 0 x) := by
  have hterm (k : ℤ) :
      (fun y ↦ windowBasedBumpFunctions.phiOne b k y +
        windowBasedBumpFunctions.phiTwo b k y) =
      aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (aux_realRescaled ((2 : ℝ) ^ k) (windowBasedBumpFunctions.theta b)) := by
    unfold windowBasedBumpFunctions.phiOne windowBasedBumpFunctions.phiTwo
    exact aux_smoothing_convolution_Ici_sub_eq_Ico _
      (aux_smoothing_rescaled_theta_integrable b k)
  rw [show (fun k ↦ fun y ↦ windowBasedBumpFunctions.phiOne b k y +
      windowBasedBumpFunctions.phiTwo b k y) =
      fun k ↦ aux_realConvolution (aux_indicator (Set.Icc 0 1))
        (aux_realRescaled ((2 : ℝ) ^ k) (windowBasedBumpFunctions.theta b)) by
        funext k
        rw [hterm k, aux_smoothing_convolution_Ico_eq_Icc]]
  rw [aux_char_convolution_integer_sum_eq]
  have hsum := aux_bumpBasic_partial_sum_eq (fun y ↦ b.phi0 y)
    (-(N : ℤ)) (N - 1)
  have hind : (-(N : ℤ) + ((N - 1 : ℕ) : ℤ)) = -1 := by omega
  rw [hind] at hsum
  have hzeroScale : aux_realRescaled ((2 : ℝ) ^ ((-1 : ℤ) + 1))
      (fun y ↦ b.phi0 y) = fun y ↦ b.phi0 y := by
    funext y
    simp [aux_realRescaled]
  rw [show windowBasedBumpFunctions.theta b =
      aux_thetaBasic (fun y ↦ b.phi0 y) by rfl,
    hsum, hzeroScale]
  rw [aux_smoothing_convolution_Ico_eq_Icc]
  simp only [aux_smoothing_R]
  have hzero : aux_realRescaled ((2 : ℝ) ^ (0 : ℤ))
      (fun y ↦ b.phi0 y) = fun y ↦ b.phi0 y := by
    funext y
    simp [aux_realRescaled]
  rw [hzero]

private theorem aux_smoothingPartialSum_finite_algebra
    (b : windowBasedBumpFunctions) (N : ℕ) (hN : 1 ≤ N) :
    windowBasedBumpFunctions.smoothingPartialSum b N =
      fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (aux_smoothing_R b (-(N : ℤ))) x -
        aux_realConvolution (aux_smoothing_G b) (aux_smoothing_R b ((N : ℤ) + 1)) x := by
  unfold windowBasedBumpFunctions.smoothingPartialSum
  rw [aux_smoothing_phiZero_partial_sum b N,
    aux_smoothing_one_two_partial_sum b N hN,
    aux_smoothing_G_convolution_sub_R b (-2) ((N : ℤ) + 1),
    aux_smoothing_Ico_convolution_sub_R b (-(N : ℤ)) 0,
    aux_smoothing_G_RminusTwo_reproduces]
  have hR0 : aux_smoothing_R b 0 = fun y ↦ b.phi0 y := by
    funext x
    simp [aux_smoothing_R, aux_realRescaled]
  rw [hR0]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  change b.phi0 x +
      ((aux_smoothing_G b x - aux_realConvolution (aux_smoothing_G b)
        (aux_smoothing_R b ((N : ℤ) + 1)) x)) +
      (aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (aux_smoothing_R b (-(N : ℤ))) x -
        aux_realConvolution (aux_indicator (Set.Ico 0 1)) (fun y ↦ b.phi0 y) x) = _
  change b.phi0 x +
      ((aux_realConvolution (aux_indicator (Set.Ico 0 1)) (fun y ↦ b.phi0 y) x - b.phi0 x) -
        aux_realConvolution (aux_smoothing_G b)
          (aux_smoothing_R b ((N : ℤ) + 1)) x) +
      (aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (aux_smoothing_R b (-(N : ℤ))) x -
        aux_realConvolution (aux_indicator (Set.Ico 0 1)) (fun y ↦ b.phi0 y) x) = _
  ring

/-! ### Decay of the high-scale remainder -/

private theorem aux_smoothing_interp_l1_bound_linf_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (e : ι → ℝ → ℝ) (A : ℝ≥0∞)
    (hAfin : A ≠ ∞)
    (hMeas : ∀ᶠ i in l, AEStronglyMeasurable (e i))
    (hOne : ∀ᶠ i in l, eLpNorm (e i) 1 volume ≤ A)
    (hTop : Tendsto (fun i => eLpNorm (e i) ∞ volume) l (nhds 0)) :
    Tendsto (fun i => eLpNorm (e i) 2 volume) l (nhds 0) := by
  have hTopHalf : Tendsto (fun i => (eLpNorm (e i) ∞ volume) ^ ((2 : ℝ)⁻¹))
      l (nhds 0) := by
    simpa using hTop.ennrpow_const ((2 : ℝ)⁻¹)
  have hAfinite : A ^ ((2 : ℝ)⁻¹) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) hAfin
  have hRight : Tendsto (fun i => A ^ ((2 : ℝ)⁻¹) *
      (eLpNorm (e i) ∞ volume) ^ ((2 : ℝ)⁻¹)) l (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hTopHalf (Or.inr hAfinite)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0∞)) l (nhds 0)) hRight
  · filter_upwards [] with i
    exact bot_le
  · filter_upwards [hMeas, hOne] with i hiMeas hiOne
    have h := Codex.aux_eLpNorm_le_of_l1_linf_bounds hiMeas (q := (2 : ℝ)) (by norm_num)
      hiOne (le_refl _)
    have hhalf : 1 - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
    rw [hhalf] at h
    have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
    rw [htwo] at h
    exact h

private theorem aux_smoothing_realRescaled_abs_bound (psi : ℝ → ℝ) (C t x : ℝ)
    (hC : ∀ y, |psi y| ≤ C) (ht : 0 < t) :
    ‖aux_realRescaled t psi x‖ ≤ C * t⁻¹ := by
  unfold aux_realRescaled
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr ht)]
  calc
    t⁻¹ * |psi (t⁻¹ * x)| ≤ t⁻¹ * C :=
      mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr ht.le)
    _ = C * t⁻¹ := mul_comm _ _

private theorem aux_smoothing_realRescaled_integrable (psi : ℝ → ℝ) (t : ℝ)
    (hpsi : Integrable psi) (ht : 0 < t) :
    Integrable (aux_realRescaled t psi) := by
  unfold aux_realRescaled
  convert (hpsi.comp_mul_left' (inv_ne_zero ht.ne')).const_mul t⁻¹ using 1

private theorem aux_smoothing_realRescaled_integral_norm (psi : ℝ → ℝ) (t : ℝ)
    (ht : 0 < t) :
    (∫ x : ℝ, ‖aux_realRescaled t psi x‖) = ∫ x : ℝ, ‖psi x‖ := by
  unfold aux_realRescaled
  rw [show (fun x : ℝ => ‖t⁻¹ * psi (t⁻¹ * x)‖) =
      fun x => t⁻¹ * ‖psi (t⁻¹ * x)‖ by
        funext x
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)],
    integral_const_mul,
    Measure.integral_comp_inv_mul_left (fun x : ℝ => ‖psi x‖) t,
    abs_of_pos ht, smul_eq_mul]
  field_simp

private theorem aux_smoothing_raw_convolution_l1_bound (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, ‖aux_realConvolution f g x‖) ≤
      (∫ x : ℝ, ‖f x‖) * (∫ x : ℝ, ‖g x‖) := by
  have hconv : Integrable (aux_realConvolution f g) :=
    hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hg
  have hD : Integrable (fun z : ℝ × ℝ => f z.2 * g (z.1 - z.2))
      ((volume : Measure ℝ).prod volume) :=
    hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
  have hright : Integrable (fun x : ℝ => ∫ y : ℝ, ‖f y * g (x - y)‖) := by
    simpa only [Measure.volume_eq_prod] using hD.integral_norm_prod_left
  calc
    (∫ x : ℝ, ‖aux_realConvolution f g x‖) ≤
        ∫ x : ℝ, ∫ y : ℝ, ‖f y * g (x - y)‖ := by
      apply integral_mono hconv.norm hright
      intro x
      exact norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, ∫ x : ℝ, ‖f y * g (x - y)‖ := by
      simpa only [Measure.volume_eq_prod] using (integral_integral_swap hD.norm)
    _ = ∫ y : ℝ, ‖f y‖ * (∫ x : ℝ, ‖g x‖) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show (fun x : ℝ => ‖f y * g (x - y)‖) =
          fun x => ‖f y‖ * ‖g (x - y)‖ by
            funext x
            rw [norm_mul], integral_const_mul,
          integral_sub_right_eq_self (fun x : ℝ => ‖g x‖) y]
    _ = (∫ y : ℝ, ‖f y‖) * (∫ x : ℝ, ‖g x‖) := by
      rw [integral_mul_const]

private theorem aux_smoothing_raw_convolution_linf_scaled_bound (f psi : ℝ → ℝ)
    (hf : Integrable f) (hpsim : Measurable psi) (C t x : ℝ)
    (hC : ∀ y, |psi y| ≤ C) (ht : 0 < t) :
    ‖aux_realConvolution f (aux_realRescaled t psi) x‖ ≤
      (C * t⁻¹) * ∫ y : ℝ, ‖f y‖ := by
  have hmeas : AEStronglyMeasurable (fun y : ℝ => aux_realRescaled t psi (x - y)) := by
    unfold aux_realRescaled
    exact (measurable_const.mul
      (hpsim.comp (measurable_const.mul (measurable_const.sub measurable_id)))).aestronglyMeasurable
  have hbound : ∀ᵐ y : ℝ, ‖aux_realRescaled t psi (x - y)‖ ≤ C * t⁻¹ := by
    filter_upwards [] with y
    exact aux_smoothing_realRescaled_abs_bound psi C t (x - y) hC ht
  have hint : Integrable (fun y : ℝ => f y * aux_realRescaled t psi (x - y)) := by
    convert hf.bdd_mul hmeas hbound using 1
    funext y
    ring
  have hmajor : Integrable (fun y : ℝ => ‖f y‖ * (C * t⁻¹)) :=
    hf.norm.mul_const _
  calc
    ‖aux_realConvolution f (aux_realRescaled t psi) x‖ ≤
        ∫ y : ℝ, ‖f y * aux_realRescaled t psi (x - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℝ, ‖f y‖ * (C * t⁻¹) := by
      apply integral_mono hint.norm hmajor
      intro y
      change ‖f y * aux_realRescaled t psi (x - y)‖ ≤ ‖f y‖ * (C * t⁻¹)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (aux_smoothing_realRescaled_abs_bound psi C t (x - y) hC ht) (norm_nonneg _)
    _ = (C * t⁻¹) * ∫ y : ℝ, ‖f y‖ := by
      rw [integral_mul_const]
      ring

private theorem aux_smoothing_dyadic_zpow_inv_tendsto_zero :
    Tendsto (fun N : ℕ => ((2 : ℝ) ^ (N : ℤ))⁻¹) atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  convert hpow using 1
  funext N
  rw [zpow_natCast, ← inv_pow]
  norm_num

private theorem aux_smoothing_scaled_convolution_tendsto_L2 (f psi : ℝ → ℝ)
    (hf : Integrable f) (hpsi : Integrable psi) (hpsim : Measurable psi)
    (C : ℝ) (hC : ∀ y, |psi y| ≤ C) :
    Tendsto (fun N : ℕ => eLpNorm
      (aux_realConvolution f (aux_realRescaled ((2 : ℝ) ^ (N : ℤ)) psi))
      2 volume) atTop (nhds 0) := by
  let t : ℕ → ℝ := fun N => (2 : ℝ) ^ (N : ℤ)
  let e : ℕ → ℝ → ℝ := fun N => aux_realConvolution f (aux_realRescaled (t N) psi)
  let A : ℝ≥0∞ := ENNReal.ofReal ((∫ x : ℝ, ‖f x‖) * (∫ x : ℝ, ‖psi x‖))
  have ht (N : ℕ) : 0 < t N := by
    dsimp [t]
    positivity
  have hInt (N : ℕ) : Integrable (e N) := by
    dsimp [e]
    exact hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (aux_smoothing_realRescaled_integrable psi (t N) hpsi (ht N))
  have hOne : ∀ᶠ N : ℕ in atTop, eLpNorm (e N) 1 volume ≤ A := by
    filter_upwards [] with N
    apply Codex.aux_eLpNorm_one_le_of_integral_norm_le (hInt N)
    dsimp [e, A]
    calc
      (∫ x : ℝ, ‖aux_realConvolution f (aux_realRescaled (t N) psi) x‖) ≤
          (∫ x : ℝ, ‖f x‖) * (∫ x : ℝ, ‖aux_realRescaled (t N) psi x‖) :=
        aux_smoothing_raw_convolution_l1_bound f (aux_realRescaled (t N) psi) hf
          (aux_smoothing_realRescaled_integrable psi (t N) hpsi (ht N))
      _ = (∫ x : ℝ, ‖f x‖) * (∫ x : ℝ, ‖psi x‖) := by
        rw [aux_smoothing_realRescaled_integral_norm psi (t N) (ht N)]
  have hinv : Tendsto (fun N : ℕ => (t N)⁻¹) atTop (nhds 0) := by
    simpa [t] using aux_smoothing_dyadic_zpow_inv_tendsto_zero
  have hD : Tendsto (fun N : ℕ => (C * (t N)⁻¹) * ∫ x : ℝ, ‖f x‖)
      atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds.mul hinv).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ x : ℝ, ‖f x‖) atTop
        (nhds (∫ x : ℝ, ‖f x‖))))
  have hTop : Tendsto (fun N : ℕ => eLpNorm (e N) ∞ volume) atTop (nhds 0) := by
    have hD' : Tendsto (fun N : ℕ => ENNReal.ofReal
        ((C * (t N)⁻¹) * ∫ x : ℝ, ‖f x‖)) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal hD
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0)) hD'
    · filter_upwards [] with N
      exact bot_le
    · filter_upwards [] with N
      apply Codex.aux_eLpNorm_top_le_of_bound
      filter_upwards [] with x
      dsimp [e]
      exact aux_smoothing_raw_convolution_linf_scaled_bound f psi hf hpsim C (t N) x hC (ht N)
  have hMeas : ∀ᶠ N : ℕ in atTop, AEStronglyMeasurable (e N) := by
    filter_upwards [] with N
    exact (hInt N).aestronglyMeasurable
  have hAfin : A ≠ ∞ := by simp [A]
  exact aux_smoothing_interp_l1_bound_linf_tendsto e A hAfin hMeas hOne hTop

private theorem aux_smoothing_scaled_convolution_tendsto_L2_succ (f psi : ℝ → ℝ)
    (hf : Integrable f) (hpsi : Integrable psi) (hpsim : Measurable psi)
    (C : ℝ) (hC : ∀ y, |psi y| ≤ C) :
    Tendsto (fun N : ℕ => eLpNorm
      (aux_realConvolution f (aux_realRescaled ((2 : ℝ) ^ ((N + 1 : ℕ) : ℤ)) psi))
      2 volume) atTop (nhds 0) := by
  have hbase := aux_smoothing_scaled_convolution_tendsto_L2 f psi hf hpsi hpsim C hC
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def] using hshift

private theorem aux_smoothing_G_high_scale_tail (b : windowBasedBumpFunctions) :
    Tendsto (fun N : ℕ => eLpNorm
      (aux_realConvolution (aux_smoothing_G b)
        (aux_realRescaled ((2 : ℝ) ^ ((N + 1 : ℕ) : ℤ))
          (fun y ↦ b.phi0 y))) 2 volume) atTop (nhds 0) := by
  refine aux_smoothing_scaled_convolution_tendsto_L2_succ _ _
    (aux_smoothing_G_integrable b) b.phi0.integrable b.phi0.continuous.measurable
    (SchwartzMap.seminorm ℝ 0 0 b.phi0) ?_
  intro y
  simpa [Real.norm_eq_abs] using SchwartzMap.norm_le_seminorm ℝ b.phi0 y

private theorem aux_smoothing_indicator_Ico_data :
    Integrable (aux_indicator (Set.Ico (0 : ℝ) 1)) ∧
    Measurable (aux_indicator (Set.Ico (0 : ℝ) 1)) ∧
    (∀ x : ℝ, |aux_indicator (Set.Ico (0 : ℝ) 1) x| ≤ 1) := by
  refine ⟨aux_smoothing_indicator_Ico_integrable, ?_, ?_⟩
  · exact measurable_const.indicator measurableSet_Ico
  · intro x
    by_cases hx : x ∈ Set.Ico (0 : ℝ) 1 <;> simp [aux_indicator, hx]

private theorem aux_smoothing_Ico_approximate_identity (b : windowBasedBumpFunctions) :
    Tendsto (fun N : ℕ => eLpNorm (fun x : ℝ =>
      aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (aux_smoothing_R b (-(N : ℤ))) x - aux_indicator (Set.Icc 0 1) x) 2 volume)
      atTop (nhds 0) := by
  rcases aux_smoothing_indicator_Ico_data with ⟨hI, hImeas, hIbound⟩
  have hphi : Integrable (fun x : ℝ ↦ b.phi0 x) := b.phi0.integrable
  have hphiMeas : Measurable (fun x : ℝ ↦ b.phi0 x) := b.phi0.continuous.measurable
  have hmass : ∫ x : ℝ, b.phi0 x = 1 := aux_phi0_integral_one b
  have htrans := aux_char_translation_integral_norm_tendsto hI
  have happrox := aux_raw_approximate_identity_L2
    (aux_indicator (Set.Ico 0 1)) (fun x : ℝ ↦ b.phi0 x)
    hI hImeas hphi hphiMeas 1 hIbound hmass htrans
  have hscaled := happrox.comp aux_zpow_neg_nat_tendsto_zero_within
  apply Tendsto.congr' ?_ hscaled
  filter_upwards [] with N
  apply eLpNorm_congr_ae
  filter_upwards [aux_smoothing_indicator_Ico_ae_eq_Icc] with x hx
  simp only [aux_smoothing_R]
  rw [hx]

/--
\begin{lemma}[Smoothing decomposition]\label{lem:smoothingdecomp}
The identity
\[\mathbf 1_{[0,1]}=\phi_0+\sum_{k=-2}^\infty\varphi_{0,k}+
\sum_{k=-\infty}^{-1}\varphi_{1,k}+
\sum_{k=-\infty}^{-1}\varphi_{2,k}\]
holds in the $L^2$ sense.
\end{lemma}
-/
theorem smoothingDecomp (b : windowBasedBumpFunctions) :
    aux_convergesInL2 (windowBasedBumpFunctions.smoothingPartialSum b)
      (aux_indicator (Set.Icc 0 1)) := by
  have hmain := aux_smoothing_Ico_approximate_identity b
  have htail := aux_smoothing_G_high_scale_tail b
  have htail' : Tendsto (fun N : ℕ => eLpNorm
      (aux_realConvolution (aux_smoothing_G b)
        (aux_smoothing_R b ((N : ℤ) + 1))) 2 volume) atTop (nhds 0) := by
    apply Tendsto.congr' ?_ htail
    filter_upwards [] with N
    congr 2
  have hsum : Tendsto (fun N : ℕ =>
      eLpNorm (fun x : ℝ => aux_realConvolution (aux_indicator (Set.Ico 0 1))
        (aux_smoothing_R b (-(N : ℤ))) x - aux_indicator (Set.Icc 0 1) x) 2 volume +
      eLpNorm (aux_realConvolution (aux_smoothing_G b)
        (aux_smoothing_R b ((N : ℤ) + 1))) 2 volume) atTop (nhds 0) := by
    simpa using hmain.add htail'
  unfold aux_convergesInL2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))
    hsum
  · filter_upwards [] with N
    exact bot_le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    rw [aux_smoothingPartialSum_finite_algebra b N hN]
    let A : ℝ → ℝ := fun x ↦ aux_realConvolution (aux_indicator (Set.Ico 0 1))
      (aux_smoothing_R b (-(N : ℤ))) x
    let B : ℝ → ℝ := fun x ↦ aux_realConvolution (aux_smoothing_G b)
      (aux_smoothing_R b ((N : ℤ) + 1)) x
    have hA : Integrable A := by
      dsimp [A, aux_smoothing_R]
      exact aux_smoothing_indicator_Ico_integrable.integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ)
        (aux_smoothing_realRescaled_integrable _ _ b.phi0.integrable
          (zpow_pos (by norm_num) _))
    have hB : Integrable B := by
      dsimp [B, aux_smoothing_R]
      exact (aux_smoothing_G_integrable b).integrable_convolution
        (ContinuousLinearMap.mul ℝ ℝ)
        (aux_smoothing_realRescaled_integrable _ _ b.phi0.integrable
          (zpow_pos (by norm_num) _))
    have hIcc : Integrable (aux_indicator (Set.Icc (0 : ℝ) 1)) :=
      aux_indicator_Icc_data.1
    have hrearrange : (fun x ↦ A x - B x - aux_indicator (Set.Icc 0 1) x) =
        fun x ↦ (A x - aux_indicator (Set.Icc 0 1) x) - B x := by
      funext x
      ring
    rw [show (fun x ↦
      (fun x ↦ A x - B x) x - aux_indicator (Set.Icc 0 1) x) =
        fun x ↦ A x - B x - aux_indicator (Set.Icc 0 1) x by rfl,
      hrearrange]
    exact eLpNorm_sub_le (hA.sub hIcc).aestronglyMeasurable hB.aestronglyMeasurable (by norm_num)

/--
\begin{lemma}\label{lem:theta_decay}
For $1\le N\le3$ and every $u\in\mathbb R$,
$|\theta(u)|\le C_{\ref{lem:theta_decay},N}\langle u\rangle^N$, where
$C_{\ref{lem:theta_decay},N}=2^{2N+2}C_{\ref{def:unipair}}$.
\end{lemma}
-/
theorem thetaDecay (b : windowBasedBumpFunctions) (N : ℕ)
    (hN_one : 1 ≤ N) (hN_three : N ≤ 3) :
    ∀ u : ℝ, |windowBasedBumpFunctions.theta b u| ≤
      C_thetaDecay N * bracketBump u ^ N := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:theta_decay},N}$ \auto]
\label{constant theta decay}
For $1\le N\le3$, $C_{\ref{lem:theta_decay},N}\le2^{2N+17}$.
\end{lemma}
-/
theorem constantThetaDecay (N : ℕ) (hN_one : 1 ≤ N) (hN_three : N ≤ 3) :
    C_thetaDecay N ≤ (2 : ℝ) ^ (2 * N + 17) := by
  sorry

/--
\begin{lemma}\label{lem:ft_phi3_eq}
For $k\in\mathbb Z$ and $\xi\in\mathbb R$,
\[\widehat{\varphi_{3,k}}(\xi)=2^k
(\widehat{\mathbf1_{[0,1)}}-1)(2^{-k}\xi)
\widehat{\phi_0}(2^{-k}\xi)\widehat\theta(\xi).\]
\end{lemma}
-/
theorem fourierPhiThreeEq (b : windowBasedBumpFunctions) (k : ℤ) (ξ : ℝ) :
    FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ)) ξ =
      (↑((2 : ℝ) ^ k) : ℂ) *
        (FourierTransform.fourier
          (fun x : ℝ ↦ (aux_indicator (Set.Ico 0 1) x : ℂ))
          ((2 : ℝ) ^ (-k) * ξ) - 1) *
        FourierTransform.fourier (fun x : ℝ ↦ (b.phi0 x : ℂ))
          ((2 : ℝ) ^ (-k) * ξ) *
        FourierTransform.fourier
          (fun x : ℝ ↦ (windowBasedBumpFunctions.theta b x : ℂ)) ξ := by
  sorry

/--
\begin{lemma}\label{lem:abs_deriv_ft_phi3_le}
For $m<4$, $k\in\mathbb Z$, and $|\xi|\le1$,
$|\widehat{\varphi_{3,k}}^{(m)}(\xi)|\le
C_{\ref{lem:abs_deriv_ft_phi3_le},m}$, with the four displayed constants from
the manuscript.
\end{lemma}
-/
theorem absDerivFourierPhiThreeLe (b : windowBasedBumpFunctions) (m : ℕ)
    (hm : m < 4) (k : ℤ) (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    ‖iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (windowBasedBumpFunctions.phiThree b k x : ℂ))) ξ‖ ≤
      C_absDerivFourierPhiThreeLe m := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:abs_deriv_ft_phi3_le},m}$ \auto]
\label{constant phi three derivative}
The constants for $m=0,1,2,3$ are respectively $2^2$, less than $2^{20}$,
less than $2^{37}$, and less than $2^{41}$.
\end{lemma}
-/
theorem constantPhiThreeDerivative :
    C_absDerivFourierPhiThreeLe 0 = (2 : ℝ) ^ 2 ∧
    C_absDerivFourierPhiThreeLe 1 < (2 : ℝ) ^ 20 ∧
    C_absDerivFourierPhiThreeLe 2 < (2 : ℝ) ^ 37 ∧
    C_absDerivFourierPhiThreeLe 3 < (2 : ℝ) ^ 41 := by
  sorry

/--
\begin{lemma}\label{lem:abs_deriv_ft_Tphi3_le}
For $m<3$, $k\in\mathbb Z$, and $|\xi|\le1$,
$|\widehat{T\varphi_{3,k}}^{(m)}(\xi)|\le
C_{\ref{lem:abs_deriv_ft_Tphi3_le},m}$, where
$C_{\ref{lem:abs_deriv_ft_Tphi3_le},m}=
mC_{\ref{lem:abs_deriv_ft_phi3_le},m}+
C_{\ref{lem:abs_deriv_ft_phi3_le},m+1}$.
\end{lemma}
-/
theorem absDerivFourierTPhiThreeLe (b : windowBasedBumpFunctions) (m : ℕ)
    (hm : m < 3) (k : ℤ) (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    ‖iteratedDeriv m
      (FourierTransform.fourier
        (fun x : ℝ ↦ (aux_T (windowBasedBumpFunctions.phiThree b k) x : ℂ))) ξ‖ ≤
      C_absDerivFourierTPhiThreeLe m := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:abs_deriv_ft_Tphi3_le},m}$ \auto]
\label{constant T phi three derivative}
For $m=0,1,2$, these constants are respectively less than $2^{20}$,
$2^{37}$, and $2^{41}$.
\end{lemma}
-/
theorem constantTPhiThreeDerivative :
    C_absDerivFourierTPhiThreeLe 0 < (2 : ℝ) ^ 20 ∧
    C_absDerivFourierTPhiThreeLe 1 < (2 : ℝ) ^ 37 ∧
    C_absDerivFourierTPhiThreeLe 2 < (2 : ℝ) ^ 41 := by
  sorry

/--
\begin{lemma}\label{lem:theta_prim}
The primitive $\widetilde\theta$ and $T\widetilde\theta$ have Fourier support in
$[-1,-2^{-2}]\cup[2^{-2},1]\subset\operatorname{Ann}_1(1,2^2)$.  For
$2\le N<N_{\ref{def:unipair}}$, both satisfy the decay bound with constant
$C_{\ref{lem:theta_prim},N}=2^{5N+6}C_{\ref{def:unipair}}$.
\end{lemma}
-/
theorem thetaPrimitive (b : windowBasedBumpFunctions) (N : ℕ)
    (hN_two : 2 ≤ N) (hN_uni : N < N_uniPair) :
    (Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.thetaTilde b x : ℂ))) ⊆ aux_frequencyAnnulus ∧
      aux_frequencyAnnulus ⊆ aux_annulusOne 1 ((2 : ℝ) ^ 2)) ∧
    (Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (aux_T (windowBasedBumpFunctions.thetaTilde b) x : ℂ))) ⊆
        aux_frequencyAnnulus ∧
      aux_frequencyAnnulus ⊆ aux_annulusOne 1 ((2 : ℝ) ^ 2)) ∧
    (∀ u : ℝ, |windowBasedBumpFunctions.thetaTilde b u| ≤
      C_thetaPrimitive N * bracketBump u ^ N) ∧
    ∀ u : ℝ, |aux_T (windowBasedBumpFunctions.thetaTilde b) u| ≤
      C_thetaPrimitive N * bracketBump u ^ N := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:theta_prim},N}$ \auto]
\label{constant theta primitive}
For $2\le N<N_{\ref{def:unipair}}$,
$C_{\ref{lem:theta_prim},N}\le2^{5N+21}$; in particular
$C_{\ref{lem:theta_prim},2}\le2^{31}$.
\end{lemma}
-/
theorem constantThetaPrimitive (N : ℕ) (hN_two : 2 ≤ N) (hN_uni : N < N_uniPair) :
    C_thetaPrimitive N ≤ (2 : ℝ) ^ (5 * N + 21) ∧
    C_thetaPrimitive 2 ≤ (2 : ℝ) ^ 31 := by
  sorry

/--
\begin{lemma}\label{lem:phi4_supp}
For every $k\in\mathbb Z$, both $\widehat{\varphi_{4,k}}$ and
$\widehat{T\varphi_{4,k}}$ are supported in
$[-1,-2^{-2}]\cup[2^{-2},1]$.
\end{lemma}
-/
theorem phiFourSupport (b : windowBasedBumpFunctions) (k : ℤ) :
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (windowBasedBumpFunctions.phiFour b k x : ℂ))) ⊆
        aux_frequencyAnnulus ∧
    Function.support (FourierTransform.fourier
      (fun x : ℝ ↦ (aux_T (windowBasedBumpFunctions.phiFour b k) x : ℂ))) ⊆
        aux_frequencyAnnulus := by
  sorry

end

end Codex.Reduction.SmoothingDecomposition
