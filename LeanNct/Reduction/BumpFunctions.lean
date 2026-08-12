import LeanNct.Preliminaries.BumpsAndEstimates

/-!
# Bump functions

Formalization of the ``Bump functions'' subsection of the reduction argument.
-/

namespace Codex.Reduction.BumpFunctions

open MeasureTheory Set
open scoped BigOperators FourierTransform Real RealInnerProductSpace

open Codex.Preliminaries.Notation

noncomputable section

/-- The multiplication operator $X\phi(u)=u\phi(u)$ from
\eqref{auto:multiplication-operator-X}. -/
noncomputable def multiplicationOperatorX {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (phi : ℝ → E) : ℝ → E :=
  fun u ↦ u • phi u

/-- The logarithmic-derivative operator $T\phi=(X\phi)'$ used in
Lemma \ref{lem:ft_deriv_mul}. -/
noncomputable def aux_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (phi : ℝ → E) : ℝ → E :=
  fun x ↦ deriv (multiplicationOperatorX phi) x

/--
\begin{lemma}\label{lem:ft_deriv_mul}
For a Schwartz function $\phi:\mathbb{R}\to\mathbb{C}$, let
$T\phi(x)=\frac{d}{dx}(x\phi(x))$.  Then, for every $m\geq0$,
\[
  (\widehat{T\phi})^{(m)}(\xi)=
  -(m(\widehat\phi)^{(m)}(\xi)+\xi(\widehat\phi)^{(m+1)}(\xi)).
\]
\end{lemma}
-/
theorem fourierDerivativeMul (phi : SchwartzMap ℝ ℂ) (m : ℕ) (xi : ℝ) :
    iteratedDeriv m
        (FourierTransform.fourier (aux_T (fun x : ℝ ↦ phi x))) xi =
      -((m : ℂ) * iteratedDeriv m
          (FourierTransform.fourier (fun x : ℝ ↦ phi x)) xi +
        (xi : ℂ) * iteratedDeriv (m + 1)
        (FourierTransform.fourier (fun x : ℝ ↦ phi x)) xi) := by
  let psi : SchwartzMap ℝ ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) phi
  let tau : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ psi
  have hpsi : ∀ x : ℝ, psi x = multiplicationOperatorX (fun x : ℝ ↦ phi x) x := by
    intro x
    change (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) phi) x = _
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    simp [multiplicationOperatorX]
  have hpsi_fun : (psi : ℝ → ℂ) = multiplicationOperatorX (fun x : ℝ ↦ phi x) := funext hpsi
  have htau : ∀ x : ℝ, tau x = aux_T (fun x : ℝ ↦ phi x) x := by
    intro x
    simp only [tau, aux_T, SchwartzMap.derivCLM_apply]
    rw [hpsi_fun]
  have hlineTau : LineDeriv.lineDerivOp (1 : ℝ) psi = tau := by
    ext x
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, tau, SchwartzMap.derivCLM_apply]
    rw [fderiv_apply_one_eq_deriv]
  have hsmul : SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ ⟪x, (1 : ℝ)⟫) phi = psi := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    calc
      ⟪x, (1 : ℝ)⟫ • phi x = (x : ℂ) * phi x := by
        simp
      _ = psi x := by
        rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
        simp only [smul_eq_mul]
  have hDerivPhi :
      SchwartzMap.derivCLM ℂ ℂ (FourierTransform.fourier phi) =
        FourierTransform.fourier (-(2 * Real.pi * Complex.I) • psi) := by
    calc
      SchwartzMap.derivCLM ℂ ℂ (FourierTransform.fourier phi) =
          LineDeriv.lineDerivOp (1 : ℝ) (FourierTransform.fourier phi) := by
        ext x
        simp only [SchwartzMap.derivCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        rw [fderiv_apply_one_eq_deriv]
      _ = FourierTransform.fourier
          (-(2 * Real.pi * Complex.I) •
            SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ ⟪x, (1 : ℝ)⟫) phi) :=
          SchwartzMap.lineDerivOp_fourier_eq phi (1 : ℝ)
      _ = FourierTransform.fourier (-(2 * Real.pi * Complex.I) • psi) := by rw [hsmul]
  have hFourierTau :
      FourierTransform.fourier tau =
        (2 * Real.pi * Complex.I) •
          SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ ⟪x, (1 : ℝ)⟫)
            (FourierTransform.fourier psi) := by
    rw [← hlineTau]
    exact SchwartzMap.fourier_lineDerivOp_eq psi (1 : ℝ)
  have hDerivPhiAt (x : ℝ) :
      deriv (FourierTransform.fourier (phi : ℝ → ℂ)) x =
        -(2 * Real.pi * Complex.I) *
          FourierTransform.fourier (psi : ℝ → ℂ) x := by
    have h := congrArg (fun f : SchwartzMap ℝ ℂ ↦ f x) hDerivPhi
    simpa [SchwartzMap.fourier_coe, smul_eq_mul, mul_assoc] using h
  have hFourierTauAt (x : ℝ) :
      FourierTransform.fourier (tau : ℝ → ℂ) x =
        (2 * Real.pi * Complex.I) * (x : ℂ) *
          FourierTransform.fourier (psi : ℝ → ℂ) x := by
    have h := congrArg (fun f : SchwartzMap ℝ ℂ ↦ f x) hFourierTau
    change FourierTransform.fourier (tau : ℝ → ℂ) x =
      (2 * Real.pi * Complex.I) *
        (SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ ⟪y, (1 : ℝ)⟫)
          (FourierTransform.fourier psi)) x at h
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)] at h
    simpa [SchwartzMap.fourier_coe, smul_eq_mul, mul_assoc] using h
  have htau_fun : (tau : ℝ → ℂ) = aux_T (fun x : ℝ ↦ phi x) := funext htau
  have hbase : FourierTransform.fourier (aux_T (fun x : ℝ ↦ phi x)) =
      fun x : ℝ ↦ -(x : ℂ) *
        deriv (FourierTransform.fourier (phi : ℝ → ℂ)) x := by
    ext x
    rw [← htau_fun, hFourierTauAt, hDerivPhiAt]
    ring
  have hdiff (k : ℕ) :
      Differentiable ℝ (iteratedDeriv k (FourierTransform.fourier (phi : ℝ → ℂ))) := by
    apply ContDiff.differentiable_iteratedDeriv' k
    simpa [SchwartzMap.fourier_coe] using
      (FourierTransform.fourier phi : SchwartzMap ℝ ℂ).smooth (k + 1)
  rw [hbase]
  have hformula : ∀ k : ℕ,
      iteratedDeriv k (fun x : ℝ ↦ -(x •
          deriv (FourierTransform.fourier (phi : ℝ → ℂ)) x)) =
        fun x : ℝ ↦ -((k : ℝ) •
          iteratedDeriv k (FourierTransform.fourier (phi : ℝ → ℂ)) x +
          x • iteratedDeriv (k + 1)
            (FourierTransform.fourier (phi : ℝ → ℂ)) x) := by
    intro k
    induction k with
    | zero =>
        funext x
        simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, zero_add]
        rw [iteratedDeriv_one]
        simp
    | succ k ih =>
        rw [iteratedDeriv_succ, ih]
        funext x
        have hiter (j : ℕ) : HasDerivAt
            (iteratedDeriv j (FourierTransform.fourier (phi : ℝ → ℂ)))
            (iteratedDeriv (j + 1) (FourierTransform.fourier (phi : ℝ → ℂ)) x) x := by
          simpa only [iteratedDeriv_succ] using (hdiff j x).hasDerivAt
        have hid : HasDerivAt (fun y : ℝ ↦ y) 1 x := hasDerivAt_id' x
        have hA : HasDerivAt (fun y : ℝ ↦ (k : ℝ) •
            iteratedDeriv k (FourierTransform.fourier (phi : ℝ → ℂ)) y)
            ((k : ℝ) • iteratedDeriv (k + 1)
              (FourierTransform.fourier (phi : ℝ → ℂ)) x) x :=
          (hiter k).const_smul (k : ℝ)
        have hBraw : HasDerivAt
            ((fun y : ℝ ↦ y) •
              iteratedDeriv (k + 1) (FourierTransform.fourier (phi : ℝ → ℂ)))
            (x • iteratedDeriv (k + 1 + 1)
              (FourierTransform.fourier (phi : ℝ → ℂ)) x +
              (1 : ℝ) • iteratedDeriv (k + 1)
                (FourierTransform.fourier (phi : ℝ → ℂ)) x) x := by
          exact HasDerivAt.smul (𝕜' := ℝ) hid (hiter (k + 1))
        have hBfun : ((fun y : ℝ ↦ y) •
            iteratedDeriv (k + 1) (FourierTransform.fourier (phi : ℝ → ℂ))) =
            fun y : ℝ ↦ y •
              iteratedDeriv (k + 1) (FourierTransform.fourier (phi : ℝ → ℂ)) y := by
          rfl
        have hB : HasDerivAt (fun y : ℝ ↦ y •
            iteratedDeriv (k + 1) (FourierTransform.fourier (phi : ℝ → ℂ)) y)
            (x • iteratedDeriv (k + 1 + 1)
              (FourierTransform.fourier (phi : ℝ → ℂ)) x +
              (1 : ℝ) • iteratedDeriv (k + 1)
                (FourierTransform.fourier (phi : ℝ → ℂ)) x) x := by
          rw [← hBfun]
          exact hBraw
        have hsum : HasDerivAt (fun y : ℝ ↦ -((k : ℝ) •
            iteratedDeriv k (FourierTransform.fourier (phi : ℝ → ℂ)) y +
            y • iteratedDeriv (k + 1)
              (FourierTransform.fourier (phi : ℝ → ℂ)) y))
            (-((k : ℝ) • iteratedDeriv (k + 1)
              (FourierTransform.fourier (phi : ℝ → ℂ)) x +
              (x • iteratedDeriv (k + 1 + 1)
                (FourierTransform.fourier (phi : ℝ → ℂ)) x +
              (1 : ℝ) • iteratedDeriv (k + 1)
                (FourierTransform.fourier (phi : ℝ → ℂ)) x))) x := by
          exact (hA.add hB).neg
        rw [hsum.deriv]
        simp [Nat.cast_add]
        ring
  simpa [smul_eq_mul] using congrFun (hformula m) xi

/-- The explicit constant in Lemma \ref{lem:widebump}. -/
noncomputable def C_wideBump (N : ℝ) : ℝ :=
  Real.rpow 2 (3 * N)

/--
\begin{lemma}\label{lem:widebump}
Let $k\leq2$ and $t\in[2^{1-k},2^{2-k}]$.  Then for every $u\in\mathbb R$
and $N\geq0$,
\[
  \langle u-t\rangle^N\leq C_{\ref{lem:widebump},N}
  2^{-kN}\langle u\rangle^N,
  \qquad C_{\ref{lem:widebump},N}=2^{3N}.
\]
\end{lemma}
-/
theorem wideBump (k : ℤ) (hk : k ≤ 2) (t : ℝ)
    (ht : t ∈ Set.Icc ((2 : ℝ) ^ (1 - k)) ((2 : ℝ) ^ (2 - k)))
    (u N : ℝ) (hN : 0 ≤ N) :
    Real.rpow (bracketBump (u - t)) N ≤
      C_wideBump N * Real.rpow 2 (-((k : ℝ) * N)) *
        Real.rpow (bracketBump u) N := by
  have htpos : 0 < t := (zpow_pos (by norm_num : (0 : ℝ) < 2) _).trans_le ht.1
  have hpowone : 1 ≤ (2 : ℝ) ^ (2 - k) := by
    apply one_le_zpow₀
    · norm_num
    · omega
  have hfactor : 1 + t ≤ (2 : ℝ) ^ (3 - k) := by
    calc
      1 + t ≤ 1 + (2 : ℝ) ^ (2 - k) := by gcongr; exact ht.2
      _ ≤ (2 : ℝ) ^ (2 - k) + (2 : ℝ) ^ (2 - k) := by linarith
      _ = (2 : ℝ) ^ (3 - k) := by
        rw [show (3 - k : ℤ) = (2 - k) + 1 by omega,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        ring
  have htri : 1 + |u| ≤ (1 + |u - t|) * (1 + t) := by
    calc
      1 + |u| = 1 + |(u - t) + t| := by congr 2 <;> ring
      _ ≤ 1 + (|u - t| + |t|) := by gcongr; exact abs_add_le _ _
      _ ≤ (1 + |u - t|) * (1 + t) := by
        rw [abs_of_pos htpos]
        nlinarith [abs_nonneg (u - t)]
  have hdenleft : 0 < 1 + |u - t| := by positivity
  have hdenright : 0 < 1 + |u| := by positivity
  have hbase : bracketBump (u - t) ≤ (1 + t) * bracketBump u := by
    rw [bracketBump, bracketBump]
    rw [← div_eq_mul_inv, ← one_div]
    rw [div_le_div_iff₀ hdenleft hdenright]
    simpa [mul_comm] using htri
  have hbrpos (v : ℝ) : 0 < bracketBump v := by
    rw [bracketBump]
    exact inv_pos.mpr (by positivity)
  have hbase' : bracketBump (u - t) ≤ (2 : ℝ) ^ (3 - k) * bracketBump u :=
    hbase.trans (mul_le_mul_of_nonneg_right hfactor (hbrpos u).le)
  have hp : Real.rpow (bracketBump (u - t)) N ≤
      Real.rpow ((2 : ℝ) ^ (3 - k) * bracketBump u) N :=
    Real.rpow_le_rpow (hbrpos _).le hbase' hN
  have hp' : Real.rpow (bracketBump (u - t)) N ≤
      Real.rpow ((2 : ℝ) ^ (3 - k)) N * Real.rpow (bracketBump u) N :=
    hp.trans_eq (Real.mul_rpow (zpow_pos (by norm_num) _).le (hbrpos _).le)
  calc
    Real.rpow (bracketBump (u - t)) N ≤
        Real.rpow ((2 : ℝ) ^ (3 - k)) N * Real.rpow (bracketBump u) N := hp'
    _ = Real.rpow 2 ((3 - (k : ℝ)) * N) * Real.rpow (bracketBump u) N := by
      congr 1
      simpa using
        (Real.rpow_intCast_mul (x := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2) (3 - k) N).symm
    _ = C_wideBump N * Real.rpow 2 (-((k : ℝ) * N)) *
        Real.rpow (bracketBump u) N := by
      rw [C_wideBump]
      calc
        Real.rpow 2 ((3 - (k : ℝ)) * N) * Real.rpow (bracketBump u) N =
            Real.rpow 2 (3 * N + -((k : ℝ) * N)) * Real.rpow (bracketBump u) N := by
          congr 2
          ring
        _ = (Real.rpow 2 (3 * N) * Real.rpow 2 (-((k : ℝ) * N))) *
            Real.rpow (bracketBump u) N := by
          exact congrArg (fun q : ℝ ↦ q * Real.rpow (bracketBump u) N)
            (Real.rpow_add (x := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2)
              (3 * N) (-((k : ℝ) * N)))

/-- The constant in Lemma \ref{lem:thetat_offcenter}. -/
noncomputable def C_thetaTOffcenter : ℝ := 133

/--
\begin{lemma}\label{lem:thetat_offcenter}
Let $k\leq-1$.  Then for every $(v_0,v_1)\in\mathbb R^2$,
\[
2^{k/2}\int_1^2\langle v_0-t2^{-k}\rangle^2
\langle v_1-t2^{-k}\rangle^2\,dt
\leq C_{\ref{lem:thetat_offcenter}}
\bigl(\langle v_0\rangle^{3/2}\langle v_1\rangle^{3/2}+
\langle v_0+v_1\rangle^{3/2}\langle v_0-v_1\rangle^{3/2}\bigr),
\]
where $C_{\ref{lem:thetat_offcenter}}=133$.
\end{lemma}
-/
theorem thetaTOffcenter (k : ℤ) (hk : k ≤ -1) (v₀ v₁ : ℝ) :
    Real.rpow 2 ((k : ℝ) / 2) *
        ∫ t : ℝ in Set.Icc 1 2,
          bracketBump (v₀ - t * ((2 : ℝ) ^ (-k))) ^ 2 *
            bracketBump (v₁ - t * ((2 : ℝ) ^ (-k))) ^ 2 ≤
      C_thetaTOffcenter *
        (Real.rpow (bracketBump v₀) (3 / 2 : ℝ) *
            Real.rpow (bracketBump v₁) (3 / 2 : ℝ) +
          Real.rpow (bracketBump (v₀ + v₁)) (3 / 2 : ℝ) *
            Real.rpow (bracketBump (v₀ - v₁)) (3 / 2 : ℝ)) := by
  sorry

/--
\begin{lemma}[constant $C_{\ref{lem:thetat_offcenter}}$ \auto]
\label{constant off center bump}
\[
  C_{\ref{lem:thetat_offcenter}}\leq133.
\]
\end{lemma}
-/
theorem constantOffCenterBump : C_thetaTOffcenter ≤ 133 := by
  sorry

/-- The one-dimensional $L^1$-normalized dilation used in Lemma \ref{lem:int_fct}. -/
noncomputable def aux_realRescaled (t : ℝ) (psi : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ t⁻¹ * psi (t⁻¹ * x)

/-- The tensor kernel defined by the integral in Lemma \ref{lem:int_fct}. -/
noncomputable def integralFctKernel (psi : ℝ → ℝ) :
    EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun u ↦ ∫ t : ℝ in Set.Icc 1 2,
    aux_realRescaled t psi (u 0) * aux_realRescaled t psi (u 1) * t⁻¹

/-- The $L^1$-normalized two-dimensional dilation of `integralFctKernel`. -/
noncomputable def aux_integralFctKernelAtScale (s : ℝ) (psi : ℝ → ℝ) :
    EuclideanSpace ℝ (Fin 2) → ℝ :=
  rescaled s (integralFctKernel psi)

/-- The frequency set in the support conclusion of Lemma \ref{lem:int_fct}. -/
noncomputable def aux_integralFctBand (ell : ℤ) : Set ℝ :=
  Set.Icc (-((2 : ℝ) ^ (-ell))) (-((2 : ℝ) ^ (-3 - ell))) ∪
    Set.Icc ((2 : ℝ) ^ (-3 - ell)) ((2 : ℝ) ^ (-ell))

/-- The one-dimensional annulus convention used in `integralFct`. -/
def aux_annulusOne (r R : ℝ) : Set ℝ :=
  {xi | r / R ≤ |xi| ∧ |xi| ≤ R * r}

/-- The coordinatewise square of a one-dimensional frequency set. -/
def aux_productSet (s : Set ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {xi | xi 0 ∈ s ∧ xi 1 ∈ s}

/-- The coordinate swap on $mathbb R^2$ used in the symmetry assertion of
Lemma \ref{lem:int_fct}. -/
noncomputable def aux_swapTwo (u : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![u 1, u 0]

/-- A bounded real function, in the sense needed by the positivity statements in
Lemmas \ref{lem:int_fct} and \ref{lem:Phipos_v2}. -/
def aux_bounded (f : ℝ → ℝ) : Prop :=
  Bornology.IsBounded (Set.range f)

/--
\begin{lemma}\label{lem:int_fct}
Let $\psi:\mathbb R\to\mathbb R$ be Schwartz and suppose that
$\operatorname{supp}(\widehat\psi)\subset[-1,-2^{-2}]\cup[2^{-2},1]$.
For
\[\Psi(u,v)=\int_1^2\psi_{(t)}(u)\psi_{(t)}(v)\,\frac{dt}{t}\]
and $\ell\in\mathbb Z$, the kernel $\Psi_{(2^\ell)}$ is symmetric, has
nonnegative quadratic forms against bounded functions, and has Fourier support in
\[
([-2^{-\ell},-2^{-3-\ell}]\cup[2^{-3-\ell},2^{-\ell}])^2
\subset \operatorname{Ann}_1(2^{-\ell},2^3)^2.
\]
\end{lemma}
-/
theorem integralFct (psi : SchwartzMap ℝ ℝ)
    (hpsi : Function.support
      (FourierTransform.fourier (fun x : ℝ ↦ (psi x : ℂ))) ⊆
        Set.Icc (-1 : ℝ) (-(1 / 4 : ℝ)) ∪ Set.Icc (1 / 4 : ℝ) 1)
    (ell : ℤ) :
    (∀ u : EuclideanSpace ℝ (Fin 2),
      aux_integralFctKernelAtScale ((2 : ℝ) ^ ell) (fun x ↦ psi x) u =
        aux_integralFctKernelAtScale ((2 : ℝ) ^ ell) (fun x ↦ psi x)
          (aux_swapTwo u)) ∧
    (∀ f : ℝ → ℝ, aux_bounded f →
      0 ≤ ∫ u : EuclideanSpace ℝ (Fin 2),
        f (u 0) * f (u 1) *
          aux_integralFctKernelAtScale ((2 : ℝ) ^ ell) (fun x ↦ psi x) u) ∧
    (Function.support (FourierTransform.fourier
      (fun u : EuclideanSpace ℝ (Fin 2) ↦
        (aux_integralFctKernelAtScale ((2 : ℝ) ^ ell) (fun x ↦ psi x) u : ℂ))) ⊆
        aux_productSet (aux_integralFctBand ell) ∧
      aux_productSet (aux_integralFctBand ell) ⊆
        aux_productSet (aux_annulusOne ((2 : ℝ) ^ (-ell)) ((2 : ℝ) ^ 3))) := by
  sorry

/--
\begin{lemma}\label{lem:Phipos_v2}
Let $\Psi:\mathbb R^2\to\mathbb R$ be symmetric and suppose that for every
bounded $g:\mathbb R\to\mathbb R$,
\[
  \int_{\mathbb R^2}g(u_0)g(u_1)\Psi(u)\,du\geq0.
\]
Then for every $\xi\in\mathbb R$,
\[
  \widehat\Psi(\xi,-\xi)\geq0.
\]
\end{lemma}
-/
theorem phiPosV2 (Psi : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hsym : ∀ u : EuclideanSpace ℝ (Fin 2), Psi u = Psi (aux_swapTwo u))
    (hpos : ∀ g : ℝ → ℝ, aux_bounded g →
      0 ≤ ∫ u : EuclideanSpace ℝ (Fin 2), g (u 0) * g (u 1) * Psi u)
    (xi : ℝ) :
    0 ≤ (FourierTransform.fourier (fun u : EuclideanSpace ℝ (Fin 2) ↦ (Psi u : ℂ))
      (WithLp.toLp 2 ![xi, -xi])).re := by
  sorry

end

end Codex.Reduction.BumpFunctions
