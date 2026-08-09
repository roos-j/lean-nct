import LeanNct.WienerSpace

namespace Codex.Preliminaries.ConvolutionAlongVector

open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace

/-- \begin{definition}[Convolution along a vector]
For $\rho\in W_0(\R^n), \varphi\in W_0(\R)$ and a vector $\alpha\in\mathbb{R}^n$
define for $x\in\mathbb{R}^n$,
\[ (\rho *_\alpha \varphi)(x) = \int_{\R} \rho(x-p\alpha) \varphi(p)\,dp \]
\end{definition} -/
noncomputable def convolutionAlongVector {n : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    [NormedSpace ℝ 𝕜]
    (rho : EuclideanSpace ℝ (Fin n) → 𝕜) (phi : ℝ → 𝕜)
    (alpha : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) → 𝕜 :=
  fun x ↦ ∫ p : ℝ, rho (x - p • alpha) * phi p

/-- Auxiliary shear equivalence used to turn convolution along a vector into a coordinate-fibre
integral. -/
noncomputable def aux_shear {n : ℕ} (alpha : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × ℝ) where
  toFun := fun xp ↦ (xp.1 - xp.2 • alpha, xp.2)
  invFun := fun xp ↦ (xp.1 + xp.2 • alpha, xp.2)
  left_inv := by
    rintro ⟨x, p⟩
    ext <;> simp [sub_eq_add_neg]
  right_inv := by
    rintro ⟨x, p⟩
    ext <;> simp [sub_eq_add_neg]
  map_add' := by
    rintro ⟨x, p⟩ ⟨y, q⟩
    ext <;> simp [sub_eq_add_neg, add_smul]; abel
  map_smul' := by
    rintro r ⟨x, p⟩
    ext <;> simp [sub_eq_add_neg, smul_add, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Auxiliary dominated-convergence argument for the continuity of an integral over the real
coordinate of a Wiener-space function. -/
theorem aux_continuous_integral_real {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {f : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜} (hf : MemW0 f) :
    Continuous (fun u ↦ ∫ p, f (u, p)) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  have hgood_ae :
      ∀ᵐ u' ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Integrable (fun p ↦ wienerEnvelope f 1 (u', p)) := by
    exact hf.2.prod_right_ae
  obtain ⟨u', hu', hu'good⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (s := ball u₀ (1 / 2))
    ((measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) u₀ (by norm_num)).ne')
    (ae_restrict_of_ae hgood_ae)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun p ↦ wienerEnvelope f 1 (u', p))
  · filter_upwards [] with u
    exact (hf.1.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds u₀ (by norm_num : 0 < (1 / 2 : ℝ))] with u hu
    filter_upwards [] with p
    apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
    apply Metric.mem_closedBall.mpr
    rw [Prod.dist_eq]
    apply max_le
    · change dist u u' ≤ 1
      apply le_of_lt
      calc
        dist u u' ≤ dist u u₀ + dist u₀ u' := dist_triangle _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (Metric.mem_ball.mp hu)
          (by simpa [dist_comm] using (Metric.mem_ball.mp hu'))
        _ = 1 := by norm_num
    · change dist p p ≤ 1
      simp
  · exact hu'good
  · filter_upwards [] with p
    exact hf.1.continuousAt.tendsto.comp
      (continuous_id.prodMk continuous_const).continuousAt

/-- Auxiliary fact extracting ordinary integrability from Wiener-space membership. -/
theorem aux_integrable_of_memW0 {E 𝕜 : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [MeasureSpace E] [BorelSpace E] [NormedAddCommGroup 𝕜]
    {f : E → 𝕜} (hf : MemW0 f) : Integrable f := by
  refine hf.2.mono hf.1.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (aux_wienerEnvelope_nonneg hf.1 zero_le_one x)] using
      aux_norm_le_wienerEnvelope hf.1 zero_le_one x

/-- Auxiliary fibre-integration closure result needed for convolution along a real direction. -/
theorem aux_memW0_integral_real {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {f : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜} (hf : MemW0 f) :
    MemW0 (fun u ↦ ∫ p, f (u, p)) := by
  letI : Measure.IsAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
    infer_instance
  let F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := wienerEnvelope f 1
  have hF : MemW0 F := by
    simpa [F] using hf.aux_mem_wienerEnvelope zero_le_one
  have hF_slice (u : EuclideanSpace ℝ (Fin n)) : Integrable (fun p ↦ F (u, p)) :=
    aux_integrable_of_memW0 (hF.aux_memW0_slice_of_addHaar u)
  have hf_slice (u : EuclideanSpace ℝ (Fin n)) : Integrable (fun p ↦ f (u, p)) :=
    aux_integrable_of_memW0 (hf.aux_memW0_slice_of_addHaar u)
  have hcont : Continuous (fun u ↦ ∫ p, f (u, p)) := aux_continuous_integral_real hf
  refine ⟨hcont, ?_⟩
  have hH : Integrable (fun u ↦ ∫ p, F (u, p)) := hf.2.integral_prod_left
  refine hH.mono_nonneg (continuous_wienerEnvelope hcont 1).aestronglyMeasurable
    (ae_of_all _ fun u ↦ aux_wienerEnvelope_nonneg hcont zero_le_one u)
    (ae_of_all _ fun u ↦ ?_)
  unfold wienerEnvelope
  apply csSup_le ((Metric.nonempty_closedBall.mpr zero_le_one).image _)
  rintro _ ⟨w, hw, rfl⟩
  change ‖∫ p, f (u + w, p)‖ ≤ ∫ p, F (u, p)
  calc
    ‖∫ p, f (u + w, p)‖ ≤ ∫ p, ‖f (u + w, p)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, F (u, p) := by
      apply integral_mono (hf_slice (u + w)).norm (hF_slice u)
      intro p
      change ‖f (u + w, p)‖ ≤ wienerEnvelope f 1 (u, p)
      apply aux_norm_le_wienerEnvelope_of_mem_closedBall hf.1
      apply Metric.mem_closedBall.mpr
      rw [Prod.dist_eq]
      apply max_le
      · simpa [Metric.mem_closedBall, dist_eq_norm] using hw
      · simp

/-- For $\rho \in W_0(\R^n), \varphi\in W_0(\R), \alpha\in\mathbb{R}^n$ we have
$\rho *_\alpha \varphi\in W_0(\R^n)$. -/
theorem memW0_convolutionAlongVector {n : ℕ}
    {𝕜 : Type*} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [CompleteSpace 𝕜]
    {rho : EuclideanSpace ℝ (Fin n) → 𝕜} {phi : ℝ → 𝕜}
    (hrho : MemW0 rho) (hphi : MemW0 phi)
    (alpha : EuclideanSpace ℝ (Fin n)) :
    MemW0 (convolutionAlongVector rho phi alpha) := by
  letI : Measure.IsAddHaarMeasure
      (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) := by
    change Measure.IsAddHaarMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
    infer_instance
  let F : EuclideanSpace ℝ (Fin n) × ℝ → 𝕜 := fun xp ↦ rho xp.1 * phi xp.2
  have hF : MemW0 F := by
    simpa [F] using hrho.aux_mul_prod hphi
  have hFs : MemW0 (F ∘ aux_shear alpha) := by
    apply hF.aux_comp_continuousLinearEquiv_between_of_integrable_radius (aux_shear alpha)
    exact aux_integrable_wienerEnvelope_of_integrable' hF.1 zero_lt_one
      (norm_nonneg (aux_shear alpha).toContinuousLinearMap) hF.2
  have hI := aux_memW0_integral_real hFs
  change MemW0 (fun u ↦ ∫ p : ℝ, rho (u - p • alpha) * phi p)
  simpa [F, aux_shear, Function.comp_def] using hI

/-- For $\rho \in W_0(\R^n), \varphi\in W_0(\R),
$\alpha,\xi\in\mathbb{R}^n$ we have
\[
\widehat{\rho *_\alpha \varphi}(\xi) = \widehat{\rho}(\xi)\widehat{\varphi}(\alpha\cdot\xi).
\] -/
theorem fourier_convolutionAlongVector {n : ℕ}
    {rho : EuclideanSpace ℝ (Fin n) → ℂ} {phi : ℝ → ℂ}
    (hrho : MemW0 rho) (hphi : MemW0 phi)
    (alpha xi : EuclideanSpace ℝ (Fin n)) :
    FourierTransform.fourier (convolutionAlongVector rho phi alpha) xi =
      FourierTransform.fourier rho xi *
        FourierTransform.fourier phi (inner ℝ alpha xi) := by
  have hrho_integrable : Integrable rho := aux_integrable_of_memW0 hrho
  have hphi_integrable : Integrable phi := aux_integrable_of_memW0 hphi
  let K : EuclideanSpace ℝ (Fin n) × ℝ → ℂ := fun xp ↦
    rho (xp.1 - xp.2 • alpha) * phi xp.2
  have hK_measurable : AEStronglyMeasurable K
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ)) := by
    apply Continuous.aestronglyMeasurable
    exact
      (hrho.1.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).mul
        (hphi.1.comp continuous_snd)
  have hK : Integrable K
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ)) := by
    rw [integrable_prod_iff' hK_measurable]
    refine ⟨Filter.Eventually.of_forall fun p ↦ ?_, ?_⟩
    · exact (hrho_integrable.comp_sub_right (p • alpha)).mul_const (phi p)
    · have hnorm (p : ℝ) :
          (∫ x : EuclideanSpace ℝ (Fin n), ‖K (x, p)‖) =
            (∫ x : EuclideanSpace ℝ (Fin n), ‖rho x‖) * ‖phi p‖ := by
        simp only [K, norm_mul]
        rw [integral_mul_const]
        congr 1
        exact integral_sub_right_eq_self
          (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖rho x‖) (p • alpha)
      convert hphi_integrable.norm.const_mul
        (∫ x : EuclideanSpace ℝ (Fin n), ‖rho x‖) using 1
      ext p
      rw [hnorm]
  let H : EuclideanSpace ℝ (Fin n) × ℝ → ℂ := fun xp ↦
    𝐞 (-inner ℝ xp.1 xi) • K xp
  have hH : Integrable H
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ)) := by
    refine hK.mono ?_ ?_
    · exact
        (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
          hK.aestronglyMeasurable
    · filter_upwards with xp
      exact le_of_eq (Circle.norm_smul (𝐞 (-inner ℝ xp.1 xi)) (K xp))
  have htranslate (p : ℝ) :
      (∫ x : EuclideanSpace ℝ (Fin n),
        𝐞 (-inner ℝ x xi) • rho (x - p • alpha)) =
        𝐞 (-(p * inner ℝ alpha xi)) • FourierTransform.fourier rho xi := by
    calc
      (∫ x : EuclideanSpace ℝ (Fin n),
        𝐞 (-inner ℝ x xi) • rho (x - p • alpha)) =
          FourierTransform.fourier
            (rho ∘ fun x : EuclideanSpace ℝ (Fin n) ↦ x + (-p • alpha)) xi := by
            rw [Real.fourier_eq]
            congr 1
            ext x
            simp [sub_eq_add_neg]
      _ = 𝐞 (inner ℝ (-p • alpha) xi) • FourierTransform.fourier rho xi := by
        exact congrFun
          (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin n))) rho (-p • alpha)) xi
      _ = 𝐞 (-(p * inner ℝ alpha xi)) • FourierTransform.fourier rho xi := by
        congr 1
        rw [real_inner_smul_left]
        ring_nf
  calc
    FourierTransform.fourier (convolutionAlongVector rho phi alpha) xi =
        ∫ x : EuclideanSpace ℝ (Fin n), ∫ p : ℝ,
          𝐞 (-inner ℝ x xi) • (rho (x - p • alpha) * phi p) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [convolutionAlongVector]
      simp_rw [Circle.smul_def, integral_smul]
    _ = ∫ p : ℝ, ∫ x : EuclideanSpace ℝ (Fin n),
          𝐞 (-inner ℝ x xi) • (rho (x - p • alpha) * phi p) := by
      apply integral_integral_swap
      change Integrable
        (Function.uncurry fun (x : EuclideanSpace ℝ (Fin n)) (p : ℝ) ↦
          𝐞 (-inner ℝ x xi) • (rho (x - p • alpha) * phi p)) _
      convert hH using 1; rfl
    _ = ∫ p : ℝ, ((∫ x : EuclideanSpace ℝ (Fin n),
          𝐞 (-inner ℝ x xi) • rho (x - p • alpha)) * phi p) := by
      congr with p
      rw [← integral_mul_const]
      congr with x
      simp [Circle.smul_def, mul_assoc]
    _ = ∫ p : ℝ, (𝐞 (-(p * inner ℝ alpha xi)) • FourierTransform.fourier rho xi) * phi p := by
      congr with p
      rw [htranslate p]
    _ = (FourierTransform.fourier rho xi) *
        ∫ p : ℝ, 𝐞 (-(p * inner ℝ alpha xi)) • phi p := by
      rw [← integral_const_mul]
      congr with p
      simp [Circle.smul_def]
      ring_nf
    _ = FourierTransform.fourier rho xi *
        FourierTransform.fourier phi (inner ℝ alpha xi) := by
      rw [← Real.fourier_real_eq]

end Codex.Preliminaries.ConvolutionAlongVector
