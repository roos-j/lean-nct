import LeanNct.Reduction.TwistedAverages
import LeanNct.Preliminaries.MKernels

/-!
# Average to prism form

Formalization of the ``$A$ to $\Lambda_1$'' reduction lemma.
-/

namespace Codex.Reduction.AToLambda

open MeasureTheory
open scoped BigOperators ENNReal

open Codex.Reduction.TwistedAverages
open Codex.Preliminaries.KKernels
open Codex.Preliminaries.MKernels

noncomputable section

/-!
The proof below is most transparent in raw coordinate spaces.  The
permutation `indexPerm` is essential: `concatVector` puts its singleton
block in coordinate zero, whereas the prism's deleted coordinate is `i`.
Thus the permutation is applied before the determinant-one shear.
-/
namespace aux_aToLambda

variable {n : ℕ}

/-- The determinant-one shear, after the distinguished coordinate has been moved to `i`. -/
def rawShear (i : Fin n) (x : RealVector n) : RealVector n :=
  fun r => if r = i then ∑ q, x q else -x r

lemma rawShear_sum (i : Fin n) (x : RealVector n) :
    ∑ r, rawShear i x r = x i := by
  rw [← Finset.sum_erase_add Finset.univ (rawShear i x) (Finset.mem_univ i)]
  have herase :
      (∑ r ∈ Finset.univ.erase i, rawShear i x r) =
        ∑ r ∈ Finset.univ.erase i, -x r := by
    apply Finset.sum_congr rfl
    intro r hr
    exact if_neg (Finset.mem_erase.mp hr).1
  rw [herase]
  rw [Finset.sum_neg_distrib]
  have hi : rawShear i x i = ∑ q, x q := by simp [rawShear]
  rw [hi]
  change -(∑ r ∈ Finset.univ.erase i, x r) + (∑ q, x q) = x i
  have hsum := Finset.add_sum_erase Finset.univ x (Finset.mem_univ i)
  rw [← hsum]
  ring

lemma rawShear_involutive (i : Fin n) (x : RealVector n) :
    rawShear i (rawShear i x) = x := by
  funext r
  by_cases hr : r = i
  · subst r
    show (if i = i then ∑ q, rawShear i x q else -(rawShear i x i)) = x i
    rw [if_pos rfl]
    exact rawShear_sum i x
  · simp [rawShear, hr]

noncomputable def rawShearLinearEquiv (i : Fin n) : RealVector n ≃ₗ[ℝ] RealVector n where
  toFun := rawShear i
  invFun := rawShear i
  left_inv := rawShear_involutive i
  right_inv := rawShear_involutive i
  map_add' x y := by
    funext r
    by_cases hr : r = i
    · subst r
      simp [rawShear, Finset.sum_add_distrib]
    · simp [rawShear, hr]
      ring
  map_smul' c x := by
    funext r
    by_cases hr : r = i
    · subst r
      simp [rawShear, Finset.mul_sum]
    · simp [rawShear, hr]

lemma rawShearLinearEquiv_comp_self (i : Fin n) :
    (rawShearLinearEquiv i).toLinearMap.comp (rawShearLinearEquiv i).toLinearMap =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact rawShear_involutive i x

lemma rawShear_det_sq (i : Fin n) :
    LinearMap.det (rawShearLinearEquiv i).toLinearMap ^ 2 = 1 := by
  rw [pow_two, ← LinearMap.det_comp, rawShearLinearEquiv_comp_self, LinearMap.det_id]

lemma rawShear_det_abs (i : Fin n) :
    |LinearMap.det (rawShearLinearEquiv i).toLinearMap| = 1 := by
  have hsq := rawShear_det_sq i
  have habssq : |LinearMap.det (rawShearLinearEquiv i).toLinearMap| ^ 2 = 1 := by
    rw [sq_abs, hsq]
  nlinarith [abs_nonneg (LinearMap.det (rawShearLinearEquiv i).toLinearMap)]

lemma rawShear_measurePreserving (i : Fin n) :
    MeasurePreserving (rawShearLinearEquiv i) volume volume := by
  let e := rawShearLinearEquiv i
  let E : RealVector n ≃L[ℝ] RealVector n := e.toContinuousLinearEquiv
  change MeasurePreserving E volume volume
  have hdet : LinearMap.det (E.toContinuousLinearMap : RealVector n →ₗ[ℝ] RealVector n) ≠ 0 := by
    have hsq : LinearMap.det (E.toContinuousLinearMap : RealVector n →ₗ[ℝ] RealVector n) ^ 2 = 1 := by
      simpa [E, e] using rawShear_det_sq i
    intro hz
    rw [hz] at hsq
    norm_num at hsq
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := (E.toContinuousLinearMap : RealVector n →ₗ[ℝ] RealVector n)) hdet
  have habs : |LinearMap.det (E.toContinuousLinearMap : RealVector n →ₗ[ℝ] RealVector n)| = 1 := by
    simpa [E, e] using rawShear_det_abs i
  have hscale : ENNReal.ofReal |(LinearMap.det
      (E.toContinuousLinearMap : RealVector n →ₗ[ℝ] RealVector n))⁻¹| = 1 := by
    rw [abs_inv, habs]
    norm_num
  refine ⟨E.continuous.measurable, ?_⟩
  rw [hscale] at hmap
  simpa using hmap

/-- Reindex the singleton block of `concatVector` from coordinate zero to `i`. -/
noncomputable def indexPerm (d : ℕ) (i : Fin (d + 1)) :
    Fin (d + 1) ≃ Fin (d + 1) :=
  (finSuccEquiv d).trans (finSuccEquiv' i).symm

noncomputable def coordinatePerm (d : ℕ) (i : Fin (d + 1)) :
    RealVector (d + 1) ≃L[ℝ] RealVector (d + 1) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (d + 1) => ℝ)
    (indexPerm d i)

lemma coordinatePerm_apply_index (d : ℕ) (i : Fin (d + 1))
    (x : RealVector (d + 1)) (j : Fin (d + 1)) :
    coordinatePerm d i x (indexPerm d i j) = x j := by
  change (Equiv.piCongrLeft (fun _ : Fin (d + 1) => ℝ)
    (indexPerm d i) x) (indexPerm d i j) = x j
  exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (d + 1) => ℝ)
    (indexPerm d i) x j

lemma coordinatePerm_measurePreserving (d : ℕ) (i : Fin (d + 1)) :
    MeasurePreserving (coordinatePerm d i) volume volume := by
  change MeasurePreserving
    (fun x : RealVector (d + 1) =>
      Equiv.piCongrLeft (fun _ : Fin (d + 1) => ℝ) (indexPerm d i) x)
    volume volume
  exact volume_measurePreserving_piCongrLeft (fun _ : Fin (d + 1) => ℝ)
    (indexPerm d i)

/-- The corrected coordinate transform in the $A$-to-$\Lambda_1$ change of variables. -/
noncomputable def coordinate (d : ℕ) (i : Fin (d + 1)) :
    RealVector (d + 1) ≃L[ℝ] RealVector (d + 1) :=
  (coordinatePerm d i).trans (rawShearLinearEquiv i).toContinuousLinearEquiv

lemma coordinate_measurePreserving (d : ℕ) (i : Fin (d + 1)) :
    MeasurePreserving (coordinate d i) volume volume := by
  exact (rawShear_measurePreserving i).comp (coordinatePerm_measurePreserving d i)

noncomputable def coordinateToEuclidean (d : ℕ) (i : Fin (d + 1)) :
    RealVector (d + 1) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
  (coordinate d i).trans (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm

lemma coordinateToEuclidean_measurePreserving (d : ℕ) (i : Fin (d + 1)) :
    MeasurePreserving (coordinateToEuclidean d i) volume volume := by
  change MeasurePreserving
    (fun x : RealVector (d + 1) => WithLp.toLp 2 (coordinate d i x)) volume volume
  exact (PiLp.volume_preserving_toLp (Fin (d + 1))).comp
    (coordinate_measurePreserving d i)

noncomputable def transformedFunctions {d : ℕ}
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ := fun i =>
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (coordinateToEuclidean d i) (f i)

lemma transformedFunctions_eLpNorm {d : ℕ}
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (i : Fin (d + 1)) (p : ℝ≥0∞) :
    eLpNorm (transformedFunctions f i) p volume = eLpNorm (f i) p volume := by
  change eLpNorm ((f i) ∘ coordinateToEuclidean d i) p volume =
    eLpNorm (f i) p volume
  exact eLpNorm_comp_measurePreserving (f i).continuous.aestronglyMeasurable
    (coordinateToEuclidean_measurePreserving d i)

lemma indexPerm_zero (d : ℕ) (i : Fin (d + 1)) :
    indexPerm d i 0 = i := by
  simp [indexPerm]

lemma indexPerm_succ (d : ℕ) (i : Fin (d + 1)) (j : Fin d) :
    indexPerm d i j.succ = i.succAbove j := by
  simp [indexPerm]

lemma coordinatePerm_concat (d : ℕ) (i : Fin (d + 1))
    (r : ℝ) (x : RealVector (d + 1)) :
    coordinatePerm d i
      (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)) =
      (i.insertNth r (eraseVector i x) : RealVector (d + 1)) := by
  funext q
  by_cases hq : q = i
  · subst q
    calc
      coordinatePerm d i
          (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)) i =
          coordinatePerm d i
            (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x))
              (indexPerm d i 0) := by rw [indexPerm_zero]
      _ = (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)) 0 :=
        coordinatePerm_apply_index d i _ 0
      _ = r := by simp [concatVector]
      _ = (i.insertNth r (eraseVector i x) : RealVector (d + 1)) i :=
        (Fin.insertNth_apply_same (α := fun _ : Fin (d + 1) => ℝ)
          i r (eraseVector i x)).symm
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    subst q
    calc
      coordinatePerm d i
          (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x))
          (i.succAbove j) =
          coordinatePerm d i
            (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x))
              (indexPerm d i j.succ) := by rw [indexPerm_succ]
      _ = (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)) j.succ :=
        coordinatePerm_apply_index d i _ j.succ
      _ = (eraseVector i x) j := by simp [concatVector]
      _ = (i.insertNth r (eraseVector i x) : RealVector (d + 1)) (i.succAbove j) :=
        (Fin.insertNth_apply_succAbove (α := fun _ : Fin (d + 1) => ℝ)
          i r (eraseVector i x) j).symm

lemma insertNth_eraseVector_apply_ne (d : ℕ) (i q : Fin (d + 1))
    (r : ℝ) (x : RealVector (d + 1)) (hqi : q ≠ i) :
    (i.insertNth r (eraseVector i x) : RealVector (d + 1)) q = x q := by
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hqi
  subst q
  simp [eraseVector]

lemma coordinate_concat (d : ℕ) (i : Fin (d + 1))
    (r : ℝ) (x : RealVector (d + 1)) :
    coordinate d i
      (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)) =
      fun q => if q = i then r + coordinateSum x - x i else -x q := by
  rw [coordinate]
  change rawShear i
    (coordinatePerm d i
      (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x))) = _
  rw [coordinatePerm_concat]
  funext q
  by_cases hqi : q = i
  · subst q
    simp only [rawShear, ite_true]
    change coordinateSum (i.insertNth r (eraseVector i x) : RealVector (d + 1)) =
      r + coordinateSum x - x i
    rw [aux_coordinateSum_insertNth]
    rw [aux_coordinateSum_eraseVector d i x]
    ring
  · simp only [rawShear, if_neg hqi]
    congr 1
    exact insertNth_eraseVector_apply_ne d i q r x hqi

lemma eLpNorm_two_sq_eq_ofReal_integral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ) (hg : Integrable (fun x => g x ^ 2) μ) :
    eLpNorm g 2 μ ^ 2 = ENNReal.ofReal (∫ x, g x ^ 2 ∂μ) := by
  rw [show eLpNorm g 2 μ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ by
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := g)
      (p := (2 : NNReal)) (by norm_num : (2 : NNReal) ≠ 0)
    simpa [ENNReal.rpow_two] using h]
  rw [ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ fun x => sq_nonneg (g x))]
  apply lintegral_congr_ae
  filter_upwards [] with x
  calc
    ‖g x‖ₑ ^ (2 : ℝ) = (ENNReal.ofReal |g x|) ^ (2 : ℝ) := by
      rw [Real.enorm_eq_ofReal_abs]
    _ = ENNReal.ofReal (|g x| ^ (2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two]
    _ = ENNReal.ofReal (g x ^ 2) := by
      congr 1
      rw [Real.rpow_two, sq_abs]

lemma coordinate_concat_eq_neg_add_single (d : ℕ) (i : Fin (d + 1))
    (r : ℝ) (x : RealVector (d + 1)) :
    coordinate d i
      (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)) =
      -x + (r + coordinateSum x) • Pi.single i (1 : ℝ) := by
  rw [coordinate_concat]
  funext q
  by_cases hq : q = i
  · subst q
    simp
    ring
  · simp [hq]

lemma transformedFunctions_concat {d : ℕ}
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (i : Fin (d + 1)) (r : ℝ) (x : RealVector (d + 1)) :
    transformedFunctions f i
      (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)) =
      f i (WithLp.toLp 2 (-x + (r + coordinateSum x) • Pi.single i (1 : ℝ))) := by
  change f i (coordinateToEuclidean d i
    (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x))) = _
  change f i (WithLp.toLp 2 (coordinate d i
    (concatVector (d + 1) 1 (by omega) (fun _ : Fin 1 => r) (eraseVector i x)))) = _
  rw [coordinate_concat_eq_neg_add_single]

lemma prismIndex_one (d : ℕ) (i : Fin (d + 1)) :
    prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i = i := by
  apply Fin.ext
  simp [prismIndex]

lemma schwartzMap_memW0_real (phi : SchwartzMap ℝ ℝ) : Codex.MemW0 phi := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let Phi : SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e phi
  have hPhi : Codex.MemW0 Phi := Codex.SchwartzMap.memW0 Phi
  have hraw := aux_memW0_comp_continuousLinearEquiv hPhi e.symm
  convert hraw using 1
  funext x
  change phi x = phi (e (e.symm x))
  rw [e.apply_symm_apply]

lemma oneTensorSquare_memW0 (phi : SchwartzMap ℝ ℝ) :
    Codex.MemW0 (fun y : RealVector 1 × RealVector 1 =>
      phi (y.1 0) * phi (y.2 0)) := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (RealVector 1)) :=
    isAddHaarMeasure_volume_pi (Fin 1)
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  letI : Measure.IsAddHaarMeasure
      (volume : Measure (RealVector 1 × RealVector 1)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let e : RealVector 1 ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)
  let E : (RealVector 1 × RealVector 1) ≃L[ℝ] (ℝ × ℝ) := e.prodCongr e
  have hphi : Codex.MemW0 phi := schwartzMap_memW0_real phi
  have htensor : Codex.MemW0 (tensorSquare phi) :=
    aux_memW0_tensorSquare phi hphi
  have hraw := aux_memW0_comp_continuousLinearEquiv htensor E
  convert hraw using 1
  funext y
  simp [E, e, tensorSquare]

lemma mToK_oneTensorSquare_eq (phi : SchwartzMap ℝ ℝ)
    (u : RealVector 1 × ℝ) :
    mToK 1 (by omega) (fun y : RealVector 1 × RealVector 1 =>
      phi (y.1 0) * phi (y.2 0)) u =
      phi (u.1 0 + u.2) * phi u.2 := by
  unfold mToK
  rw [aux_integral_realVector_zero]
  simp [mToKPoint, lastIndex, coordinateSum]

def rawTwistedFactor {d : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (x : RealVector (d + 1)) (r : ℝ) : ℝ :=
  phi r * ∏ i, f i (WithLp.toLp 2 (x + r • Pi.single i (1 : ℝ)))

lemma rankOneFactor_transformedFunctions {d : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (x : RealVector (d + 1)) (r : ℝ) :
    aux_rankOneFactor (d + 1) (by omega) phi (transformedFunctions f) x r =
      rawTwistedFactor phi f (-x) (r + coordinateSum x) := by
  unfold aux_rankOneFactor rawTwistedFactor
  congr 1
  apply Fintype.prod_congr
  intro i
  rw [prismIndex_one]
  rw [transformedFunctions_concat]

def globalChange (d : ℕ) :
    RealVector (d + 1) × (ℝ × ℝ) → RealVector (d + 1) × (ℝ × ℝ) :=
  fun q => (-q.1, (q.2.1 + coordinateSum q.1, q.2.2 + coordinateSum q.1))

lemma coordinateSum_neg (d : ℕ) (x : RealVector d) :
    coordinateSum (-x) = -coordinateSum x := by
  simp [coordinateSum, Finset.sum_neg_distrib]

lemma globalChange_involutive (d : ℕ)
    (q : RealVector (d + 1) × (ℝ × ℝ)) :
    globalChange d (globalChange d q) = q := by
  rcases q with ⟨x, r, s⟩
  apply Prod.ext
  · simp [globalChange]
  · apply Prod.ext <;> simp [globalChange, coordinateSum_neg] <;> ring

lemma globalChange_measurePreserving (d : ℕ) :
    MeasurePreserving (globalChange d) volume volume := by
  let A := RealVector (d + 1)
  have hneg : MeasurePreserving (fun x : A => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hnegProd : MeasurePreserving
      (fun q : A × (ℝ × ℝ) => (-q.1, q.2)) volume volume := by
    change MeasurePreserving
      (Prod.map (fun x : A => -x) (id : ℝ × ℝ → ℝ × ℝ)) volume volume
    simpa only [Measure.volume_eq_prod, id_eq] using
      hneg.prod (MeasurePreserving.id (volume : Measure (ℝ × ℝ)))
  have hshearProd : MeasurePreserving
      (fun q : A × (ℝ × ℝ) =>
        (q.1, (q.2.1 - coordinateSum q.1, q.2.2 - coordinateSum q.1)))
      ((volume : Measure A).prod (volume : Measure (ℝ × ℝ)))
      ((volume : Measure A).prod (volume : Measure (ℝ × ℝ))) := by
    refine MeasurePreserving.skew_product
      (μa := (volume : Measure A)) (μb := (volume : Measure A))
      (μc := (volume : Measure (ℝ × ℝ))) (μd := (volume : Measure (ℝ × ℝ)))
      (f := id) (g := fun x y =>
        (y.1 - coordinateSum x, y.2 - coordinateSum x))
      (MeasurePreserving.id (volume : Measure A)) ?_ ?_
    · exact
        (((continuous_fst.comp continuous_snd).sub
          ((aux_continuous_coordinateSum (d + 1)).comp continuous_fst)).prodMk
          ((continuous_snd.comp continuous_snd).sub
            ((aux_continuous_coordinateSum (d + 1)).comp continuous_fst))).measurable
    · filter_upwards [] with x
      have htranslate : MeasurePreserving
          (fun r : ℝ => r - coordinateSum x) volume volume := by
        simpa [sub_eq_add_neg] using
          (measurePreserving_add_right (volume : Measure ℝ) (-coordinateSum x))
      have hpair : MeasurePreserving
          (fun y : ℝ × ℝ =>
            (y.1 - coordinateSum x, y.2 - coordinateSum x)) volume volume := by
        change MeasurePreserving
          (Prod.map (fun r : ℝ => r - coordinateSum x)
            (fun r : ℝ => r - coordinateSum x)) volume volume
        simpa only [Measure.volume_eq_prod] using htranslate.prod htranslate
      exact hpair.map_eq
  have hshear : MeasurePreserving
      (fun q : A × (ℝ × ℝ) =>
        (q.1, (q.2.1 - coordinateSum q.1, q.2.2 - coordinateSum q.1)))
      volume volume := by
    simpa only [Measure.volume_eq_prod] using hshearProd
  have htotal := hshear.comp hnegProd
  convert htotal using 1
  funext q
  rcases q with ⟨x, r, s⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change r + coordinateSum x = r - coordinateSum (-x)
      rw [coordinateSum_neg]
      ring
    · change s + coordinateSum x = s - coordinateSum (-x)
      rw [coordinateSum_neg]
      ring

lemma globalChange_integral_comp (d : ℕ)
    (g : RealVector (d + 1) × (ℝ × ℝ) → ℝ)
    (hg : Integrable g) :
    (∫ q, g (globalChange d q)) = ∫ q, g q := by
  let h := globalChange_measurePreserving d
  have hmeas : AEStronglyMeasurable g (Measure.map (globalChange d) volume) := by
    rw [h.map_eq]
    exact hg.aestronglyMeasurable
  calc
    (∫ q, g (globalChange d q)) =
        ∫ q, g q ∂Measure.map (globalChange d) volume :=
      (MeasureTheory.integral_map h.measurable.aemeasurable hmeas).symm
    _ = ∫ q, g q := by rw [h.map_eq]

def rawTwistedSquareIntegrand {d : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (q : RealVector (d + 1) × (ℝ × ℝ)) : ℝ :=
  rawTwistedFactor phi f q.1 q.2.1 * rawTwistedFactor phi f q.1 q.2.2

lemma rankOneRawIntegrand_eq_global {d : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (p : (RealVector 1 × RealVector 1) × RealVector (d + 1)) :
    aux_rankOneRawIntegrand (d + 1) (by omega) 1 phi
      (transformedFunctions f) p =
      rawTwistedSquareIntegrand phi f
        (globalChange d (aux_baseReorderOne (d + 1) p)) := by
  rw [aux_baseReorderOne_apply]
  unfold aux_rankOneRawIntegrand rawTwistedSquareIntegrand globalChange
  rw [rankOneFactor_transformedFunctions]
  rw [rankOneFactor_transformedFunctions]
  ring

lemma rawTwistedSquareIntegrand_integrable {d : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    Integrable (rawTwistedSquareIntegrand phi f) := by
  let F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ :=
    transformedFunctions f
  let M : MKernel 1 := fun y => phi (y.1 0) * phi (y.2 0)
  let K : KKernel 1 := mToK 1 (by omega) M
  have hM : Codex.MemW0 M := by
    simpa [M] using oneTensorSquare_memW0 phi
  have hKmem : Codex.MemW0 K := by
    simpa [K] using mToK_memW0 (d + 1) 1 (by omega) (by omega) M hM
  have hK : ∀ u : RealVector 1 × ℝ,
      K u = phi (u.1 0 + u.2) * phi u.2 := by
    intro u
    simpa [K, M] using mToK_oneTensorSquare_eq phi u
  let H : (RealVector 1 × RealVector 1) × RealVector (d + 1) → ℝ :=
    fun p => K (p.1.2 - p.1.1, coordinateSum p.1.1 + coordinateSum p.2) *
      ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
        F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
          (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) p.1 p.2 h i)
  have hH : Integrable H := by
    simpa [H] using aux_integrable_prismIntegrand (d + 1) 1 (by omega) (by omega)
      K hKmem F
  let G : RealVector (d + 1) × (ℝ × ℝ) → ℝ :=
    fun q => rawTwistedSquareIntegrand phi f (globalChange d q)
  have hpoint (p : (RealVector 1 × RealVector 1) × RealVector (d + 1)) :
      H p = G (aux_baseReorderOne (d + 1) p) := by
    have hraw := aux_prism_one_integrand_eq_rankOneRaw (d + 1) (by omega) 1 phi F K
      (by intro u; simpa using hK u) p
    have hraw' : H p = aux_rankOneRawIntegrand (d + 1) (by omega) 1 phi F p := by
      dsimp [H]
      convert hraw using 1 <;> simp
    rw [hraw']
    dsimp [G]
    simpa [F] using rankOneRawIntegrand_eq_global phi f p
  have hGcomp : Integrable (G ∘ aux_baseReorderOne (d + 1)) := by
    refine hH.congr ?_
    filter_upwards [] with p
    exact hpoint p
  have hG : Integrable G := by
    let e := aux_baseReorderOne (d + 1)
    have hinv : MeasurePreserving e.symm volume volume :=
      (aux_measurePreserving_baseReorderOne (d + 1)).symm e
    have h := hinv.integrable_comp_of_integrable hGcomp
    refine h.congr ?_
    filter_upwards [] with q
    simp [e, Function.comp_def]
  have hIcomp := (globalChange_measurePreserving d).integrable_comp_of_integrable hG
  refine hIcomp.congr ?_
  filter_upwards [] with q
  change G (globalChange d q) = rawTwistedSquareIntegrand phi f q
  dsimp [G]
  rw [globalChange_involutive]

def rawTwistedAverage {d : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (x : RealVector (d + 1)) : ℝ :=
  ∫ r : ℝ, rawTwistedFactor phi f x r

lemma rawTwistedAverage_sq_fubini {d : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    Integrable (fun x => rawTwistedAverage phi f x ^ 2) ∧
      (∫ x, rawTwistedAverage phi f x ^ 2) =
        ∫ q, rawTwistedSquareIntegrand phi f q := by
  have hI : Integrable (rawTwistedSquareIntegrand phi f) :=
    rawTwistedSquareIntegrand_integrable phi f
  have hIprod : Integrable (rawTwistedSquareIntegrand phi f)
      ((volume : Measure (RealVector (d + 1))).prod (volume : Measure (ℝ × ℝ))) := by
    simpa only [Measure.volume_eq_prod] using hI
  have hinner := hIprod.integral_prod_left
  have hinnerEq (x : RealVector (d + 1)) :
      (∫ y : ℝ × ℝ, rawTwistedSquareIntegrand phi f (x, y)) =
        rawTwistedAverage phi f x ^ 2 := by
    unfold rawTwistedSquareIntegrand rawTwistedAverage
    change (∫ y : ℝ × ℝ,
      rawTwistedFactor phi f x y.1 * rawTwistedFactor phi f x y.2) = _
    rw [show (∫ y : ℝ × ℝ,
      rawTwistedFactor phi f x y.1 * rawTwistedFactor phi f x y.2) =
        (∫ r : ℝ, rawTwistedFactor phi f x r) *
          (∫ r : ℝ, rawTwistedFactor phi f x r) by
      simpa only [Measure.volume_eq_prod] using
        (integral_prod_mul (rawTwistedFactor phi f x) (rawTwistedFactor phi f x))]
    ring
  have hsq : Integrable (fun x => rawTwistedAverage phi f x ^ 2) := by
    refine hinner.congr ?_
    filter_upwards [] with x
    exact hinnerEq x
  refine ⟨hsq, ?_⟩
  calc
    (∫ x, rawTwistedAverage phi f x ^ 2) =
        ∫ x, ∫ y : ℝ × ℝ, rawTwistedSquareIntegrand phi f (x, y) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact (hinnerEq x).symm
    _ = ∫ q, rawTwistedSquareIntegrand phi f q := by
      simpa only [Measure.volume_eq_prod] using
        (integral_prod (rawTwistedSquareIntegrand phi f) hIprod).symm

lemma twistedAverage_toLp_eq_rawTwistedAverage {d : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (x : RealVector (d + 1)) :
    twistedAverage phi (fun i z => f i z) (WithLp.toLp 2 x) =
      rawTwistedAverage phi f x := by
  unfold twistedAverage rawTwistedAverage rawTwistedFactor
  apply integral_congr_ae
  filter_upwards [] with r
  congr 1

lemma rawTwistedSquareIntegrand_integral_eq_prismForm {d : ℕ}
    (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    (∫ q, rawTwistedSquareIntegrand phi f q) =
      prismForm (d + 1) 1 (by omega) (by omega)
        (fun y => phi (y.1 0) * phi (y.2 0))
        (fun i x => transformedFunctions f i x) := by
  let F : Fin (d + 1) → SchwartzMap (RealVector (d + 1)) ℝ :=
    transformedFunctions f
  let M : MKernel 1 := fun y => phi (y.1 0) * phi (y.2 0)
  let K : KKernel 1 := mToK 1 (by omega) M
  have hM : Codex.MemW0 M := by
    simpa [M] using oneTensorSquare_memW0 phi
  have hKmem : Codex.MemW0 K := by
    simpa [K] using mToK_memW0 (d + 1) 1 (by omega) (by omega) M hM
  have hK : ∀ u : RealVector 1 × ℝ,
      K u = phi (u.1 0 + u.2) * phi u.2 := by
    intro u
    simpa [K, M] using mToK_oneTensorSquare_eq phi u
  let H : (RealVector 1 × RealVector 1) × RealVector (d + 1) → ℝ :=
    fun p => K (p.1.2 - p.1.1, coordinateSum p.1.1 + coordinateSum p.2) *
      ∏ h : Fin 1 → Fin 2, ∏ i : Fin (d + 1),
        F (prismIndex (n := d + 1) (k := 1) (by omega) (by omega) i)
          (prismPoint (n := d + 1) (k := 1) (by omega) (by omega) p.1 p.2 h i)
  have hH : Integrable H := by
    simpa [H] using aux_integrable_prismIntegrand (d + 1) 1 (by omega) (by omega)
      K hKmem F
  have hpoint (p : (RealVector 1 × RealVector 1) × RealVector (d + 1)) :
      H p = rawTwistedSquareIntegrand phi f
        (globalChange d (aux_baseReorderOne (d + 1) p)) := by
    have hraw := aux_prism_one_integrand_eq_rankOneRaw (d + 1) (by omega) 1 phi F K
      (by intro u; simpa using hK u) p
    have hraw' : H p = aux_rankOneRawIntegrand (d + 1) (by omega) 1 phi F p := by
      dsimp [H]
      convert hraw using 1 <;> simp
    rw [hraw']
    simpa [F] using rankOneRawIntegrand_eq_global phi f p
  have hI : Integrable (rawTwistedSquareIntegrand phi f) :=
    rawTwistedSquareIntegrand_integrable phi f
  have hcalc : (∫ q, rawTwistedSquareIntegrand phi f q) =
      prismBrascampLiebForm (d + 1) 1 (by omega) (by omega) K
        (fun i x => F i x) := by
    change (∫ q, rawTwistedSquareIntegrand phi f q) =
      ∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1), H (y, x)
    calc
      (∫ q, rawTwistedSquareIntegrand phi f q) =
          ∫ q, rawTwistedSquareIntegrand phi f (globalChange d q) :=
        (globalChange_integral_comp d (rawTwistedSquareIntegrand phi f) hI).symm
      _ = ∫ p, rawTwistedSquareIntegrand phi f
          (globalChange d (aux_baseReorderOne (d + 1) p)) :=
        ((aux_measurePreserving_baseReorderOne (d + 1)).integral_comp'
          (fun q => rawTwistedSquareIntegrand phi f (globalChange d q))).symm
      _ = ∫ p, H p := by
        apply integral_congr_ae
        filter_upwards [] with p
        exact (hpoint p).symm
      _ = ∫ y : RealVector 1 × RealVector 1, ∫ x : RealVector (d + 1), H (y, x) := by
        simpa only [Measure.volume_eq_prod] using (integral_prod H hH)
  simpa [prismForm, F, M, K] using hcalc

lemma toLp_integral_comp {d : ℕ}
    (g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
    (hg : Integrable g) :
    (∫ x : RealVector (d + 1), g (WithLp.toLp 2 x)) = ∫ z, g z := by
  let h := PiLp.volume_preserving_toLp (Fin (d + 1))
  have hmeas : AEStronglyMeasurable g (Measure.map (WithLp.toLp 2) volume) := by
    rw [h.map_eq]
    exact hg.aestronglyMeasurable
  calc
    (∫ x : RealVector (d + 1), g (WithLp.toLp 2 x)) =
        ∫ z, g z ∂Measure.map (WithLp.toLp 2) volume :=
      (MeasureTheory.integral_map h.measurable.aemeasurable hmeas).symm
    _ = ∫ z, g z := by rw [h.map_eq]

end aux_aToLambda

open aux_aToLambda

/- The canonical form of the change-of-variables identity.  Unlike the public
existential formulation below, this fixes the transformed tuple once and for all,
which is needed when several kernels are considered simultaneously. -/
private theorem aux_aToLambda_explicit {d : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    eLpNorm (twistedAverage phi (fun i x ↦ f i x)) 2 volume ^ 2 =
      ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (fun y ↦ phi (y.1 0) * phi (y.2 0))
          (fun i x ↦ transformedFunctions f i x)) := by
  have hRaw := rawTwistedAverage_sq_fubini phi f
  have hT2 : Integrable (fun z : EuclideanSpace ℝ (Fin (d + 1)) =>
      twistedAverage phi (fun i x => f i x) z ^ 2) := by
    have hcomp :=
      (PiLp.volume_preserving_ofLp (Fin (d + 1))).integrable_comp_of_integrable hRaw.1
    refine hcomp.congr ?_
    filter_upwards [] with z
    change rawTwistedAverage phi f z.ofLp ^ 2 =
      twistedAverage phi (fun i x => f i x) z ^ 2
    rw [← twistedAverage_toLp_eq_rawTwistedAverage phi f z.ofLp,
      WithLp.toLp_ofLp]
  have hTInt :
      (∫ z : EuclideanSpace ℝ (Fin (d + 1)),
        twistedAverage phi (fun i x => f i x) z ^ 2) =
        ∫ x : RealVector (d + 1), rawTwistedAverage phi f x ^ 2 := by
      calc
        (∫ z : EuclideanSpace ℝ (Fin (d + 1)),
            twistedAverage phi (fun i x => f i x) z ^ 2) =
            ∫ x : RealVector (d + 1),
              twistedAverage phi (fun i z => f i z) (WithLp.toLp 2 x) ^ 2 :=
          (toLp_integral_comp (fun z : EuclideanSpace ℝ (Fin (d + 1)) =>
            twistedAverage phi (fun i x => f i x) z ^ 2) hT2).symm
        _ = ∫ x : RealVector (d + 1), rawTwistedAverage phi f x ^ 2 := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [twistedAverage_toLp_eq_rawTwistedAverage phi f x]
  calc
    eLpNorm (twistedAverage phi (fun i x => f i x)) 2 volume ^ 2 =
        ENNReal.ofReal (∫ z : EuclideanSpace ℝ (Fin (d + 1)),
          twistedAverage phi (fun i x => f i x) z ^ 2) :=
      eLpNorm_two_sq_eq_ofReal_integral_sq volume _ hT2
    _ = ENNReal.ofReal (∫ x : RealVector (d + 1), rawTwistedAverage phi f x ^ 2) := by
      rw [hTInt]
    _ = ENNReal.ofReal (∫ q, rawTwistedSquareIntegrand phi f q) := by
      rw [hRaw.2]
    _ = ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (fun y => phi (y.1 0) * phi (y.2 0))
          (fun i x => transformedFunctions f i x)) := by
      rw [rawTwistedSquareIntegrand_integral_eq_prismForm phi f]

/--
\begin{lemma}[$A$ to $\Lambda_1$]\label{A to Lambda}
Let $\phi\in \mathcal{S}(\R)$ and let
$\mathbf f=(f_0,\dots,f_{n-1})$ consist of functions in $\mathcal S(\R^n)$.
Then $\|A(\phi,\mathbf f)\|_2^2=\Lambda_1(\phi^{\otimes2})(\mathbf F)$,
where $F_i$ is the manuscript's determinant-one coordinate transform of
$f_i$.  Each $F_i$ is Schwartz and has the same $L^p$ norms as $f_i$.
\end{lemma}
-/
theorem aToLambda {n : ℕ} (hn : 1 ≤ n) (phi : SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    ∃ F : Fin n → SchwartzMap (RealVector n) ℝ,
      (∀ i, ∀ p : ℝ≥0∞, eLpNorm (F i) p volume = eLpNorm (f i) p volume) ∧
      eLpNorm (twistedAverage phi (fun i x ↦ f i x)) 2 volume ^ 2 =
        ENNReal.ofReal
          (prismForm n 1 (by omega) hn
            (fun y ↦ phi (y.1 0) * phi (y.2 0))
            (fun i x ↦ F i x)) := by
  cases n with
  | zero => omega
  | succ d =>
      refine ⟨transformedFunctions f, ?_, ?_⟩
      · intro i p
        exact transformedFunctions_eLpNorm f i p
      · simpa using aux_aToLambda_explicit phi f

/-- The canonical, scale-independent successor-dimensional form of the
`A`-to-`Λ₁` identity.  Unlike `aToLambda`, this fixes
`transformedFunctions f` explicitly, which is needed when the kernel varies
under an integral or a parameterized family. -/
theorem aToLambda_transformed {d : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    eLpNorm (twistedAverage phi (fun i x ↦ f i x)) 2 volume ^ 2 =
      ENNReal.ofReal
        (prismForm (d + 1) 1 (by omega) (by omega)
          (fun y ↦ phi (y.1 0) * phi (y.2 0))
          (fun i x ↦ transformedFunctions f i x)) := by
  simpa using aux_aToLambda_explicit phi f

/- The tensor-square prism form in the canonical `A`-to-`Λ₁` reduction is a
square integral, hence nonnegative. -/
private lemma aux_aToLambda_explicit_prism_nonneg {d : ℕ} (phi : SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    0 ≤ prismForm (d + 1) 1 (by omega) (by omega)
      (fun y ↦ phi (y.1 0) * phi (y.2 0))
      (fun i x ↦ transformedFunctions f i x) := by
  rw [← rawTwistedSquareIntegrand_integral_eq_prismForm phi f]
  rw [← (rawTwistedAverage_sq_fubini phi f).2]
  exact integral_nonneg fun _ ↦ sq_nonneg _

/- Finite linearity of the first prism form for the special tensor-square
kernels arising from the `A`-to-`Λ₁` change of variables. -/
private lemma aux_aToLambda_prismForm_fin_sum {d J : ℕ}
    (phi : Fin J → SchwartzMap ℝ ℝ)
    (f : Fin (d + 1) → SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ) :
    prismForm (d + 1) 1 (by omega) (by omega)
      (fun y ↦ ∑ j, phi j (y.1 0) * phi j (y.2 0))
      (fun i x ↦ transformedFunctions f i x) =
      ∑ j, prismForm (d + 1) 1 (by omega) (by omega)
        (fun y ↦ phi j (y.1 0) * phi j (y.2 0))
        (fun i x ↦ transformedFunctions f i x) := by
  have hM (j : Fin J) : MemW0 (fun y : RealVector 1 × RealVector 1 =>
      phi j (y.1 0) * phi j (y.2 0)) :=
    oneTensorSquare_memW0 (phi j)
  have hK (j : Fin J) : MemW0 (mToK 1 (by omega)
      (fun y : RealVector 1 × RealVector 1 => phi j (y.1 0) * phi j (y.2 0))) :=
    mToK_memW0 (d + 1) 1 (by omega) (by omega) _ (hM j)
  unfold prismForm
  rw [aux_mToK_finset_sum 1 J (by omega)
    (fun j y => phi j (y.1 0) * phi j (y.2 0)) hM]
  rw [aux_prismBrascampLiebForm_finset_sum (d + 1) 1 J (by omega) (by omega)
    (fun j => mToK 1 (by omega)
      (fun y => phi j (y.1 0) * phi j (y.2 0))) hK]

/--
A finite-family version of `aToLambda`. It uses one common determinant-one
coordinate transform of `f` for every kernel, so a finite square sum of
twisted averages becomes a single first prism form.
-/
theorem aToLambda_fin_sum {n J : ℕ} (hn : 1 ≤ n)
    (phi : Fin J → SchwartzMap ℝ ℝ)
    (f : Fin n → SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    ∃ F : Fin n → SchwartzMap (RealVector n) ℝ,
      (∀ i, ∀ p : ℝ≥0∞, eLpNorm (F i) p volume = eLpNorm (f i) p volume) ∧
      (∑ j, eLpNorm (twistedAverage (phi j) (fun i x ↦ f i x)) 2 volume ^ 2) =
        ENNReal.ofReal
          (prismForm n 1 (by omega) hn
            (fun y ↦ ∑ j, phi j (y.1 0) * phi j (y.2 0))
            (fun i x ↦ F i x)) := by
  cases n with
  | zero => omega
  | succ d =>
    refine ⟨transformedFunctions f, ?_, ?_⟩
    · intro i p
      exact transformedFunctions_eLpNorm f i p
    · calc
        (∑ j, eLpNorm (twistedAverage (phi j) (fun i x ↦ f i x)) 2 volume ^ 2) =
            ∑ j, ENNReal.ofReal
              (prismForm (d + 1) 1 (by omega) hn
                (fun y ↦ phi j (y.1 0) * phi j (y.2 0))
                (fun i x ↦ transformedFunctions f i x)) := by
              apply Finset.sum_congr rfl
              intro j _
              simpa using aux_aToLambda_explicit (phi j) f
        _ = ENNReal.ofReal
            (∑ j, prismForm (d + 1) 1 (by omega) hn
              (fun y ↦ phi j (y.1 0) * phi j (y.2 0))
              (fun i x ↦ transformedFunctions f i x)) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro j _
            simpa using aux_aToLambda_explicit_prism_nonneg (phi j) f
        _ = ENNReal.ofReal
            (prismForm (d + 1) 1 (by omega) hn
              (fun y ↦ ∑ j, phi j (y.1 0) * phi j (y.2 0))
              (fun i x ↦ transformedFunctions f i x)) := by
            rw [aux_aToLambda_prismForm_fin_sum phi f]

end

end Codex.Reduction.AToLambda
