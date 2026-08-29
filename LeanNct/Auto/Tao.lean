/- This file was machine generated -/

module

public import LeanNct.Auto.RealToErgodic
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Tao's norm-convergence theorem

This file proves Tao's theorem on norm convergence of multiple ergodic
averages.  The one-transformation case is proved using von Neumann's mean
ergodic theorem, and the remaining cases follow from the Auto implementation
of the main ergodic theorem.
-/

@[expose] public noncomputable section

namespace Auto

open Filter MeasureTheory
open scoped Topology ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-
Mathlib already contains von Neumann's mean ergodic theorem as
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`.
The following private bridge only identifies its Birkhoff averages with the
project's one-transformation multiple ergodic averages.
-/
private theorem one_transform_converges
    (T : Fin 1 → X → X) (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (f : Fin 1 → X → ℂ) (hf : ∀ i, MemLp (f i) 2 μ) :
    ∃ g : X → ℂ, MemLp g 2 μ ∧
      Tendsto (fun N => eLpNorm (nCT.multipleErgodicAverage f T N - g) 2 μ)
        atTop (𝓝 0) := by
  let S : aux_ErgodicSystem X μ 1 := {
    transformation := T
    measurePreserving := hT
    commutes := by
      intro i j x
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      rfl }
  let hf' : ∀ i, MemLp (f i) (2 * ((1 : ℕ) : ℝ≥0∞)) μ := by
    intro i
    convert hf i using 1 ; norm_num
  let U : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℂ (T 0) (hT 0)).toContinuousLinearMap
  let gLp : Lp ℂ 2 μ :=
    (U.eqLocus (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)).orthogonalProjectionOnto
      ((hf 0).toLp (f 0))
  have haverage (N : ℕ) :
      nCT.multipleErgodicAverage f T N = aux_ergodicAverage S N f := by
    simpa [S] using aux_nCT_multipleErgodicAverage_eq_aux_ergodicAverage S f (N := N)
  have hmem (N : ℕ) : MemLp (nCT.multipleErgodicAverage f T N) 2 μ := by
    rw [haverage]
    exact aux_ergodicAverage_memLp_two (by omega) S f hf'
  have hiterate (m : ℕ) :
      U^[m] ((hf 0).toLp (f 0) : Lp ℂ 2 μ) =
        ((hf 0).comp_measurePreserving ((hT 0).iterate m)).toLp
          (fun x => f 0 ((T 0)^[m] x)) := by
    change (Lp.compMeasurePreserving (T 0) (hT 0))^[m]
      ((hf 0).toLp (f 0)) = _
    rw [Lp.compMeasurePreserving_iterate, Lp.toLp_compMeasurePreserving]
    rfl
  have hterm₀ (m : ℕ) :
      (fun x => f 0 ((T 0)^[m] x)) =ᵐ[μ]
        fun x => (U^[m] ((hf 0).toLp (f 0) : Lp ℂ 2 μ)) x := by
    rw [hiterate m]
    exact (MemLp.coeFn_toLp
      ((hf 0).comp_measurePreserving ((hT 0).iterate m))).symm
  have hterm (m : ℕ) :
      (fun x => ∏ i, f i ((S.transformation i)^[m] x)) =ᵐ[μ]
        fun x => (U^[m] ((hf 0).toLp (f 0) : Lp ℂ 2 μ)) x := by
    simpa [S] using hterm₀ m
  have hsumTerms (N : ℕ) :
      (∑ m ∈ Finset.range N, fun x => ∏ i, f i ((S.transformation i)^[m] x)) =ᵐ[μ]
        ∑ m ∈ Finset.range N,
          fun x => (U^[m] ((hf 0).toLp (f 0) : Lp ℂ 2 μ)) x :=
    eventuallyEq_sum (s := Finset.range N) fun m _ => hterm m
  have hLpAverage (N : ℕ) :
      (hmem N).toLp (nCT.multipleErgodicAverage f T N) =
        birkhoffAverage ℂ U id N ((hf 0).toLp (f 0)) := by
    let haux : MemLp (aux_ergodicAverage S N f) 2 μ :=
      aux_ergodicAverage_memLp_two (by omega) S f hf'
    calc
      (hmem N).toLp (nCT.multipleErgodicAverage f T N) =
          haux.toLp (aux_ergodicAverage S N f) :=
        MemLp.toLp_congr (hmem N) haux (Filter.EventuallyEq.of_eq (haverage N))
      _ = aux_ergodicAverageLp (by omega) S f hf' N := by rfl
      _ = birkhoffAverage ℂ U id N ((hf 0).toLp (f 0)) := by
        apply Lp.ext
        have hleft :
            (aux_ergodicAverageLp (by omega) S f hf' N : X → ℂ) =ᵐ[μ]
              aux_ergodicAverage S N f :=
          MemLp.coeFn_toLp (aux_ergodicAverage_memLp_two (by omega) S f hf')
        rw [birkhoffAverage, birkhoffSum]
        filter_upwards [hleft,
          Lp.coeFn_smul ((N : ℂ)⁻¹)
            (∑ m ∈ Finset.range N, U^[m] ((hf 0).toLp (f 0))),
          Lp.coeFn_finsetSum (Finset.range N) fun m =>
            U^[m] ((hf 0).toLp (f 0)),
          hsumTerms N] with x hx hsmul hsum hsumTerms
        simp only [id_eq]
        rw [hx, hsmul]
        simp only [Pi.smul_apply]
        rw [hsum]
        unfold aux_ergodicAverage
        simp only [smul_eq_mul]
        simp only [Finset.sum_apply]
        simp only [Finset.sum_apply] at hsumTerms
        rw [hsumTerms]
  have hU : ‖U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖Lp.compMeasurePreserving (T 0) (hT 0) x‖ ≤ 1 * ‖x‖
    simp
  have hmean : Tendsto
      (birkhoffAverage ℂ U id · ((hf 0).toLp (f 0))) atTop (𝓝 gLp) := by
    dsimp [gLp]
    exact ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
      U hU ((hf 0).toLp (f 0))
  have hconverges : Tendsto
      (fun N => (hmem N).toLp (nCT.multipleErgodicAverage f T N)) atTop (𝓝 gLp) := by
    simpa only [hLpAverage] using hmean
  refine ⟨(gLp : X → ℂ), Lp.memLp gLp, ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (nCT.multipleErgodicAverage f T) hmem (gLp : X → ℂ) (Lp.memLp gLp)).mp
  simpa using hconverges

private theorem cauchySeq_of_variationSeminorm_lt_top
    {B : Type*} [NormedAddCommGroup B] (a : ℕ → B) {r : ℝ} (hr : 0 < r)
    (hvariation : nCT.variationSeminorm (fun b => ‖b‖ₑ) r a < ∞) :
    CauchySeq a := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  by_contra htail
  push Not at htail
  have hstep (N : ℕ) : ∃ m, N < m ∧ ε ≤ dist (a m) (a N) := by
    rcases htail N with ⟨m, hm, hdist⟩
    refine ⟨m, ?_, hdist⟩
    refine lt_of_le_of_ne hm ?_
    intro hEq
    subst m
    have : ε ≤ 0 := by simpa using hdist
    linarith
  choose next hnext using hstep
  let k : ℕ → ℕ := fun i => next^[i] 1
  have hk_succ (i : ℕ) : k i < k (i + 1) := by
    change next^[i] 1 < next^[i.succ] 1
    rw [Function.iterate_succ_apply']
    exact (hnext _).1
  have hk_strict : StrictMono k := strictMono_nat_of_lt_succ hk_succ
  have hk_pos (i : ℕ) : 0 < k i := by
    have hzero : k 0 = 1 := by simp [k]
    calc
      0 < 1 := Nat.zero_lt_one
      _ = k 0 := hzero.symm
      _ ≤ k i := hk_strict.monotone (Nat.zero_le i)
  have hk_jump (i : ℕ) : ε ≤ dist (a (k (i + 1))) (a (k i)) := by
    change ε ≤ dist (a (next^[i.succ] 1)) (a (next^[i] 1))
    rw [Function.iterate_succ_apply']
    exact (hnext _).2
  let V : ℝ≥0∞ := nCT.variationSeminorm (fun b => ‖b‖ₑ) r a
  let δ : ℝ≥0∞ := ENNReal.ofReal ε
  have hδpos : 0 < δ := ENNReal.ofReal_pos.mpr hε
  have hδrpos : 0 < δ ^ r := ENNReal.rpow_pos hδpos ENNReal.ofReal_ne_top
  have hbound (J : ℕ) : (J : ℝ≥0∞) * δ ^ r ≤ V ^ r := by
    let t : Fin (J + 1) → ℕ := fun j => k j
    have ht : StrictMono t := by
      intro i j hij
      exact hk_strict hij
    have htpos : ∀ j, 0 < t j := fun j => hk_pos j
    let E : ℝ≥0∞ := ∑ j : Fin J,
      ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ r
    have hroot : E ^ r⁻¹ ≤ V := by
      dsimp [E, V]
      unfold nCT.variationSeminorm
      exact le_iSup_of_le J <|
        le_iSup_of_le ⟨t, ⟨ht, htpos⟩⟩ le_rfl
    have hupper : E ≤ V ^ r := by
      calc
        E = (E ^ r⁻¹) ^ r := by
          rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]
        _ ≤ V ^ r := ENNReal.rpow_le_rpow hroot hr.le
    have hpoint (j : Fin J) : δ ^ r ≤
        ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ r := by
      apply ENNReal.rpow_le_rpow _ hr.le
      dsimp [δ]
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      simpa [t, dist_eq_norm_sub] using hk_jump j
    have hlower : (J : ℝ≥0∞) * δ ^ r ≤ E := by
      calc
        (J : ℝ≥0∞) * δ ^ r = ∑ _j : Fin J, δ ^ r := by
          simp [nsmul_eq_mul]
        _ ≤ E := by
          dsimp [E]
          exact Finset.sum_le_sum fun j _ => hpoint j
    exact hlower.trans hupper
  obtain ⟨J, hJ⟩ := ENNReal.exists_nat_mul_gt hδrpos.ne'
    (ENNReal.rpow_ne_top_of_nonneg hr.le hvariation.ne)
  exact (not_lt_of_ge (hbound J)) hJ

/--
**Tao's norm-convergence theorem** (Theorem 1.1 of Tao's paper).

Let `(X, μ)` be a probability space, let `T₁, …, Tₙ` be commuting,
invertible, measure-preserving transformations, and let `f₁, …, fₙ` be
bounded complex-valued functions.  Then the multiple ergodic averages
`nCT.multipleErgodicAverage f T N` converge in `L²(X)` as `N → ∞`.

For `n ≥ 2`, this is a corollary of `aux_nCT_main_ergodic_theorem`: bounded
functions on a probability space lie in `L^(2n)`, and its finite
`r`-variation bound makes the averages Cauchy in `L²`.  For `n = 1`, it is
Mathlib's von Neumann mean ergodic theorem.  The stated bijectivity hypotheses
are those in Tao's theorem; the stronger main ergodic theorem does not need
them.
-/
theorem tao_norm_convergence
    {n : ℕ} (hn : 1 ≤ n) [IsProbabilityMeasure μ]
    {T : Fin n → X → X} (hT : ∀ i, MeasurePreserving (T i) μ μ)
    (hcomm : ∀ i j x, T i (T j x) = T j (T i x))
    (hbij : ∀ i, Function.Bijective (T i))
    {f : Fin n → X → ℂ} (hf : ∀ i, MemLp (f i) ∞ μ) :
    ∃ g : X → ℂ, MemLp g 2 μ ∧
      Tendsto (fun N => eLpNorm (nCT.multipleErgodicAverage f T N - g) 2 μ)
        atTop (𝓝 0) := by
  by_cases hn_one : n = 1
  · subst n
    exact one_transform_converges T hT f fun i =>
      (hf i).mono_exponent (by simp)
  have hn_two : 2 ≤ n := by omega
  let r : ℝ := (2 : ℝ) ^ n
  have hr : 2 ^ (n - 1) < r := by
    dsimp [r]
    exact_mod_cast Nat.pow_lt_pow_right one_lt_two (by omega : n - 1 < n)
  have hr_pos : 0 < r := by positivity
  have hf' : ∀ i, MemLp (f i) (2 * n) μ := fun i =>
    (hf i).mono_exponent (by simp)
  let S : aux_ErgodicSystem X μ n := {
    transformation := T
    measurePreserving := hT
    commutes := by
      intro i j x
      exact hcomm i j x }
  have haverage (N : ℕ) :
      nCT.multipleErgodicAverage f T N = aux_ergodicAverage S N f := by
    simpa [S] using
      aux_nCT_multipleErgodicAverage_eq_aux_ergodicAverage S f (N := N)
  have hmem (N : ℕ) : MemLp (nCT.multipleErgodicAverage f T N) 2 μ := by
    rw [haverage]
    exact aux_ergodicAverage_memLp_two (by omega) S f hf'
  let A : ℕ → Lp ℂ 2 μ := aux_ergodicAverageLp (by omega) S f hf'
  have hA (N : ℕ) :
      A N = (hmem N).toLp (nCT.multipleErgodicAverage f T N) := by
    let haux : MemLp (aux_ergodicAverage S N f) 2 μ :=
      aux_ergodicAverage_memLp_two (by omega) S f hf'
    calc
      A N = haux.toLp (aux_ergodicAverage S N f) := by rfl
      _ = (hmem N).toLp (nCT.multipleErgodicAverage f T N) :=
        (MemLp.toLp_congr haux (hmem N)
          (Filter.EventuallyEq.of_eq (haverage N).symm))
  have hvariation_eq :
      nCT.variationSeminorm (eLpNorm · 2 μ) r
          (nCT.multipleErgodicAverage f T) =
        nCT.variationSeminorm (fun z : Lp ℂ 2 μ => ‖z‖ₑ) r A := by
    unfold nCT.variationSeminorm
    apply iSup_congr
    intro J
    apply iSup_congr
    intro t
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change eLpNorm
        (nCT.multipleErgodicAverage f T (t.1 j.succ) -
          nCT.multipleErgodicAverage f T (t.1 j.castSucc)) 2 μ ^ r =
      ‖A (t.1 j.succ) - A (t.1 j.castSucc)‖ₑ ^ r
    rw [haverage, haverage]
    change eLpNorm (fun x =>
        aux_ergodicAverage S (t.1 j.succ) f x -
          aux_ergodicAverage S (t.1 j.castSucc) f x) 2 μ ^ r = _
    rw [aux_ergodicAverageLp_enorm_sub (by omega) S f hf']
  have hmain := aux_nCT_main_ergodic_theorem hn_two (r := r) (Or.inl hr)
    hT hcomm hf'
  have hvariation_raw :
      nCT.variationSeminorm (eLpNorm · 2 μ) r
          (nCT.multipleErgodicAverage f T) < ∞ := by
    apply lt_of_le_of_lt (hmain 0).2
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · apply ENNReal.prod_lt_top
      intro i _
      exact (hf' i).eLpNorm_lt_top
  have hvariation :
      nCT.variationSeminorm (fun z : Lp ℂ 2 μ => ‖z‖ₑ) r A < ∞ := by
    rw [← hvariation_eq]
    exact hvariation_raw
  obtain ⟨gLp, hconverges⟩ :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_of_variationSeminorm_lt_top A hr_pos hvariation)
  refine ⟨(gLp : X → ℂ), Lp.memLp gLp, ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (nCT.multipleErgodicAverage f T) hmem (gLp : X → ℂ) (Lp.memLp gLp)).mp
  have hconverges' : Tendsto A atTop
      (𝓝 ((Lp.memLp gLp).toLp (gLp : X → ℂ))) := by
    simpa only [Lp.toLp_coeFn] using hconverges
  apply hconverges'.congr'
  filter_upwards with N
  exact hA N

end Auto
