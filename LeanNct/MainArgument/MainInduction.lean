import LeanNct.MainArgument.MultipliersHLN
import LeanNct.MainArgument.GaussianDomination

/-!
# Main induction

Formalization of the subsection ``Main induction''.
-/

namespace Codex.MainArgument.MainInduction

open MeasureTheory
open Filter Topology
open scoped BigOperators ENNReal Real

open Codex.Preliminaries.KKernels
open Codex.Preliminaries.MKernels
open Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
open Codex.MainArgument.SandwichKernel
open Codex.MainArgument.MultipliersHLN
open Codex.MainArgument.GaussianDomination

noncomputable section

/--
The raw tensor square of the one-dimensional multiplier. This auxiliary
definition is needed to express the manuscript's repeated notation
`s_\gamma \otimes s_\gamma` as a double sequence on the concrete product
coordinate model.
-/
noncomputable def aux_sMultiplierTensorSquare {n : ℕ} (γ : GeometricParameters n) :
    DoubleSequence γ.k :=
  fun i j v => sMultiplier γ i j v.1 * sMultiplier γ i j v.2

/-- The tensor square of the square-root multiplier is a double sequence. -/
theorem aux_sMultiplierTensorSquare_memDoubleSequence {n : ℕ}
    (γ : GeometricParameters n) :
    MemDoubleSequence γ.k (aux_sMultiplierTensorSquare γ) := by
  intro i j
  exact (sMultiplier_memW0 γ i j).aux_mul_prod (sMultiplier_memW0 γ i j)

/-- The square-root tensor sandwich splits into its vanishing and telescoping parts. -/
theorem aux_sMultiplierTensorSquare_sandwich_eq {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) :
    sandwichKernel γ (aux_sMultiplierTensorSquare γ) i =
      fun j y => sandwichKernel γ (hMultiplier γ) i j y +
        sandwichKernel γ (gaussianDifference γ) i j y := by
  funext j y
  unfold sandwichKernel aux_sMultiplierTensorSquare hMultiplier
  ring

/--
The raw kernel appearing in the definition of `\mathrm{IncreaseData}`. It is
introduced only to give a Lean name to the displayed sequence
`\mathcal M_{i,\iota}` in that definition.
-/
noncomputable def aux_increaseDataKernel {n : ℕ} (γ : GeometricParameters n)
    (hkn : γ.k ≤ n - 1) (i : Fin γ.k) (ι : MultiplierIndex γ) :
    KernelSequence (γ.k + 1) := fun j y =>
  (∏ m ∈ Finset.univ.filter (fun m => m < i),
      gammaGaussian γ m j (y.1 m.castSucc, y.2 m.castSucc)) *
    |nMultiplier γ hkn ι i j (y.1 i.castSucc, y.2 i.castSucc)| *
      (∏ m ∈ Finset.univ.filter (fun m => i < m),
        gammaGaussian γ m (j - 1) (y.1 m.castSucc, y.2 m.castSucc)) *
    tensorSquare (sigmaMultiplier γ ι i j) (y.1 (Fin.last γ.k), y.2 (Fin.last γ.k))

/-- The raw kernel in `IncreaseData` is a Wiener kernel sequence. -/
theorem aux_increaseDataKernel_memKernelSequence {n : ℕ}
    (γ : GeometricParameters n) (hkn : γ.k ≤ n - 1)
    (i : Fin γ.k) (ι : MultiplierIndex γ) :
    MemKernelSequence (γ.k + 1) (aux_increaseDataKernel γ hkn i ι) := by
  intro j
  let A : Fin (γ.k + 1) → RealPlane → ℝ :=
    Fin.lastCases (tensorSquare (sigmaMultiplier γ ι i j)) (fun q =>
      if q < i then gammaGaussian γ q j else if i < q then
        gammaGaussian γ q (j - 1) else fun v => |nMultiplier γ hkn ι i j v|)
  have hA (q : Fin (γ.k + 1)) : MemW0 (A q) := by
    refine Fin.lastCases ?_ (fun r => ?_) q
    · simpa [A] using aux_memW0_tensorSquare (sigmaMultiplier γ ι i j)
        (sigmaMultiplier_memW0 γ ι i j)
    · by_cases hlt : r < i
      · simpa [A, hlt] using aux_gammaGaussian_memW0 γ r j
      by_cases hgt : i < r
      · simpa [A, hlt, hgt] using aux_gammaGaussian_memW0 γ r (j - 1)
      · have hri : r = i := by omega
        subst r
        simpa [A, hlt, hgt] using
          aux_memW0_abs (nKernelWellDefinedness γ hkn ι i j)
  have hprod : MemW0 (fun y : RealVector (γ.k + 1) × RealVector (γ.k + 1) =>
      ∏ q, A q (y.1 q, y.2 q)) :=
    fintype_plane_product_memW0 (γ.k + 1) A hA
  convert hprod using 1
  funext y
  rw [Fin.prod_univ_castSucc]
  have hfactor (a b c : Fin γ.k → ℝ) :
      (∏ q, if q < i then a q else if i < q then b q else c q) =
        (∏ q ∈ Finset.univ.filter (fun q => q < i), a q) * c i *
          ∏ q ∈ Finset.univ.filter (fun q => i < q), b q := by
    rw [Finset.prod_filter, Finset.prod_filter]
    have hc : c i = ∏ q : Fin γ.k, if q = i then c q else 1 := by simp
    rw [hc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    by_cases hqi : q < i
    · have hiq : ¬ i < q := not_lt_of_ge hqi.le
      simp [hqi, hiq, ne_of_lt hqi]
    by_cases hiq : i < q
    · simp [hqi, hiq, ne_of_gt hiq]
    have hq : q = i := by omega
    simp [hq]
  unfold aux_increaseDataKernel
  simp only [A, Fin.lastCases_castSucc, Fin.lastCases_last]
  simp only [ite_apply]
  let a : Fin γ.k → ℝ := fun q =>
    gammaGaussian γ q j (y.1 q.castSucc, y.2 q.castSucc)
  let b : Fin γ.k → ℝ := fun q =>
    gammaGaussian γ q (j - 1) (y.1 q.castSucc, y.2 q.castSucc)
  let c : Fin γ.k → ℝ := fun q =>
    |nMultiplier γ hkn ι i j (y.1 q.castSucc, y.2 q.castSucc)|
  change ((∏ q ∈ Finset.univ.filter (fun q => q < i), a q) * c i *
      ∏ q ∈ Finset.univ.filter (fun q => i < q), b q) *
      tensorSquare (sigmaMultiplier γ ι i j) (y.1 (Fin.last γ.k), y.2 (Fin.last γ.k)) =
    (∏ q, if q < i then a q else if i < q then b q else c q) *
      tensorSquare (sigmaMultiplier γ ι i j) (y.1 (Fin.last γ.k), y.2 (Fin.last γ.k))
  rw [← hfactor a b c]

private noncomputable def aux_sigmaScale {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) : ℤ → ℝ :=
  if _hzero : ι.1.1 = 0 then
    fun r => γ.scales i 1 (r + ι.1.2)
  else if _hpositive : 0 < ι.1.1 then
    fun r => (2 : ℝ) ^ ι.1.1 * γ.scales i 1 (r + (geometricDelta γ : ℤ))
  else
    fun r => (2 : ℝ) ^ ι.1.1 * γ.scales i 1 (r - (geometricDelta γ : ℤ))

private theorem aux_sigmaScale_spaced {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) :
    SpacedSequence (aux_sigmaScale γ ι i) := by
  unfold aux_sigmaScale
  split_ifs with hzero hpositive
  · exact shift_mem_A (γ.scales_spaced i 1) ι.1.2
  · exact smul_mem_A (shift_mem_A (γ.scales_spaced i 1) (geometricDelta γ : ℤ))
      (zpow_pos (by norm_num) _)
  · exact smul_mem_A (shift_mem_A (γ.scales_spaced i 1) (-(geometricDelta γ : ℤ)))
      (zpow_pos (by norm_num) _)

private theorem aux_sigmaMultiplier_eq_sigmaScale {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (j : ℤ) :
    sigmaMultiplier γ ι i j =
      squareRootGaussianDifference (aux_sigmaScale γ ι i) (aux_sigmaScale_spaced γ ι i) j := by
  funext x
  unfold sigmaMultiplier aux_sigmaScale squareRootGaussianDifference
  split_ifs <;> rfl

private noncomputable def aux_sigmaScalePair {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) : SequencePair :=
  fun _ r => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i r

private theorem aux_sigmaScalePair_spaced {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (r : Fin 2) :
    SpacedSequence (aux_sigmaScalePair γ ι i r) := by
  unfold aux_sigmaScalePair
  apply smul_mem_A (aux_sigmaScale_spaced γ ι i)
  exact inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))

private theorem aux_sqrt_sigmaScalePair {n : ℕ} (γ : GeometricParameters n)
    (ι : MultiplierIndex γ) (i : Fin γ.k) (r : ℤ) :
    Real.sqrt ((aux_sigmaScalePair γ ι i 0 r) ^ 2 +
      (aux_sigmaScalePair γ ι i 1 r) ^ 2) = aux_sigmaScale γ ι i r := by
  have hpos : 0 < aux_sigmaScale γ ι i r := (aux_sigmaScale_spaced γ ι i r).1
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  rw [show aux_sigmaScalePair γ ι i 0 r = (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i r by rfl]
  rw [show aux_sigmaScalePair γ ι i 1 r = (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i r by rfl]
  have hsq : ((Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i r) ^ 2 +
      ((Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i r) ^ 2 = (aux_sigmaScale γ ι i r) ^ 2 := by
    have hinv_sq : (Real.sqrt 2)⁻¹ ^ 2 = (2 : ℝ)⁻¹ := by
      rw [inv_pow, hsqrt]
    calc
      ((Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i r) ^ 2 +
          ((Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i r) ^ 2 =
          (Real.sqrt 2)⁻¹ ^ 2 *
            ((aux_sigmaScale γ ι i r) ^ 2 + (aux_sigmaScale γ ι i r) ^ 2) := by ring
      _ = (Real.sqrt 2)⁻¹ ^ 2 * (2 * (aux_sigmaScale γ ι i r) ^ 2) := by ring
      _ = (2 : ℝ)⁻¹ * (2 * (aux_sigmaScale γ ι i r) ^ 2) := by rw [hinv_sq]
      _ = (aux_sigmaScale γ ι i r) ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos hpos]

private theorem aux_sequenceDistance_common_shift_le (a b : ℤ → ℝ) (s : ℤ) :
    SequenceDistance (fun j => a (j + s)) (fun j => b (j + s)) ≤
      SequenceDistance a b := by
  classical
  by_cases hab : ∃ k : ℕ, WithinSequenceDistance a b k
  · rw [show SequenceDistance a b = (Nat.find hab : WithTop ℕ) by
      simp [SequenceDistance, hab]]
    apply aux_sequenceDistance_le_of_within
    intro j
    constructor
    · convert (Nat.find_spec hab (j + s)).1 using 1
      ring
    · convert (Nat.find_spec hab (j + s)).2 using 1
      ring
  · simp [SequenceDistance, hab]

private theorem aux_sequenceDistance_self_lt_top (a : ℤ → ℝ) : SequenceDistance a a < ⊤ := by
  apply lt_of_le_of_lt (aux_sequenceDistance_le_of_within (a := a) (b := a) (k := 0) ?_)
    (WithTop.coe_lt_top 0)
  intro j
  simp

private theorem aux_sequenceDistance_self_eq_zero (a : ℤ → ℝ) : SequenceDistance a a = 0 := by
  apply le_antisymm
  · apply aux_sequenceDistance_le_of_within
    intro j
    simp
  · exact bot_le

private noncomputable def aux_augmentedIncreaseOrientation {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) : Fin (γ.k + 1) → Fin 2 :=
  Fin.lastCases 0 (fun r => if r = i then w.orientation b else γ.orientation r)

private noncomputable def aux_augmentedIncreaseScales {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (m : Fin 2 → ℕ) :
    Fin (γ.k + 1) → SequencePair :=
  Fin.lastCases (aux_sigmaScalePair γ ι i)
    (fun r => if r < i then γ.scales r else if r = i then w.scales b m
      else fun s j => γ.scales r s (j - 1))

private theorem aux_augmentedIncreaseScales_spaced {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (hb : b ∈ w.B)
    (m : Fin 2 → ℕ) (r : Fin (γ.k + 1)) (s : Fin 2) :
    SpacedSequence (aux_augmentedIncreaseScales γ i ι w b m r s) := by
  refine Fin.lastCases ?_ (fun q => ?_) r
  · simpa [aux_augmentedIncreaseScales] using aux_sigmaScalePair_spaced γ ι i s
  · simp only [aux_augmentedIncreaseScales, Fin.lastCases_castSucc]
    split_ifs with hlt heq
    · exact γ.scales_spaced q s
    · exact w.scales_in_A b hb m s
    · simpa only [sub_eq_add_neg] using shift_mem_A (γ.scales_spaced q s) (-1)

private theorem aux_augmentedIncreaseScales_finite_distance {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (hb : b ∈ w.B)
    (m : Fin 2 → ℕ) (r : Fin (γ.k + 1)) :
    SequenceDistance (aux_augmentedIncreaseScales γ i ι w b m r 0)
      (aux_augmentedIncreaseScales γ i ι w b m r 1) < ⊤ := by
  refine Fin.lastCases ?_ (fun q => ?_) r
  · simp only [aux_augmentedIncreaseScales, Fin.lastCases_last]
    change SequenceDistance (fun j => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i j)
      (fun j => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i j) < ⊤
    exact aux_sequenceDistance_self_lt_top (fun j => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i j)
  · simp only [aux_augmentedIncreaseScales, Fin.lastCases_castSucc]
    split_ifs with hlt heq
    · exact γ.finite_distance q
    · apply lt_of_le_of_lt (w.distance_bound b hb m)
      have htop :
          ((C_gaussianDominationCombinedDistance *
            (geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m) : ℕ) : WithTop ℕ) < ⊤ :=
        WithTop.coe_lt_top _
      simpa using htop
    · exact lt_of_le_of_lt
        (by simpa only [sub_eq_add_neg] using
          aux_sequenceDistance_common_shift_le (γ.scales q 0) (γ.scales q 1) (-1))
        (γ.finite_distance q)

/-- The augmented geometric parameters used to dominate an `IncreaseData` kernel. -/
noncomputable def aux_augmentedIncreaseParameters {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (hb : b ∈ w.B)
    (m : Fin 2 → ℕ) : GeometricParameters n where
  k := γ.k + 1
  one_le_k := Nat.succ_le_succ (Nat.zero_le _)
  k_le_n := by
    have hn : 1 ≤ n := γ.one_le_k.trans (hkn.trans (Nat.sub_le _ _))
    calc
      γ.k + 1 ≤ (n - 1) + 1 := Nat.add_le_add_right hkn 1
      _ = n := Nat.sub_add_cancel hn
  orientation := aux_augmentedIncreaseOrientation γ i ι w b
  scales := aux_augmentedIncreaseScales γ i ι w b m
  scales_spaced := aux_augmentedIncreaseScales_spaced γ i ι w b hb m
  finite_distance := aux_augmentedIncreaseScales_finite_distance γ i ι w b hb m

/-- The old-coordinate orientations of the augmented parameters. -/
theorem aux_augmentedIncreaseParameters_orientation_castSucc {n : ℕ}
    (γ : GeometricParameters n) {hkn : γ.k ≤ n - 1} (i : Fin γ.k)
    (ι : MultiplierIndex γ) {C : ℝ} (w : aux_GaussianDominationWitness γ hkn i ι C)
    (b : ℕ) (hb : b ∈ w.B) (m : Fin 2 → ℕ) (q : Fin γ.k) :
    (aux_augmentedIncreaseParameters γ i ι w b hb m).orientation q.castSucc =
      if q = i then w.orientation b else γ.orientation q := by
  simp [aux_augmentedIncreaseParameters, aux_augmentedIncreaseOrientation]

/-- The old-coordinate scale pairs of the augmented parameters. -/
theorem aux_augmentedIncreaseParameters_scales_castSucc {n : ℕ}
    (γ : GeometricParameters n) {hkn : γ.k ≤ n - 1} (i : Fin γ.k)
    (ι : MultiplierIndex γ) {C : ℝ} (w : aux_GaussianDominationWitness γ hkn i ι C)
    (b : ℕ) (hb : b ∈ w.B) (m : Fin 2 → ℕ) (q : Fin γ.k) :
    (aux_augmentedIncreaseParameters γ i ι w b hb m).scales q.castSucc =
      if q < i then γ.scales q else if q = i then w.scales b m
      else fun s r => γ.scales q s (r - 1) := by
  simp [aux_augmentedIncreaseParameters, aux_augmentedIncreaseScales]

/-- The old-coordinate Gaussian factors of the augmented parameters. -/
theorem aux_augmentedIncreaseParameters_gammaGaussian_castSucc {n : ℕ}
    (γ : GeometricParameters n) {hkn : γ.k ≤ n - 1}
    (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ)
    (hb : b ∈ w.B) (m : Fin 2 → ℕ) (q : Fin γ.k) (j : ℤ) (v : RealPlane) :
    gammaGaussian (aux_augmentedIncreaseParameters γ i ι w b hb m) q.castSucc j v =
      if q < i then gammaGaussian γ q j v
      else if q = i then
        aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j v
      else gammaGaussian γ q (j - 1) v := by
  unfold gammaGaussian
  rw [aux_augmentedIncreaseParameters_scales_castSucc,
    aux_augmentedIncreaseParameters_orientation_castSucc]
  by_cases hqi : q = i
  · subst q
    simp [aux_dominatingGaussianTerm]
  · by_cases hlt : q < i
    · simp [hlt, hqi]
    · simp [hlt, hqi]

private noncomputable def aux_augmentedLastBaseKernel
    {n : ℕ} (γ : GeometricParameters n) {hkn : γ.k ≤ n - 1}
    (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C)
    (b : ℕ) (m : Fin 2 → ℕ) (j : ℤ) : MKernel γ.k :=
  fun x => ∏ q : Fin γ.k,
    if q < i then gammaGaussian γ q j (x.1 q, x.2 q)
    else if q = i then
      aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j (x.1 q, x.2 q)
    else gammaGaussian γ q (j - 1) (x.1 q, x.2 q)

/-- The Gaussian product preceding the terminal sigma factor is Wiener. -/
private theorem aux_augmentedLastBaseKernel_memW0
    {n : ℕ} (γ : GeometricParameters n) {hkn : γ.k ≤ n - 1}
    (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C)
    (b : ℕ) (hb : b ∈ w.B) (m : Fin 2 → ℕ) (j : ℤ) :
    MemW0 (aux_augmentedLastBaseKernel γ i ι w b m j) := by
  let A : Fin γ.k → RealPlane → ℝ := fun q =>
    if q < i then gammaGaussian γ q j else if q = i then
      aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j
    else gammaGaussian γ q (j - 1)
  have hA (q : Fin γ.k) : MemW0 (A q) := by
    by_cases hlt : q < i
    · simpa [A, hlt] using aux_gammaGaussian_memW0 γ q j
    by_cases hqi : q = i
    · subst q
      simpa [A, hlt] using aux_dominatingGaussianTerm_memW0
        (w.scales b m) (w.scales_in_A b hb m) (w.orientation b) j
    · simpa [A, hlt, hqi] using aux_gammaGaussian_memW0 γ q (j - 1)
  have hprod : MemW0 (fun x : RealVector γ.k × RealVector γ.k =>
      ∏ q, A q (x.1 q, x.2 q)) :=
    fintype_plane_product_memW0 γ.k A hA
  change MemW0 (fun x : RealVector γ.k × RealVector γ.k =>
    ∏ q, if q < i then gammaGaussian γ q j (x.1 q, x.2 q)
      else if q = i then
        aux_dominatingGaussianTerm (w.scales b m) (w.orientation b) j (x.1 q, x.2 q)
      else gammaGaussian γ q (j - 1) (x.1 q, x.2 q))
  simpa only [A, ite_apply] using hprod

/-- The Gaussian product preceding the terminal sigma factor is nonnegative. -/
private theorem aux_augmentedLastBaseKernel_nonneg
    {n : ℕ} (γ : GeometricParameters n) {hkn : γ.k ≤ n - 1}
    (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C)
    (b : ℕ) (hb : b ∈ w.B) (m : Fin 2 → ℕ) (j : ℤ)
    (x : RealVector γ.k × RealVector γ.k) :
    0 ≤ aux_augmentedLastBaseKernel γ i ι w b m j x := by
  unfold aux_augmentedLastBaseKernel
  apply Finset.prod_nonneg
  intro q _
  split_ifs with hlt hqi
  · exact aux_gammaGaussian_nonneg γ q j _
  · exact aux_dominatingGaussianTerm_nonneg
      (w.scales b m) (w.scales_in_A b hb m) (w.orientation b) j _
  · exact aux_gammaGaussian_nonneg γ q (j - 1) _

/-- The terminal sandwich of the augmented parameters has the required tensor-extension form. -/
theorem aux_augmentedLast_sandwich_eq_tensorSquareExtension
    {n : ℕ} (γ : GeometricParameters n) {hkn : γ.k ≤ n - 1}
    (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C)
    (b : ℕ) (hb : b ∈ w.B) (m : Fin 2 → ℕ) (j : ℤ) :
    sandwichKernel (aux_augmentedIncreaseParameters γ i ι w b hb m)
      (aux_sMultiplierTensorSquare (aux_augmentedIncreaseParameters γ i ι w b hb m))
      (Fin.last γ.k) j =
    tensorSquareExtension (γ.k + 1) (by omega) (Fin.last γ.k)
      (aux_augmentedLastBaseKernel γ i ι w b m j)
      (sigmaMultiplier γ ι i j) := by
  classical
  funext y
  let δ := aux_augmentedIncreaseParameters γ i ι w b hb m
  have hprod :
      (∏ r ∈ Finset.univ.filter (fun r : Fin (γ.k + 1) => r < Fin.last γ.k),
        gammaGaussian δ r j (y.1 r, y.2 r)) =
      aux_augmentedLastBaseKernel γ i ι w b m j
        (fun q => y.1 q.castSucc, fun q => y.2 q.castSucc) := by
    unfold aux_augmentedLastBaseKernel
    symm
    apply Finset.prod_bij (fun q _ => q.castSucc)
    · intro q _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.castSucc_lt_last q⟩
    · intro q₁ _ q₂ _ hq
      exact Fin.castSucc_injective _ hq
    · intro r hr
      have hrlt : r < Fin.last γ.k := (Finset.mem_filter.mp hr).2
      have hrne : r ≠ Fin.last γ.k := ne_of_lt hrlt
      refine ⟨r.castPred hrne, Finset.mem_univ _, ?_⟩
      exact Fin.castSucc_castPred r hrne
    · intro q _
      simpa [δ] using
        (aux_augmentedIncreaseParameters_gammaGaussian_castSucc γ i ι w b hb m q j
          (y.1 q.castSucc, y.2 q.castSucc)).symm
  have hlast :
      aux_sMultiplierTensorSquare δ (Fin.last γ.k) j =
        tensorSquare (sigmaMultiplier γ ι i j) := by
    have horientation : δ.orientation (Fin.last γ.k) = 0 := by
      simp [δ, aux_augmentedIncreaseParameters, aux_augmentedIncreaseOrientation]
    have hscales : δ.scales (Fin.last γ.k) = aux_sigmaScalePair γ ι i := by
      simp [δ, aux_augmentedIncreaseParameters, aux_augmentedIncreaseScales]
    have hsigma : sMultiplier δ (Fin.last γ.k) j = sigmaMultiplier γ ι i j := by
      rw [aux_sigmaMultiplier_eq_sigmaScale]
      funext x
      unfold sMultiplier
      rw [dif_pos horientation]
      unfold squareRootGaussianDifference
      simp_rw [hscales]
      simp_rw [aux_sqrt_sigmaScalePair]
    funext v
    unfold aux_sMultiplierTensorSquare tensorSquare
    rw [hsigma]
  have herase (x : RealVector (γ.k + 1)) :
      aux_eraseVector (γ.k + 1) (by omega) (Fin.last γ.k) x =
        fun q => x q.castSucc := by
    funext q
    simp [aux_eraseVector]
  change sandwichKernel δ (aux_sMultiplierTensorSquare δ) (Fin.last γ.k) j y = _
  unfold sandwichKernel
  change
    (∏ r ∈ Finset.univ.filter (fun r : Fin (γ.k + 1) => r < Fin.last γ.k),
        gammaGaussian δ r j (y.1 r, y.2 r)) *
      aux_sMultiplierTensorSquare δ (Fin.last γ.k) j
        (y.1 (Fin.last γ.k), y.2 (Fin.last γ.k)) *
      (∏ r ∈ Finset.univ.filter (fun r : Fin (γ.k + 1) => Fin.last γ.k < r),
        gammaGaussian δ r (j - 1) (y.1 r, y.2 r)) =
    tensorSquareExtension (γ.k + 1) (by omega) (Fin.last γ.k)
      (aux_augmentedLastBaseKernel γ i ι w b m j)
      (sigmaMultiplier γ ι i j) y
  have hright :
      (∏ r ∈ Finset.univ.filter (fun r : Fin (γ.k + 1) => Fin.last γ.k < r),
        gammaGaussian δ r (j - 1) (y.1 r, y.2 r)) = 1 := by
    rw [Finset.filter_false_of_mem]
    · simp
    · intro r _ hr
      exact not_lt_of_ge (Fin.le_last r) hr
  rw [hprod, hlast, hright]
  unfold tensorSquareExtension
  simp only [herase, mul_one]
  rfl

private theorem aux_augmentedIncreaseParameters_orientation_last {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (hb : b ∈ w.B)
    (m : Fin 2 → ℕ) :
    (aux_augmentedIncreaseParameters γ i ι w b hb m).orientation (Fin.last γ.k) = 0 := by
  simp [aux_augmentedIncreaseParameters, aux_augmentedIncreaseOrientation]

private theorem aux_augmentedIncreaseParameters_scales_last {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (hb : b ∈ w.B)
    (m : Fin 2 → ℕ) :
    (aux_augmentedIncreaseParameters γ i ι w b hb m).scales (Fin.last γ.k) =
      aux_sigmaScalePair γ ι i := by
  simp [aux_augmentedIncreaseParameters, aux_augmentedIncreaseScales]

/-- The final-coordinate multiplier of the augmented parameters is the sigma multiplier. -/
theorem aux_sMultiplier_augmentedIncreaseParameters_last {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (hb : b ∈ w.B)
    (m : Fin 2 → ℕ) (j : ℤ) :
    sMultiplier (aux_augmentedIncreaseParameters γ i ι w b hb m) (Fin.last γ.k) j =
      sigmaMultiplier γ ι i j := by
  rw [aux_sigmaMultiplier_eq_sigmaScale]
  funext x
  unfold sMultiplier
  rw [dif_pos (aux_augmentedIncreaseParameters_orientation_last γ i ι w b hb m)]
  unfold squareRootGaussianDifference
  simp_rw [aux_augmentedIncreaseParameters_scales_last]
  simp_rw [aux_sqrt_sigmaScalePair]

/-- The augmented parameters have the geometric bound required by Gaussian domination. -/
theorem aux_geometricDelta_augmentedIncreaseParameters_le {n : ℕ} (γ : GeometricParameters n)
    {hkn : γ.k ≤ n - 1} (i : Fin γ.k) (ι : MultiplierIndex γ) {C : ℝ}
    (w : aux_GaussianDominationWitness γ hkn i ι C) (b : ℕ) (hb : b ∈ w.B)
    (m : Fin 2 → ℕ) :
    geometricDelta (aux_augmentedIncreaseParameters γ i ι w b hb m) ≤
      (1 + C_gaussianDominationCombinedDistance) *
        (geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m) := by
  let d : Fin γ.k → ℕ := fun q =>
    (sequencePairDistance (γ.scales q)).untop (ne_of_lt (γ.finite_distance q))
  let dp : ℕ := (sequencePairDistance (w.scales b m)).untop (by
    have h := w.distance_bound b hb m
    apply ne_of_lt (lt_of_le_of_lt h ?_)
    norm_cast
    exact WithTop.coe_lt_top _)
  let u : Fin γ.k → ℕ := fun q =>
    (sequencePairDistance (aux_augmentedIncreaseScales γ i ι w b m q.castSucc)).untop
      (ne_of_lt (aux_augmentedIncreaseScales_finite_distance γ i ι w b hb m q.castSucc))
  let da : ℕ := (sequencePairDistance (aux_sigmaScalePair γ ι i)).untop
    (ne_of_lt (aux_sequenceDistance_self_lt_top
      (fun j => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i j)))
  have hαzero : sequencePairDistance (aux_sigmaScalePair γ ι i) = 0 := by
    change SequenceDistance (fun j => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i j)
      (fun j => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i j) = 0
    exact aux_sequenceDistance_self_eq_zero (fun j => (Real.sqrt 2)⁻¹ * aux_sigmaScale γ ι i j)
  have hda : da = 0 := by simp [da, hαzero]
  have hu_i : u i = dp := by
    simp [u, dp, aux_augmentedIncreaseScales]
  have hu_le (q : Fin γ.k) (hqi : q ≠ i) : u q ≤ d q := by
    by_cases hlt : q < i
    · simp [u, d, aux_augmentedIncreaseScales, hlt]
    · have hshift :
          SequenceDistance (fun j => γ.scales q 0 (j - 1))
            (fun j => γ.scales q 1 (j - 1)) ≤
              SequenceDistance (γ.scales q 0) (γ.scales q 1) :=
        aux_sequenceDistance_common_shift_le (γ.scales q 0) (γ.scales q 1) (-1)
      simp only [u, d, aux_augmentedIncreaseScales, Fin.lastCases_castSucc, hlt, if_false, hqi]
      apply WithTop.coe_le_coe.mp
      simpa only [sequencePairDistance, WithTop.coe_untop] using hshift
  have hrest : (∑ q ∈ Finset.univ.erase i, u q) ≤
      ∑ q ∈ Finset.univ.erase i, d q := by
    apply Finset.sum_le_sum
    intro q hq
    exact hu_le q (Finset.mem_erase.mp hq).1
  have hsum_u : (∑ q, u q) = (∑ q ∈ Finset.univ.erase i, u q) + dp := by
    rw [← Finset.sum_erase_add Finset.univ u (Finset.mem_univ i), hu_i]
  have hsum_d : (∑ q, d q) = (∑ q ∈ Finset.univ.erase i, d q) + d i := by
    rw [← Finset.sum_erase_add Finset.univ d (Finset.mem_univ i)]
  have hsum_le : (∑ q, u q) ≤ (∑ q, d q) + dp := by
    rw [hsum_u, hsum_d]
    omega
  have hdelta : geometricDelta γ = 1 + ∑ q, d q := by
    simp [geometricDelta, d]
  have htilde : geometricDelta (aux_augmentedIncreaseParameters γ i ι w b hb m) =
      1 + (∑ q, u q) + da := by
    unfold geometricDelta aux_augmentedIncreaseParameters
    rw [Fin.sum_univ_castSucc]
    simp [aux_augmentedIncreaseScales, u, da]
    omega
  let P : ℕ := geometricDelta γ + ι.1.1.natAbs + aux_natPairWeight m
  have hpfinite : sequencePairDistance (w.scales b m) < ⊤ :=
    lt_of_le_of_lt (w.distance_bound b hb m) (by
      norm_cast
      exact WithTop.coe_lt_top _)
  have hdp : dp ≤ C_gaussianDominationCombinedDistance * P := by
    have hdist := w.distance_bound b hb m
    rw [← WithTop.coe_untop _ (ne_of_lt hpfinite)] at hdist
    norm_cast at hdist ⊢
    simpa [dp, P] using hdist
  calc
    geometricDelta (aux_augmentedIncreaseParameters γ i ι w b hb m) =
        1 + (∑ q, u q) + da := htilde
    _ ≤ 1 + ((∑ q, d q) + dp) + 0 := by omega
    _ = geometricDelta γ + dp := by omega
    _ ≤ geometricDelta γ + C_gaussianDominationCombinedDistance * P :=
      Nat.add_le_add_left hdp _
    _ ≤ P + C_gaussianDominationCombinedDistance * P := by
      apply Nat.add_le_add_right
      dsimp [P]
      omega
    _ = (1 + C_gaussianDominationCombinedDistance) * P := by
      simp [Nat.add_mul]

/--
\begin{definition}[induct positive terms]\label{induct positive terms}
Let $k\in \N$ with $1\le k\le n$ and $C\in [1,\infty)$.
We say that $\InductPositiveTerms{k,C}$ holds if
for all $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$,
\begin{equation}
    \|\M(\gamma,s_{\gamma} \otimes s_{\gamma},i)\|_{{\rm M}(k)}\le C \Delta_\gamma^{2-2^{k-n+1}}.
\end{equation}
\end{definition}
-/
def InductPositiveTerms (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (_hkn : k ≤ n) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n), γ.k = k → ∀ i : Fin γ.k,
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (aux_sMultiplierTensorSquare γ) i) ≤
      ENNReal.ofReal
        (C * Real.rpow (geometricDelta γ : ℝ)
          (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1)))

/--
\begin{definition}[vanishing diagonal]\label{vanishing diagonal}
Let $k\in \N$ with $1\le k\le n$ and $C\in [1,\infty)$.
We say that $\VanishingDiagonal{k,C}$ holds if
for all $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$,
\begin{equation}
    \|\M(\gamma,H_\gamma,i)\|_{{\rm M}(k)}
    \le C \Delta_\gamma^{2-2^{k-n+1}} .
\end{equation}
\end{definition}
-/
def VanishingDiagonal (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (_hkn : k ≤ n) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n), γ.k = k → ∀ i : Fin γ.k,
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (hMultiplier γ) i) ≤
      ENNReal.ofReal
        (C * Real.rpow (geometricDelta γ : ℝ)
          (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1)))

/--
\begin{definition}[diagonal band]\label{diagonal band}
Let $k\in \N$ with $1\le k\le n-1$ and $C\in [1,\infty)$.
We say that $\DiagonalBand{k,C}$ holds if
for all $\gamma=(k,u,a)\in \Gamma$, $i\in [k)$,
\begin{equation}
   \sum_{\iota\in\mathcal{I}_{\gamma}}
   \|\M(\gamma,L_{\gamma,\iota},i)\|_{{\rm M}(k)}
   \le C\Delta_\gamma^{2-2^{k-n+1}} .
\end{equation}
\end{definition}
-/
def DiagonalBand (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (_hkn : k ≤ n - 1) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n), γ.k = k → ∀ i : Fin γ.k,
    sumOverMultiplierIndexENNReal γ (fun ι =>
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (lMultiplier γ ι) i)) ≤
      ENNReal.ofReal
        (C * Real.rpow (geometricDelta γ : ℝ)
          (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1)))

/--
\begin{definition}[increase data]\label{increase data}
Let $k\in \N$ with $1\le k\le n-1$ and $C\in [1,\infty)$.
We say that $\IncreaseData{k,C}$ holds if the following holds.

Let $\gamma=(k,u,a)\in \Gamma$, let $i\in [k)$, and let
\iota\in\mathcal{I}_{\gamma}$.
For $j\in\mathbb Z$ and $y\in(\mathbb R^2)^{k+1}$ define
\begin{equation}
    (\M_{i,\iota})_j(y):=
    \Big(\prod_{m\in [i)} (G_\gamma)_{m,j}(y_m)\Big)
    |(N_{\gamma,\iota})_{i,j}(y_i)|
    \Big(\prod_{m=i+1}^{k-1} (G_\gamma)_{m,j-1}(y_m)\Big)
    \bigl(\sigma_{\gamma,\iota,i,j}^{\otimes 2}\bigr)(y_{k}) .
\end{equation}
Then $\M_{i,\iota}\in {\rm M}(k+1)$ and
\begin{equation}
  \|\M_{i,\iota}\|_{{\rm M}(k+1)}
  \le C 2^{-\frac{|\iota_1|}{2}}(1+|\iota_1|)^2
  \Delta_\gamma^{2-2^{k-n+2}} .
\end{equation}
\end{definition}
-/
def IncreaseData (n k : ℕ) (C : ℝ) (_hk : 1 ≤ k) (hkn : k ≤ n - 1) (_hC : 1 ≤ C) :
    Prop :=
  ∀ (γ : GeometricParameters n) (hγ : γ.k = k) (i : Fin γ.k)
    (ι : MultiplierIndex γ),
    let hγn : γ.k ≤ n - 1 := by simpa [hγ] using hkn
    MemKernelSequence (γ.k + 1) (aux_increaseDataKernel γ hγn i ι) ∧
      kernelSequenceSeminorm n (γ.k + 1) (by omega) (by omega)
          (aux_increaseDataKernel γ hγn i ι) ≤
        ENNReal.ofReal
          (C * Real.rpow 2 (-((ι.1.1.natAbs : ℝ) / 2)) *
            (1 + (ι.1.1.natAbs : ℝ)) ^ 2 *
            Real.rpow (geometricDelta γ : ℝ)
              (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 2)))

/-- The geometric loss in the induction estimates is at least one. -/
theorem aux_one_le_geometricDelta_rpow {n k : ℕ} (_hk : 1 ≤ k) (hkn : k ≤ n)
    (γ : GeometricParameters n) :
    1 ≤ Real.rpow (geometricDelta γ : ℝ)
      (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1)) := by
  have hdelta_nat : 1 ≤ geometricDelta γ := by
    unfold geometricDelta
    omega
  have hdelta : (1 : ℝ) ≤ (geometricDelta γ : ℝ) := by
    exact_mod_cast hdelta_nat
  have hindex : (k : ℤ) - (n : ℤ) + 1 ≤ 1 := by
    omega
  have hpow : (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1) ≤ 2 := by
    calc
      (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1) ≤ (2 : ℝ) ^ (1 : ℤ) :=
        zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hindex
      _ = 2 := by norm_num
  have hexp : 0 ≤ 2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1) := by
    linarith
  exact Real.one_le_rpow hdelta hexp

private theorem aux_terminalSandwichSeminorm_eq_zero {n : ℕ} (hn : 1 ≤ n)
    (γ : GeometricParameters n) (hγ : γ.k = n) (i : Fin γ.k) :
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
      (sandwichKernel γ (hMultiplier γ) i) = 0 := by
  rcases γ with ⟨k, hk, hkn, orientation, scales, hscales, hfinite⟩
  dsimp at hγ
  subst k
  let γ : GeometricParameters n :=
    { k := n
      one_le_k := hk
      k_le_n := hkn
      orientation := orientation
      scales := scales
      scales_spaced := hscales
      finite_distance := hfinite }
  change kernelSequenceSeminorm n n γ.one_le_k γ.k_le_n
    (sandwichKernel γ (hMultiplier γ) i) = 0
  unfold kernelSequenceSeminorm
  apply le_antisymm
  · refine iSup_le fun J => ?_
    refine iSup_le fun F => ?_
    let M : Fin J.1 → MKernel γ.k := fun l =>
      sandwichKernel γ (hMultiplier γ) i (l : ℤ)
    have hM (l : Fin J.1) : MemW0 (M l) := by
      exact sandwichKernel_memKernelSequence γ (hMultiplier γ)
        (hMultiplier_memDoubleSequence γ) i (l : ℤ)
    have hsum :
        (fun y : RealVector γ.k × RealVector γ.k =>
          ∑ j ∈ Finset.range J.1, sandwichKernel γ (hMultiplier γ) i (j : ℤ) y) =
        fun y => ∑ l, M l y := by
      funext y
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp [M, Finset.mem_range.mp hj]
    have hMsum : MemW0 (fun y : RealVector γ.k × RealVector γ.k => ∑ l, M l y) := by
      apply aux_memW0_finset_sum Finset.univ
      intro l hl
      exact hM l
    have hzero : ∀ z : RealVector γ.k × ℝ,
        ∫ q : ℝ, mToK γ.k γ.one_le_k (fun y => ∑ l, M l y) (z.1, z.2 + q) = 0 := by
      intro z
      rw [aux_mToK_finset_sum γ.k J.1 γ.one_le_k M hM]
      rw [integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro l hl
        have htransport := mToK_terminalFibreIntegral_general γ.one_le_k
          (M l) (hM l) z
        have htransport' :
            (∫ q : ℝ, mToK γ.k γ.one_le_k (M l) (z.1, z.2 + q)) =
              ∫ p : RealVector γ.k, M l (z.1 + p, p) := by
          calc
            (∫ q : ℝ, mToK γ.k γ.one_le_k (M l) (z.1, z.2 + q)) =
                ∫ q : ℝ, mToK γ.k γ.one_le_k (M l) (z.1, z.2 + (-q)) :=
              (integral_neg_eq_self
                (fun q : ℝ => mToK γ.k γ.one_le_k (M l) (z.1, z.2 + q)) volume).symm
            _ = ∫ q : ℝ, mToK γ.k γ.one_le_k (M l) (z.1, z.2 - q) := by
              apply integral_congr_ae
              filter_upwards [] with q
              congr 2
            _ = ∫ p : RealVector γ.k, M l (z.1 + p, p) := htransport
        rw [htransport']
        exact sandwichHMultiplier_terminalIntegral γ i (l : ℤ) z.1
      · intro l hl
        have hK : MemW0 (mToK γ.k γ.one_le_k (M l)) :=
          mToK_memW0 γ.k γ.k γ.one_le_k le_rfl (M l) (hM l)
        have hS : MemW0 (fun s : ℝ => mToK γ.k γ.one_le_k (M l) (z.1, s)) :=
          hK.aux_memW0_slice_of_addHaar z.1
        have hSint : Integrable (fun s : ℝ =>
            mToK γ.k γ.one_le_k (M l) (z.1, s)) :=
          aux_memW0_integrable_of_addHaar hS
        have hshift : MeasurePreserving (fun q : ℝ => z.2 + q) volume volume :=
          measurePreserving_add_left (volume : Measure ℝ) z.2
        simpa [Function.comp_def] using hshift.integrable_comp_of_integrable hSint
    have hprism :
        prismForm n γ.k γ.one_le_k γ.k_le_n (fun y => ∑ l, M l y)
            (fun a z => F.1 a z) = 0 := by
      rw [prismForm]
      exact simplificationOnePrism γ.k hn (mToK γ.k γ.one_le_k (fun y => ∑ l, M l y))
        (mToK_memW0 n γ.k γ.one_le_k γ.k_le_n _ hMsum) hzero F.1 F.2
    rw [hsum]
    rw [hprism]
    norm_num
  · exact bot_le

private theorem aux_terminalVanishingDiagonal {n : ℕ} (hn : 1 ≤ n) :
    VanishingDiagonal n n 1 hn le_rfl (by norm_num) := by
  intro γ hγ i
  rw [aux_terminalSandwichSeminorm_eq_zero hn γ hγ i]
  exact bot_le

/--
\begin{proposition}[vanishing kernel integral]
\label{vanishing kernel integral}
Let $\gamma=(n,w,a)\in\Gamma$.
Then the corresponding terminal sandwich seminorm vanishes.
\end{proposition}
-/
theorem vanishingKernelIntegral (n : ℕ) (hn : 1 ≤ n) :
    (∀ (γ : GeometricParameters n), γ.k = n → ∀ i : Fin γ.k,
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (hMultiplier γ) i) = 0) ∧
      VanishingDiagonal n n 1 hn le_rfl (by norm_num) := by
  constructor
  · intro γ hγ i
    exact aux_terminalSandwichSeminorm_eq_zero hn γ hγ i
  · exact aux_terminalVanishingDiagonal hn

/-- This auxiliary monotonicity lemma lets later induction steps enlarge the
constant in the conclusion of `InductPositiveTerms` without changing the
geometric data. -/
theorem aux_inductPositiveTerms_mono {n k : ℕ} {C D : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hC : 1 ≤ C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    InductPositiveTerms n k C hk hkn hC →
      InductPositiveTerms n k D hk hkn hD := by
  intro h γ hγ i
  refine (h γ hγ i).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right hCD
  exact Real.rpow_nonneg (by positivity) _

/-- A kernel sequence is bounded by a uniform limit of finite partial approximants. -/
private theorem aux_kernelSequenceSeminorm_le_of_tendsto_eLpNorm
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (M : KernelSequence k) (P : ℕ → KernelSequence k) (A : ℝ≥0∞)
    (hM : MemKernelSequence k M) (hP : ∀ N, MemKernelSequence k (P N))
    (hbound : ∀ N, kernelSequenceSeminorm n k hk hkn (P N) ≤ A)
    (hconv : ∀ J : {J : ℕ // 0 < J}, Tendsto (fun N => eLpNorm
      (fun y => (∑ j ∈ Finset.range J.1, P N (j : ℤ) y) -
        ∑ j ∈ Finset.range J.1, M (j : ℤ) y) 1 volume) atTop (nhds 0)) :
    kernelSequenceSeminorm n k hk hkn M ≤ A := by
  classical
  unfold kernelSequenceSeminorm
  refine iSup_le fun J => ?_
  refine iSup_le fun F => ?_
  let c : ℝ := min 1
    (Real.rpow (J.1 : ℝ) (-1 + 2 ^ ((k : ℤ) - (n : ℤ) + 1)))
  have hc : 0 ≤ c := by
    dsimp [c]
    exact le_min zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hc_one : c ≤ 1 := by
    dsimp [c]
    exact min_le_left _ _
  apply aux_le_iSup_of_tendsto_error (hconv J)
  intro N
  let MP : MKernel k := fun y => ∑ j ∈ Finset.range J.1, P N (j : ℤ) y
  let MM : MKernel k := fun y => ∑ j ∈ Finset.range J.1, M (j : ℤ) y
  have hMP : MemW0 MP := by
    dsimp [MP]
    apply aux_memW0_finset_sum
    intro j hj
    exact hP N (j : ℤ)
  have hMM : MemW0 MM := by
    dsimp [MM]
    apply aux_memW0_finset_sum
    intro j hj
    exact hM (j : ℤ)
  have hsub : prismForm n k hk hkn MP (fun a => F.1 a) -
      prismForm n k hk hkn MM (fun a => F.1 a) =
      prismForm n k hk hkn (fun y => MP y - MM y) (fun a => F.1 a) := by
    exact aux_prismForm_sub hk hkn MP MM hMP hMM F.1
  have herror : ‖prismForm n k hk hkn (fun y => MP y - MM y)
      (fun a => F.1 a)‖ₑ ≤ eLpNorm (fun y => MP y - MM y) 1 volume := by
    change ‖prismBrascampLiebForm n k hk hkn
        (mToK k hk (fun y => MP y - MM y)) (fun a x => F.1 a x)‖ₑ ≤ _
    exact (prismBLInequality n k hk hkn
      (mToK k hk (fun y => MP y - MM y))
      (mToK_memW0 n k hk hkn (fun y => MP y - MM y) (aux_memW0_sub hMP hMM))
      F.1 F.2).trans
      (mToK_eLpNorm_one_le n k hk hkn (fun y => MP y - MM y)
        (aux_memW0_sub hMP hMM))
  have hmain : ENNReal.ofReal (c * |prismForm n k hk hkn MP
      (fun a => F.1 a)|) ≤ A := by
    change ENNReal.ofReal (min 1
      (Real.rpow (J.1 : ℝ) (-1 + 2 ^ ((k : ℤ) - (n : ℤ) + 1))) *
      |prismForm n k hk hkn
        (fun y => ∑ j ∈ Finset.range J.1, P N (j : ℤ) y)
        (fun a => F.1 a)|) ≤ A
    let Q : {J : ℕ // 0 < J} → ℝ≥0∞ := fun J =>
      ⨆ F : NormalizedFunctionTuple n,
        ENNReal.ofReal (min 1
          (Real.rpow (J.1 : ℝ) (-1 + 2 ^ ((k : ℤ) - (n : ℤ) + 1))) *
          |prismForm n k hk hkn
            (fun y => ∑ j ∈ Finset.range J.1, P N (j : ℤ) y)
            (fun a => F.1 a)|)
    calc
      _ ≤ Q J := by
        dsimp [Q]
        exact le_iSup (fun F : NormalizedFunctionTuple n =>
          ENNReal.ofReal (min 1
            (Real.rpow (J.1 : ℝ) (-1 + 2 ^ ((k : ℤ) - (n : ℤ) + 1))) *
            |prismForm n k hk hkn
              (fun y => ∑ j ∈ Finset.range J.1, P N (j : ℤ) y)
              (fun a => F.1 a)|)) F
      _ ≤ ⨆ J, Q J := le_iSup Q J
      _ = kernelSequenceSeminorm n k hk hkn (P N) := by rfl
      _ ≤ A := hbound N
  have herror' : ENNReal.ofReal (c * |prismForm n k hk hkn
      (fun y => MP y - MM y) (fun a => F.1 a)|) ≤
      eLpNorm (fun y => MP y - MM y) 1 volume := by
    calc
      ENNReal.ofReal (c * |prismForm n k hk hkn
          (fun y => MP y - MM y) (fun a => F.1 a)|) ≤
          ENNReal.ofReal |prismForm n k hk hkn
            (fun y => MP y - MM y) (fun a => F.1 a)| := by
              apply ENNReal.ofReal_le_ofReal
              have hmul : |prismForm n k hk hkn
                  (fun y => MP y - MM y) (fun a => F.1 a)| * c ≤
                  |prismForm n k hk hkn
                    (fun y => MP y - MM y) (fun a => F.1 a)| :=
                mul_le_of_le_one_right (abs_nonneg _) hc_one
              simpa [mul_comm] using hmul
      _ = ‖prismForm n k hk hkn (fun y => MP y - MM y)
          (fun a => F.1 a)‖ₑ := by rw [Real.enorm_eq_ofReal_abs]
      _ ≤ _ := herror
  change ENNReal.ofReal (c * |prismForm n k hk hkn MM (fun a => F.1 a)|) ≤ _
  calc
    ENNReal.ofReal (c * |prismForm n k hk hkn MM (fun a => F.1 a)|) =
        ENNReal.ofReal (c * |prismForm n k hk hkn MP (fun a => F.1 a) -
          prismForm n k hk hkn (fun y => MP y - MM y) (fun a => F.1 a)|) := by
          congr 3
          linarith [hsub]
    _ ≤ ENNReal.ofReal (c *
        (|prismForm n k hk hkn MP (fun a => F.1 a)| +
          |prismForm n k hk hkn (fun y => MP y - MM y) (fun a => F.1 a)|)) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ hc
          simpa using (abs_sub_le
            (prismForm n k hk hkn MP (fun a => F.1 a)) 0
            (prismForm n k hk hkn (fun y => MP y - MM y) (fun a => F.1 a)))
    _ = ENNReal.ofReal (c * |prismForm n k hk hkn MP (fun a => F.1 a)|) +
        ENNReal.ofReal (c * |prismForm n k hk hkn
          (fun y => MP y - MM y) (fun a => F.1 a)|) := by
          rw [mul_add]
          exact ENNReal.ofReal_add (mul_nonneg hc (abs_nonneg _))
            (mul_nonneg hc (abs_nonneg _))
    _ ≤ A + eLpNorm (fun y => MP y - MM y) 1 volume := add_le_add hmain herror'

/-- This auxiliary monotonicity lemma is used to align the output constants of
the diagonal-band and positive-term implications. -/
theorem aux_vanishingDiagonal_mono {n k : ℕ} {C D : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hC : 1 ≤ C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    VanishingDiagonal n k C hk hkn hC →
      VanishingDiagonal n k D hk hkn hD := by
  intro h γ hγ i
  refine (h γ hγ i).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right hCD
  exact Real.rpow_nonneg (by positivity) _

/-- This auxiliary monotonicity lemma is used to enlarge the summation bound
in `DiagonalBand` when composing the main induction implications. -/
theorem aux_diagonalBand_mono {n k : ℕ} {C D : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n - 1) (hC : 1 ≤ C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    DiagonalBand n k C hk hkn hC →
      DiagonalBand n k D hk hkn hD := by
  intro h γ hγ i
  refine (h γ hγ i).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right hCD
  exact Real.rpow_nonneg (by positivity) _

/-- Constant from Proposition \ref{induct positive terms imply increase data}; it is used in
`inductPositiveTerms_implies_increaseData`. -/
noncomputable def C_inductPositiveTermsImplyIncreaseData : ℝ :=
  (2 : ℝ) ^ (10 : ℕ) * C_gaussianDominationCombinedCard *
    (1 + C_gaussianDominationCombinedDistance) ^ (2 : ℕ) * C_gaussianDominationCombined

/-- Source label `\ref{constant induct positive terms imply increase data}`. -/
theorem constantInductPositiveTermsImplyIncreaseData :
    C_inductPositiveTermsImplyIncreaseData < (2 : ℝ) ^ (172 : ℕ) := by
  unfold C_inductPositiveTermsImplyIncreaseData
    C_gaussianDominationCombinedCard C_gaussianDominationCombinedDistance
    C_gaussianDominationCombined
  norm_num

/-- This auxiliary positivity fact is needed when taking square roots of the
constant in the reverse induction estimates. -/
theorem aux_C_inductPositiveTermsImplyIncreaseData_pos :
    0 < C_inductPositiveTermsImplyIncreaseData := by
  unfold C_inductPositiveTermsImplyIncreaseData
    C_gaussianDominationCombinedCard C_gaussianDominationCombinedDistance
    C_gaussianDominationCombined
  positivity

/-- This auxiliary lower bound supplies the manuscript's admissibility
condition `C ∈ [1,∞)` when the Gaussian-domination constant is fed into the
main induction. -/
theorem aux_one_le_C_inductPositiveTermsImplyIncreaseData :
    1 ≤ C_inductPositiveTermsImplyIncreaseData := by
  unfold C_inductPositiveTermsImplyIncreaseData
    C_gaussianDominationCombinedCard C_gaussianDominationCombinedDistance
    C_gaussianDominationCombined
  norm_num

/-- Constant used by Proposition \ref{P:better-induction}, formalized by
`betterInduction`. -/
noncomputable def C_betterInduction (k : ℕ) : ℝ :=
  ((2 : ℝ) ^ (15 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
    Real.sqrt 2) ^ (2 : ℕ)

/-- This auxiliary positivity fact supplies the admissibility condition on the
constant in `betterInduction`. -/
theorem aux_C_betterInduction_pos (k : ℕ) : 0 < C_betterInduction k := by
  unfold C_betterInduction
  apply sq_pos_of_pos
  apply add_pos_of_nonneg_of_pos
  · positivity
  · exact Real.sqrt_pos.2 (by norm_num)

/-- This auxiliary lower bound supplies the `C ∈ [1,∞)` hypothesis needed
when `betterInduction` invokes the preceding induction implication. -/
theorem aux_one_le_C_betterInduction (k : ℕ) : 1 ≤ C_betterInduction k := by
  unfold C_betterInduction
  have hmain : 0 ≤ (2 : ℝ) ^ (15 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) := by
    positivity
  have hroot : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsum : Real.sqrt 2 ≤ (2 : ℝ) ^ (15 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
        Real.sqrt 2 := by
    linarith
  have hsumnonneg : 0 ≤ (2 : ℝ) ^ (15 : ℕ) * (k + 2 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
        Real.sqrt 2 := by
    positivity
  have hsqrt : (Real.sqrt 2) ^ (2 : ℕ) = 2 := by
    rw [Real.sq_sqrt (by norm_num)]
  calc
    1 ≤ (Real.sqrt 2) ^ (2 : ℕ) := by rw [hsqrt]; norm_num
    _ ≤ ((2 : ℝ) ^ (15 : ℕ) * (k + 2 : ℕ) *
        Real.sqrt
          (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
        Real.sqrt 2) ^ (2 : ℕ) :=
      (sq_le_sq₀ hroot hsumnonneg).2 hsum

/-- Constant in Theorem \ref{induct positive terms theorem}, formalized by
`inductPositiveTermsTheorem`. -/
noncomputable def C_inductPositiveTermsTheorem : ℝ :=
  ((2 : ℝ) ^ (17 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
    Real.sqrt 2) ^ (2 : ℕ)

/-- Source label `\ref{constant induct positive terms theorem}`. -/
theorem constantInductPositiveTermsTheorem :
    C_inductPositiveTermsTheorem < (2 : ℝ) ^ (359 : ℕ) := by
  unfold C_inductPositiveTermsTheorem
  have hproduct :
      C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData =
        ((18 : ℝ) * (2 : ℝ) ^ (158 : ℕ)) ^ (2 : ℕ) := by
    unfold C_inductPositiveTermsImplyIncreaseData
      C_gaussianDominationCombinedCard C_gaussianDominationCombinedDistance
      C_gaussianDominationCombined
    norm_num
  rw [hproduct, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hsqrt : Real.sqrt 2 < (2 : ℝ) ^ (175 : ℕ) := by
    calc
      Real.sqrt 2 < 2 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ (2 : ℝ) ^ (175 : ℕ) := by norm_num
  have hsum :
      (2 : ℝ) ^ (17 : ℕ) * ((18 : ℝ) * (2 : ℝ) ^ (158 : ℕ)) + Real.sqrt 2 <
        (19 : ℝ) * (2 : ℝ) ^ (175 : ℕ) := by
    calc
      (2 : ℝ) ^ (17 : ℕ) * ((18 : ℝ) * (2 : ℝ) ^ (158 : ℕ)) + Real.sqrt 2 =
          (18 : ℝ) * (2 : ℝ) ^ (175 : ℕ) + Real.sqrt 2 := by norm_num
      _ < (18 : ℝ) * (2 : ℝ) ^ (175 : ℕ) + (2 : ℝ) ^ (175 : ℕ) := by gcongr
      _ = (19 : ℝ) * (2 : ℝ) ^ (175 : ℕ) := by ring
  calc
    ((2 : ℝ) ^ (17 : ℕ) * ((18 : ℝ) * (2 : ℝ) ^ (158 : ℕ)) + Real.sqrt 2) ^ (2 : ℕ) <
        ((19 : ℝ) * (2 : ℝ) ^ (175 : ℕ)) ^ (2 : ℕ) :=
      (sq_lt_sq₀ (by positivity) (by positivity)).mpr hsum
    _ = (19 : ℝ) ^ (2 : ℕ) * (2 : ℝ) ^ (175 * 2 : ℕ) := by
      rw [mul_pow, ← pow_mul]
    _ = (361 : ℝ) * (2 : ℝ) ^ (350 : ℕ) := by norm_num
    _ < (2 : ℝ) ^ (9 : ℕ) * (2 : ℝ) ^ (350 : ℕ) := by
      gcongr
      norm_num
    _ = (2 : ℝ) ^ (359 : ℕ) := by
      rw [← pow_add]

/-- This auxiliary positivity fact supplies the admissibility condition on the
constant in `inductPositiveTermsTheorem`. -/
theorem aux_C_inductPositiveTermsTheorem_pos :
    0 < C_inductPositiveTermsTheorem := by
  unfold C_inductPositiveTermsTheorem
  apply sq_pos_of_pos
  apply add_pos_of_nonneg_of_pos
  · positivity
  · exact Real.sqrt_pos.2 (by norm_num)

/-- This auxiliary lower bound supplies the admissibility condition on the
constant used in the final `inductPositiveTermsTheorem`. -/
theorem aux_one_le_C_inductPositiveTermsTheorem :
    1 ≤ C_inductPositiveTermsTheorem := by
  unfold C_inductPositiveTermsTheorem
  have hmain : 0 ≤ (2 : ℝ) ^ (17 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) := by
    positivity
  have hroot : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsum : Real.sqrt 2 ≤ (2 : ℝ) ^ (17 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
        Real.sqrt 2 := by
    linarith
  have hsumnonneg : 0 ≤ (2 : ℝ) ^ (17 : ℕ) *
      Real.sqrt
        (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
        Real.sqrt 2 := by
    positivity
  have hsqrt : (Real.sqrt 2) ^ (2 : ℕ) = 2 := by
    rw [Real.sq_sqrt (by norm_num)]
  calc
    1 ≤ (Real.sqrt 2) ^ (2 : ℕ) := by rw [hsqrt]; norm_num
    _ ≤ ((2 : ℝ) ^ (17 : ℕ) *
        Real.sqrt
          (C_gaussianDominationCombined * C_inductPositiveTermsImplyIncreaseData) +
        Real.sqrt 2) ^ (2 : ℕ) :=
      (sq_le_sq₀ hroot hsumnonneg).2 hsum

/-- Output constant from Proposition \ref{vanishing diagonal implies induct positive terms},
formalized by `vanishingDiagonal_implies_inductPositiveTerms`. -/
def C_vanishingDiagonalImpliesInductPositiveTerms (k : ℕ) (C : ℝ) : ℝ :=
  k * C + 2

/-- This auxiliary bound verifies the admissibility condition on the output
constant of `vanishingDiagonal_implies_inductPositiveTerms`. -/
theorem aux_one_le_C_vanishingDiagonalImpliesInductPositiveTerms (k : ℕ) {C : ℝ}
    (hC : 1 ≤ C) : 1 ≤ C_vanishingDiagonalImpliesInductPositiveTerms k C := by
  unfold C_vanishingDiagonalImpliesInductPositiveTerms
  have hnonneg : 0 ≤ (k : ℝ) * C :=
    mul_nonneg (Nat.cast_nonneg k) (by linarith)
  linarith

/-- Positivity lets one sandwich term be bounded by the finite sum of all sandwich terms. -/
theorem aux_kernelSequenceSeminorm_le_sum_of_positive {n : ℕ}
    (γ : GeometricParameters n) (X : DoubleSequence γ.k) (hX : MemDoubleSequence γ.k X)
    (hfactor : ∀ i j, ∃ f : ℝ → ℝ, MemW0 f ∧
      ∀ u v, X i j (u, v) = f u * f v) (i : Fin γ.k) :
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n (sandwichKernel γ X i) ≤
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (fun j y => ∑ q, sandwichKernel γ X q j y) := by
  classical
  unfold kernelSequenceSeminorm
  refine iSup_le fun J => ?_
  refine iSup_le fun F => ?_
  apply le_iSup_of_le J
  apply le_iSup_of_le F
  let w : ℝ := min 1
    (Real.rpow (J.1 : ℝ) (-1 + (2 : ℝ) ^ ((γ.k : ℤ) - (n : ℤ) + 1)))
  let p : Fin γ.k → ℤ → ℝ := fun q j =>
    prismForm n γ.k γ.one_le_k γ.k_le_n (sandwichKernel γ X q j) (fun a => F.1 a)
  have hmem (q : Fin γ.k) : MemKernelSequence γ.k (sandwichKernel γ X q) :=
    sandwichKernel_memKernelSequence γ X hX q
  have hlin_i :
      prismForm n γ.k γ.one_le_k γ.k_le_n
          (fun y => ∑ j ∈ Finset.range J.1, sandwichKernel γ X i (j : ℤ) y)
          (fun a => F.1 a) =
        ∑ j ∈ Finset.range J.1, p i (j : ℤ) := by
    simpa [p] using
      (aux_prismForm_finset_sum γ.one_le_k γ.k_le_n (Finset.range J.1)
        (fun j : ℕ => sandwichKernel γ X i (j : ℤ))
        (by
          intro j hj
          exact hmem i (j : ℤ)) F.1)
  have hmem_sum_j (j : ℕ) : MemW0 (fun y => ∑ q, sandwichKernel γ X q (j : ℤ) y) := by
    apply aux_memW0_finset_sum Finset.univ
    intro q hq
    exact hmem q (j : ℤ)
  have hlin_sum :
      prismForm n γ.k γ.one_le_k γ.k_le_n
          (fun y => ∑ j ∈ Finset.range J.1,
            (∑ q, sandwichKernel γ X q (j : ℤ) y))
          (fun a => F.1 a) =
        ∑ j ∈ Finset.range J.1, ∑ q, p q (j : ℤ) := by
    calc
      prismForm n γ.k γ.one_le_k γ.k_le_n
          (fun y => ∑ j ∈ Finset.range J.1,
            (∑ q, sandwichKernel γ X q (j : ℤ) y))
          (fun a => F.1 a) =
          ∑ j ∈ Finset.range J.1,
            prismForm n γ.k γ.one_le_k γ.k_le_n
              (fun y => ∑ q, sandwichKernel γ X q (j : ℤ) y)
              (fun a => F.1 a) := by
            simpa using
              (aux_prismForm_finset_sum γ.one_le_k γ.k_le_n (Finset.range J.1)
                (fun j : ℕ => fun y => ∑ q, sandwichKernel γ X q (j : ℤ) y)
                (by
                  intro j hj
                  exact hmem_sum_j j) F.1)
      _ = ∑ j ∈ Finset.range J.1, ∑ q,
          prismForm n γ.k γ.one_le_k γ.k_le_n
            (sandwichKernel γ X q (j : ℤ)) (fun a => F.1 a) := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa using
              (aux_prismForm_finset_sum γ.one_le_k γ.k_le_n Finset.univ
                (fun q : Fin γ.k => sandwichKernel γ X q (j : ℤ))
                (by
                  intro q hq
                  exact hmem q (j : ℤ)) F.1)
      _ = ∑ j ∈ Finset.range J.1, ∑ q, p q (j : ℤ) := by
            rfl
  have hnonneg (q : Fin γ.k) (j : ℤ) : 0 ≤ p q j := by
    dsimp [p]
    exact positiveTerms γ X hX hfactor q j F.1 F.2
  have hpi_nonneg : 0 ≤ ∑ j ∈ Finset.range J.1, p i (j : ℤ) := by
    apply Finset.sum_nonneg
    intro j hj
    exact hnonneg i (j : ℤ)
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range J.1, ∑ q, p q (j : ℤ) := by
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro q hq
    exact hnonneg q (j : ℤ)
  have hpi_le_sum :
      (∑ j ∈ Finset.range J.1, p i (j : ℤ)) ≤
        ∑ j ∈ Finset.range J.1, ∑ q, p q (j : ℤ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.single_le_sum (s := Finset.univ)
      (fun q _ => hnonneg q (j : ℤ)) (Finset.mem_univ i)
  change ENNReal.ofReal (w *
      |prismForm n γ.k γ.one_le_k γ.k_le_n
        (fun y => ∑ j ∈ Finset.range J.1, sandwichKernel γ X i (j : ℤ) y)
        (fun a => F.1 a)|) ≤
    ENNReal.ofReal (w *
      |prismForm n γ.k γ.one_le_k γ.k_le_n
        (fun y => ∑ j ∈ Finset.range J.1,
          (∑ q, sandwichKernel γ X q (j : ℤ) y))
        (fun a => F.1 a)|)
  rw [hlin_i, hlin_sum]
  have hw : 0 ≤ w := by
    dsimp [w]
    exact le_min zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [abs_of_nonneg hpi_nonneg, abs_of_nonneg hsum_nonneg]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpi_le_sum hw)

/--
\begin{proposition}
\label{vanishing diagonal implies induct positive terms}
Let $k\in\N$ with $1\le k\le n$ and $C\in [1,\infty)$.
If $\VanishingDiagonal{k,C}$ holds, then $\InductPositiveTerms{k,kC+2}$ holds.
\end{proposition}
-/
theorem vanishingDiagonal_implies_inductPositiveTerms {n k : ℕ} {C : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n) (hC : 1 ≤ C) :
    VanishingDiagonal n k C hk hkn hC →
      InductPositiveTerms n k (C_vanishingDiagonalImpliesInductPositiveTerms k C) hk hkn
        (aux_one_le_C_vanishingDiagonalImpliesInductPositiveTerms k hC) := by
  intro hvanishing
  unfold VanishingDiagonal at hvanishing
  unfold InductPositiveTerms
  intro γ hγ i
  classical
  let D : ℝ := Real.rpow (geometricDelta γ : ℝ)
    (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1))
  have hD : 1 ≤ D := by
    dsimp [D]
    exact aux_one_le_geometricDelta_rpow hk hkn γ
  have hfactor : ∀ q j, ∃ f : ℝ → ℝ, MemW0 f ∧
      ∀ u v, aux_sMultiplierTensorSquare γ q j (u, v) = f u * f v := by
    intro q j
    refine ⟨sMultiplier γ q j, sMultiplier_memW0 γ q j, ?_⟩
    intro u v
    rfl
  have hHmem (q : Fin γ.k) :
      MemKernelSequence γ.k (sandwichKernel γ (hMultiplier γ) q) :=
    sandwichKernel_memKernelSequence γ (hMultiplier γ) (hMultiplier_memDoubleSequence γ) q
  have htel := telescopingTerms γ
  have htel_eq :
      (fun j => ∑ q, sandwichKernel γ (gaussianDifference γ) q j) =
        (fun j y => ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) := by
    funext j y
    simp only [Finset.sum_apply]
  have hYmem (q : Fin γ.k) :
      MemKernelSequence γ.k (sandwichKernel γ (gaussianDifference γ) q) :=
    sandwichKernel_memKernelSequence γ (gaussianDifference γ) htel.1 q
  have hHsum_mem : MemKernelSequence γ.k
      (fun j y => ∑ q, sandwichKernel γ (hMultiplier γ) q j y) := by
    intro j
    apply aux_memW0_finset_sum Finset.univ
    intro q hq
    exact hHmem q j
  have hYsum_mem : MemKernelSequence γ.k
      (fun j y => ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) := by
    intro j
    apply aux_memW0_finset_sum Finset.univ
    intro q hq
    exact hYmem q j
  have hsplit :
      (fun j y => ∑ q, sandwichKernel γ (aux_sMultiplierTensorSquare γ) q j y) =
        fun j y =>
          (∑ q, sandwichKernel γ (hMultiplier γ) q j y) +
            ∑ q, sandwichKernel γ (gaussianDifference γ) q j y := by
    funext j y
    simp_rw [aux_sMultiplierTensorSquare_sandwich_eq γ]
    rw [Finset.sum_add_distrib]
  have hHbound :
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (hMultiplier γ) q j y) ≤
        ENNReal.ofReal ((γ.k : ℝ) * (C * D)) := by
    calc
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (hMultiplier γ) q j y) ≤
          ∑ q, kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
            (sandwichKernel γ (hMultiplier γ) q) := by
            simpa using
              (aux_kernelSequenceSeminorm_finset_sum_le γ.one_le_k γ.k_le_n Finset.univ
                (fun q => sandwichKernel γ (hMultiplier γ) q)
                (by
                  intro q hq
                  exact hHmem q))
      _ ≤ ∑ q, ENNReal.ofReal (C * D) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa [D] using hvanishing γ hγ q
      _ = ENNReal.ofReal ((γ.k : ℝ) * (C * D)) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (γ.k : ℝ))]
        norm_cast
        simp [nsmul_eq_mul]
  have hYbound :
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) ≤
        ENNReal.ofReal (2 * D) := by
    calc
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) ≤ 2 := by
            rw [← htel_eq]
            exact htel.2
      _ ≤ ENNReal.ofReal (2 * D) := by
        calc
          (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          _ ≤ ENNReal.ofReal (2 * D) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith
  have hsum_bound :
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (hMultiplier γ) q j y) +
        kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) ≤
        ENNReal.ofReal (((γ.k : ℝ) * C + 2) * D) := by
    calc
      kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (hMultiplier γ) q j y) +
        kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) ≤
          ENNReal.ofReal ((γ.k : ℝ) * (C * D)) + ENNReal.ofReal (2 * D) :=
        add_le_add hHbound hYbound
      _ ≤ ENNReal.ofReal (((γ.k : ℝ) * C + 2) * D) := by
        rw [← ENNReal.ofReal_add]
        · apply ENNReal.ofReal_le_ofReal
          ring_nf
          exact le_rfl
        · positivity
        · positivity
  calc
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (sandwichKernel γ (aux_sMultiplierTensorSquare γ) i) ≤
        kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (aux_sMultiplierTensorSquare γ) q j y) :=
      aux_kernelSequenceSeminorm_le_sum_of_positive γ (aux_sMultiplierTensorSquare γ)
        (aux_sMultiplierTensorSquare_memDoubleSequence γ) hfactor i
    _ = kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
        (fun j y =>
          (∑ q, sandwichKernel γ (hMultiplier γ) q j y) +
            ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) := by
        rw [hsplit]
    _ ≤ kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (hMultiplier γ) q j y) +
        kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (fun j y => ∑ q, sandwichKernel γ (gaussianDifference γ) q j y) :=
      kernelSequenceSeminorm_add_le γ.one_le_k γ.k_le_n _ _ hHsum_mem hYsum_mem
    _ ≤ ENNReal.ofReal (((γ.k : ℝ) * C + 2) * D) := hsum_bound
    _ = ENNReal.ofReal
        (C_vanishingDiagonalImpliesInductPositiveTerms k C *
          Real.rpow (geometricDelta γ : ℝ)
            (2 - (2 : ℝ) ^ ((k : ℤ) - (n : ℤ) + 1))) := by
        simp [C_vanishingDiagonalImpliesInductPositiveTerms, D, hγ]

/-- The symmetric partial sums of the sandwiched L multipliers converge in `L¹`. -/
private theorem aux_sandwichLMultiplierPartial_tendsto {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (j : ℤ) :
    Tendsto (fun N : ℕ =>
      eLpNorm (sandwichMultiplierIndexPartialSum γ (lMultiplier γ) i j N -
        sandwichKernel γ (hMultiplier γ) i j) 1 volume) atTop (nhds 0) := by
  let ι₀ : MultiplierIndex γ := ⟨(0, 0), by simp [multiplierIndexSet]⟩
  exact sandwichSumsL1 γ (hMultiplier γ) (lMultiplier γ)
    (hMultiplier_memDoubleSequence γ)
    (fun ι => lMultiplier_memDoubleSequence γ ι)
    (by
      intro i j
      change Tendsto (fun N : ℕ =>
        eLpNorm (lMultiplierPartialSum γ i j N - hMultiplier γ i j) 1 volume)
        atTop (nhds 0)
      exact (sumLMultiplierConvergenceL1 γ ι₀).2 i j)
    i j

/-- A finite sum over the scale index preserves the symmetric `L¹` convergence. -/
private theorem aux_finiteSandwichLMultiplier_convergesL1 {n : ℕ} (γ : GeometricParameters n)
    (i : Fin γ.k) (J : ℕ) :
    Tendsto (fun N : ℕ => eLpNorm
      (mKernelMultiplierIndexPartialSum γ
        (fun ι y => ∑ j ∈ Finset.range J,
          sandwichKernel γ (lMultiplier γ ι) i (j : ℤ) y) N -
        (fun y => ∑ j ∈ Finset.range J,
          sandwichKernel γ (hMultiplier γ) i (j : ℤ) y)) 1 volume)
      atTop (nhds 0) := by
  classical
  have hsum : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range J,
      eLpNorm (sandwichMultiplierIndexPartialSum γ (lMultiplier γ) i (j : ℤ) N -
        sandwichKernel γ (hMultiplier γ) i (j : ℤ)) 1 volume) atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.range J)
      (fun j _ => aux_sandwichLMultiplierPartial_tendsto γ i (j : ℤ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0)) hsum
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with N
    have hdiff :
        mKernelMultiplierIndexPartialSum γ
          (fun ι y => ∑ j ∈ Finset.range J,
            sandwichKernel γ (lMultiplier γ ι) i (j : ℤ) y) N -
          (fun y => ∑ j ∈ Finset.range J,
            sandwichKernel γ (hMultiplier γ) i (j : ℤ) y) =
          (fun y => ∑ j ∈ Finset.range J,
            (sandwichMultiplierIndexPartialSum γ (lMultiplier γ) i (j : ℤ) N y -
              sandwichKernel γ (hMultiplier γ) i (j : ℤ) y)) := by
      funext y
      simp only [mKernelMultiplierIndexPartialSum, sandwichMultiplierIndexPartialSum,
        Finset.sum_apply, Pi.sub_apply]
      have hterm (c : ℤ × ℤ) :
          (if h : c ∈ multiplierIndexSet γ then fun y =>
              ∑ j ∈ Finset.range J,
                sandwichKernel γ (lMultiplier γ ⟨c, h⟩) i (j : ℤ) y
            else 0) y =
            ∑ j ∈ Finset.range J,
              (if h : c ∈ multiplierIndexSet γ then
                sandwichKernel γ (lMultiplier γ ⟨c, h⟩) i (j : ℤ) else 0) y := by
          split_ifs <;> simp
      simp_rw [hterm]
      rw [Finset.sum_comm, Finset.sum_sub_distrib]
    let E : ℕ → MKernel γ.k := fun j =>
      sandwichMultiplierIndexPartialSum γ (lMultiplier γ) i (j : ℤ) N -
        sandwichKernel γ (hMultiplier γ) i (j : ℤ)
    have hEfun :
        (fun y => ∑ j ∈ Finset.range J,
          (sandwichMultiplierIndexPartialSum γ (lMultiplier γ) i (j : ℤ) N y -
            sandwichKernel γ (hMultiplier γ) i (j : ℤ) y)) =
          ∑ j ∈ Finset.range J, E j := by
      funext y
      simp [E]
    rw [hdiff, hEfun]
    change eLpNorm (∑ j ∈ Finset.range J, E j) 1 volume ≤
      ∑ j ∈ Finset.range J, eLpNorm (E j) 1 volume
    refine eLpNorm_sum_le (f := E) ?_ (by norm_num)
    intro j hj
    have hpartial : MemW0
        (sandwichMultiplierIndexPartialSum γ (lMultiplier γ) i (j : ℤ) N) := by
      change MemW0 (mKernelMultiplierIndexPartialSum γ
        (fun ι => sandwichKernel γ (lMultiplier γ ι) i (j : ℤ)) N)
      exact aux_mKernelMultiplierIndexPartialSum_memW0 γ
        (fun ι => sandwichKernel γ (lMultiplier γ ι) i (j : ℤ))
        (fun ι => sandwichKernel_memKernelSequence γ (lMultiplier γ ι)
          (lMultiplier_memDoubleSequence γ ι) i (j : ℤ)) N
    exact (aux_memW0_sub hpartial
      (sandwichKernel_memKernelSequence γ (hMultiplier γ)
        (hMultiplier_memDoubleSequence γ) i (j : ℤ))).aux_continuous.aestronglyMeasurable

/-- The H-multiplier sandwich seminorm is bounded by the symmetric L-multiplier sum. -/
private theorem aux_hMultiplier_seminorm_le_symmetricLMultiplierSum {n : ℕ}
    (γ : GeometricParameters n) (i : Fin γ.k) :
    kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
      (sandwichKernel γ (hMultiplier γ) i) ≤
      sumOverMultiplierIndexENNReal γ (fun ι =>
        kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
          (sandwichKernel γ (lMultiplier γ ι) i)) := by
  classical
  unfold kernelSequenceSeminorm sumOverMultiplierIndexENNReal
  refine iSup_le fun J => ?_
  refine iSup_le fun F => ?_
  let M : MKernel γ.k := fun y => ∑ j ∈ Finset.range J.1,
    sandwichKernel γ (hMultiplier γ) i (j : ℤ) y
  let Mι : MultiplierIndex γ → MKernel γ.k := fun ι y =>
    ∑ j ∈ Finset.range J.1, sandwichKernel γ (lMultiplier γ ι) i (j : ℤ) y
  have hM : MemW0 M := by
    dsimp [M]
    apply aux_memW0_finset_sum
    intro j hj
    exact sandwichKernel_memKernelSequence γ (hMultiplier γ)
      (hMultiplier_memDoubleSequence γ) i (j : ℤ)
  have hMι (ι : MultiplierIndex γ) : MemW0 (Mι ι) := by
    dsimp [Mι]
    apply aux_memW0_finset_sum
    intro j hj
    exact sandwichKernel_memKernelSequence γ (lMultiplier γ ι)
      (lMultiplier_memDoubleSequence γ ι) i (j : ℤ)
  have hconverges : Tendsto (fun N : ℕ => eLpNorm
      (mKernelMultiplierIndexPartialSum γ Mι N - M) 1 volume) atTop (nhds 0) := by
    simpa [M, Mι] using aux_finiteSandwichLMultiplier_convergesL1 γ i J.1
  have hprism := prismSumLeSumPrismL1 γ M Mι hM hMι hconverges F.1 F.2
  let w : ℝ := min 1
    (Real.rpow (J.1 : ℝ) (-1 + (2 : ℝ) ^ ((γ.k : ℤ) - (n : ℤ) + 1)))
  have hw : 0 ≤ w := by
    dsimp [w]
    exact le_min zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let P : ℝ := prismForm n γ.k γ.one_le_k γ.k_le_n M (fun a => F.1 a)
  have hprism' : ENNReal.ofReal |P| ≤
      ⨆ N, prismMultiplierIndexPartialAbsoluteSum γ Mι F.1 N := by
    simpa [P, Real.enorm_eq_ofReal_abs] using hprism
  change ENNReal.ofReal (w * |P|) ≤ _
  calc
    ENNReal.ofReal (w * |P|) = ENNReal.ofReal w * ENNReal.ofReal |P| :=
      ENNReal.ofReal_mul hw
    _ ≤ ENNReal.ofReal w * (⨆ N,
        prismMultiplierIndexPartialAbsoluteSum γ Mι F.1 N) := by gcongr
    _ = ⨆ N, ENNReal.ofReal w * prismMultiplierIndexPartialAbsoluteSum γ Mι F.1 N :=
      ENNReal.mul_iSup _ _
    _ ≤ _ := by
      refine iSup_le fun N => ?_
      apply le_iSup_of_le N
      unfold prismMultiplierIndexPartialAbsoluteSum
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro ξ hξ
      split_ifs with hξmem
      · change ENNReal.ofReal w *
            ‖prismForm n γ.k γ.one_le_k γ.k_le_n (Mι ⟨ξ, hξmem⟩)
              (fun a => F.1 a)‖ₑ ≤
            kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
              (sandwichKernel γ (lMultiplier γ ⟨ξ, hξmem⟩) i)
        have hterm : ENNReal.ofReal (w *
            |prismForm n γ.k γ.one_le_k γ.k_le_n (Mι ⟨ξ, hξmem⟩)
              (fun a => F.1 a)|) ≤
            kernelSequenceSeminorm n γ.k γ.one_le_k γ.k_le_n
              (sandwichKernel γ (lMultiplier γ ⟨ξ, hξmem⟩) i) := by
          unfold kernelSequenceSeminorm
          apply le_iSup_of_le J
          apply le_iSup_of_le F
          simp [w, Mι]
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hw]
        exact hterm
      · simp

/--
\begin{proposition}
\label{diagonal band implies vanishing diagonal}
Let $k\in\N$ with $1\le k\le n-1$ and $C\in [1,\infty)$.
If $\DiagonalBand{k,C}$ holds, then $\VanishingDiagonal{k,C}$ holds.
\end{proposition}
-/
theorem diagonalBand_implies_vanishingDiagonal {n k : ℕ} {C : ℝ}
    (hk : 1 ≤ k) (hkn : k ≤ n - 1) (hC : 1 ≤ C) :
    DiagonalBand n k C hk hkn hC → VanishingDiagonal n k C hk (by omega) hC := by
  intro hband
  unfold VanishingDiagonal
  intro γ hγ i
  exact (aux_hMultiplier_seminorm_le_symmetricLMultiplierSum γ i).trans (hband γ hγ i)

/-- Output constant from Proposition \ref{increase data implies diagonal band}, formalized by
`increaseData_implies_diagonalBand`. -/
noncomputable def C_increaseDataImpliesDiagonalBand (k n : ℕ) (C : ℝ) : ℝ :=
  if k < n - 1 then
    (2 : ℝ) ^ (15 : ℕ) * Real.sqrt C_gaussianDominationCombined * Real.sqrt C
  else
    (2 : ℝ) ^ (10 : ℕ) * C

/-- This auxiliary bound verifies the `C ∈ [1,∞)` side condition for the
two constants in `increaseData_implies_diagonalBand`. -/
theorem aux_one_le_C_increaseDataImpliesDiagonalBand (k n : ℕ) {C : ℝ}
    (hC : 1 ≤ C) : 1 ≤ C_increaseDataImpliesDiagonalBand k n C := by
  unfold C_increaseDataImpliesDiagonalBand
  split_ifs
  · calc
      1 ≤ Real.sqrt C_gaussianDominationCombined * Real.sqrt C := by
        apply one_le_mul_of_one_le_of_one_le
        · rw [C_gaussianDominationCombined]
          norm_num
        · exact (Real.one_le_sqrt).2 hC
      _ ≤ (2 : ℝ) ^ (15 : ℕ) * Real.sqrt C_gaussianDominationCombined *
          Real.sqrt C := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg C_gaussianDominationCombined)
          (Real.sqrt_nonneg C)]
  · calc
      1 ≤ C := hC
      _ ≤ (2 : ℝ) ^ (10 : ℕ) * C := by
        simpa using (mul_le_mul_of_nonneg_right
          (show (1 : ℝ) ≤ (2 : ℝ) ^ (10 : ℕ) by norm_num) (by linarith : 0 ≤ C))

/-- Recursive constants from Proposition \ref{P:C_k-induction}, formalized by
`inductPositiveTermsByInduction`.  The argument is the reverse distance from `n`. -/
noncomputable def C_inductPositiveTermsByInduction (n : ℕ) : ℕ → ℝ
  | 0 => (2 : ℝ) + n
  | Nat.succ 0 =>
      (2 : ℝ) + ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (10 : ℕ) *
        C_inductPositiveTermsImplyIncreaseData * C_inductPositiveTermsByInduction n 0
  | Nat.succ (Nat.succ r) =>
      (2 : ℝ) + ((n - (r + 2) : ℕ) : ℝ) * (2 : ℝ) ^ (15 : ℕ) *
      Real.sqrt C_gaussianDominationCombined *
        Real.sqrt
          (C_inductPositiveTermsImplyIncreaseData *
            C_inductPositiveTermsByInduction n (r + 1))

/-- This auxiliary induction establishes the admissibility side condition for
the recursive constants in `inductPositiveTermsByInduction`. -/
theorem aux_one_le_C_inductPositiveTermsByInduction (n r : ℕ) :
    1 ≤ C_inductPositiveTermsByInduction n r := by
  induction r with
  | zero =>
      change (1 : ℝ) ≤ 2 + (n : ℝ)
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
  | succ r ih =>
      cases r with
      | zero =>
          simp only [C_inductPositiveTermsByInduction]
          have hinc : 0 ≤ C_inductPositiveTermsImplyIncreaseData :=
            aux_C_inductPositiveTermsImplyIncreaseData_pos.le
          have hnonneg : 0 ≤ ((n - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (10 : ℕ) *
              C_inductPositiveTermsImplyIncreaseData * ((2 : ℝ) + n) := by
            positivity
          linarith
      | succ r =>
          simp only [C_inductPositiveTermsByInduction]
          have hprev : 0 ≤ C_inductPositiveTermsByInduction n (r + 1) := by
            linarith
          have hinc : 0 ≤ C_inductPositiveTermsImplyIncreaseData :=
            aux_C_inductPositiveTermsImplyIncreaseData_pos.le
          have hnonneg : 0 ≤ ((n - (r + 2) : ℕ) : ℝ) * (2 : ℝ) ^ (15 : ℕ) *
              Real.sqrt C_gaussianDominationCombined *
                Real.sqrt
                  (C_inductPositiveTermsImplyIncreaseData *
                    C_inductPositiveTermsByInduction n (r + 1)) := by
            positivity
          linarith

end

end Codex.MainArgument.MainInduction
