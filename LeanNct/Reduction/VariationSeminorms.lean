import Mathlib

/-!
# Variation seminorms

The finite variation seminorms used in the reduction argument.
-/

namespace Codex.Reduction.VariationSeminorms

open MeasureTheory Set
open scoped BigOperators ENNReal

/--
For a map `a : I → B`, this is the finite `r`-variation seminorm with at most
`J` jumps:
\[
 \|a\|_{V_{r,J}(I; B)} = \sup_{0\le M\le J}\ \sup_{t_0<\cdots<t_M,\ t_j\in I}
 \Big(\sum_{j\in[M)} \|a(t_{j+1})-a(t_j)\|^r\Big)^{1/r}.
\]
The Lean implementation uses monotone chains with exactly `J + 1` entries.
Repeated entries contribute zero, so for the intended range `1 ≤ r` this is
equivalent to taking the displayed supremum over strict chains with at most
`J` jumps. The value is encoded in `ℝ≥0∞`, so that the defining supremum is
also meaningful when it is unbounded. -/
noncomputable def finiteVariationSeminorm {B : Type*} [SeminormedAddCommGroup B]
    {I : Set ℝ} (a : I → B) (r : ℝ) (J : ℕ) : ℝ≥0∞ :=
  ⨆ (t : {u : Fin (J + 1) → I // Monotone u}),
    (∑ j : Fin J,
      (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹

/-- Auxiliary dyadic interval for `shortlongJumps`. -/
noncomputable def aux_dyadicInterval (k : ℤ) : Set ℝ :=
  Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))

/-- Auxiliary logarithmic measure `dt / t` on the interval `[α, β]`, used by `ftcCsR`. -/
noncomputable def aux_logarithmicMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc α β)).withDensity fun t ↦ ENNReal.ofReal t⁻¹

/-- Auxiliary `L²(dt/t)` norm used by `ftcCsR`. -/
noncomputable def aux_logarithmicL2 (α β : ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  eLpNorm f 2 (aux_logarithmicMeasure α β)

/-- The finite-dimensional three-term Minkowski estimate used in
`shortlongJumps`. -/
private theorem aux_lrpow_three_le {M : ℕ} (r : ℝ) (hr : 1 ≤ r)
    (d u v w : Fin M → ℝ≥0∞)
    (h : ∀ j, d j ≤ u j + v j + w j) :
    (∑ j, d j ^ r) ^ r⁻¹ ≤
      (∑ j, u j ^ r) ^ r⁻¹ + (∑ j, v j ^ r) ^ r⁻¹ +
        (∑ j, w j ^ r) ^ r⁻¹ := by
  calc
    (∑ j, d j ^ r) ^ r⁻¹ ≤ (∑ j, (u j + v j + w j) ^ r) ^ r⁻¹ := by
      gcongr with j
      exact h j
    _ ≤ (∑ j, (u j + v j) ^ r) ^ r⁻¹ + (∑ j, w j ^ r) ^ r⁻¹ := by
      simpa [Finset.sum_add_distrib] using
        (ENNReal.Lp_add_le (s := Finset.univ) (f := fun j : Fin M ↦ u j + v j)
          (g := fun j : Fin M ↦ w j) hr)
    _ ≤ ((∑ j, u j ^ r) ^ r⁻¹ + (∑ j, v j ^ r) ^ r⁻¹) +
        (∑ j, w j ^ r) ^ r⁻¹ := by
      gcongr
      simpa [Finset.sum_add_distrib] using
        (ENNReal.Lp_add_le (s := Finset.univ) (f := u) (g := v) hr)

/-- A single monotone chain is one candidate in the defining variation
supremum. -/
private theorem aux_chainVariation_le {B : Type*} [SeminormedAddCommGroup B]
    {I : Set ℝ} (a : I → B) (r : ℝ) (J : ℕ)
    (t : Fin (J + 1) → I) (ht : Monotone t) :
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
        finiteVariationSeminorm a r J := by
  exact le_iSup (fun t : {u : Fin (J + 1) → I // Monotone u} ↦
    (∑ j : Fin J,
      (‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹) ⟨t, ht⟩

/-- The two endpoints of a closed dyadic interval are ordered. -/
private theorem aux_dyadicLower_le_upper (k : ℤ) :
    (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) :=
  zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- The left endpoint of a dyadic interval, packaged as a point of that interval. -/
private noncomputable def aux_dyadicLowerPoint (k : ℤ) : aux_dyadicInterval k :=
  ⟨(2 : ℝ) ^ k, ⟨le_rfl, aux_dyadicLower_le_upper k⟩⟩

/-- Clamp a monotone chain to one dyadic interval. -/
private noncomputable def aux_dyadicLocalChain (J : ℕ) (k : ℤ)
    (t : Fin (J + 1) → ℝ) : Fin (J + 1) → aux_dyadicInterval k :=
  fun j ↦ Set.projIcc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))
    (aux_dyadicLower_le_upper k) (t j)

/-- Clamping preserves monotonicity. -/
private theorem aux_dyadicLocalChain_mono {J : ℕ} {k : ℤ} {t : Fin (J + 1) → ℝ}
    (ht : Monotone t) : Monotone (aux_dyadicLocalChain J k t) := by
  exact (Set.monotone_projIcc _).comp ht

/-- A clamped point already inside its dyadic interval is unchanged. -/
private theorem aux_dyadicLocalChain_eq_of_mem {J : ℕ} {k : ℤ}
    {t : Fin (J + 1) → ℝ} {j : Fin (J + 1)}
    (hj : t j ∈ Set.Icc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) :
    (aux_dyadicLocalChain J k t j : ℝ) = t j := by
  simpa [aux_dyadicLocalChain] using congrArg Subtype.val
    (Set.projIcc_of_mem (h := aux_dyadicLower_le_upper k) hj)

/-- A clamped point before a dyadic interval becomes its left endpoint. -/
private theorem aux_dyadicLocalChain_eq_left {J : ℕ} {k : ℤ}
    {t : Fin (J + 1) → ℝ} {j : Fin (J + 1)} (hj : t j ≤ (2 : ℝ) ^ k) :
    (aux_dyadicLocalChain J k t j : ℝ) = (2 : ℝ) ^ k := by
  simpa [aux_dyadicLocalChain] using congrArg Subtype.val
    (Set.projIcc_of_le_left (h := aux_dyadicLower_le_upper k) hj)

/-- The local variation of a clamped chain is bounded by its dyadic variation. -/
private theorem aux_dyadicLocal_sum_le_variation_rpow {B : Type*} [SeminormedAddCommGroup B]
    {J : ℕ} {k : ℤ} {t : Fin (J + 1) → ℝ} (ht : Monotone t)
    (a : ℝ → B) (r : ℝ) (hr : 1 ≤ r) :
    (∑ j : Fin J,
      (‖a (aux_dyadicLocalChain J k t j.succ) -
        a (aux_dyadicLocalChain J k t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ≤
      (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
  let c : {u : Fin (J + 1) → aux_dyadicInterval k // Monotone u} :=
    ⟨aux_dyadicLocalChain J k t, aux_dyadicLocalChain_mono ht⟩
  have hc := aux_chainVariation_le (fun s : aux_dyadicInterval k ↦ a s) r J c.1 c.2
  have hpos : 0 ≤ r := le_trans zero_le_one hr
  have hne : r ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hr)
  have hp := ENNReal.rpow_le_rpow hc hpos
  simpa [c, ENNReal.rpow_inv_rpow hne] using hp

/-- A monotone chain whose only nonzero increment is from the lower endpoint
to a specified point of a dyadic interval. -/
private noncomputable def aux_dyadicPairChain (J : ℕ) (k : ℤ)
    (x : aux_dyadicInterval k) : Fin (J + 1) → aux_dyadicInterval k :=
  Fin.cases (aux_dyadicLowerPoint k) (fun _ ↦ x)

/-- The padded dyadic pair chain is monotone. -/
private theorem aux_dyadicPairChain_mono {J : ℕ} {k : ℤ} (x : aux_dyadicInterval k) :
    Monotone (aux_dyadicPairChain J k x) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      rfl
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      change (2 : ℝ) ^ k ≤ (x : ℝ)
      exact x.2.1
  · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi
    have hjpos : (0 : Fin (J + 1)) < j := lt_of_lt_of_le (Fin.succ_pos i) hij
    have hj : j ≠ 0 := Fin.ne_of_gt hjpos
    obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
    simp [aux_dyadicPairChain]

/-- Evaluate the padded dyadic pair chain at its initial point. -/
private theorem aux_dyadicPairChain_zero {J : ℕ} {k : ℤ} (x : aux_dyadicInterval k) :
    aux_dyadicPairChain J k x 0 = aux_dyadicLowerPoint k := by
  simp [aux_dyadicPairChain]

/-- Evaluate the padded dyadic pair chain away from its initial point. -/
private theorem aux_dyadicPairChain_succ {J : ℕ} {k : ℤ}
    (x : aux_dyadicInterval k) (j : Fin J) :
    aux_dyadicPairChain J k x j.succ = x := by
  simp [aux_dyadicPairChain]

/-- The energy of the padded dyadic pair has one nonzero increment. -/
private theorem aux_dyadicPair_sum {B : Type*} [SeminormedAddCommGroup B]
    {M : ℕ} {k : ℤ} (a : ℝ → B) (r : ℝ) (hr : 0 < r)
    (x : aux_dyadicInterval k) :
    (∑ j : Fin (M + 1),
      (‖a (aux_dyadicPairChain (M + 1) k x j.succ) -
        a (aux_dyadicPairChain (M + 1) k x j.castSucc)‖₊ : ℝ≥0∞) ^ r) =
      (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r := by
  rw [Fin.sum_univ_succ]
  rw [aux_dyadicPairChain_succ x 0]
  simp only [Fin.castSucc_zero]
  rw [aux_dyadicPairChain_zero x]
  simp [aux_dyadicPairChain, aux_dyadicLowerPoint, ENNReal.zero_rpow_of_pos hr]

/-- A dyadic lower-endpoint tail is bounded by the corresponding local
variation whenever there is at least one available jump. -/
private theorem aux_dyadicPair_le_variation_rpow {B : Type*} [SeminormedAddCommGroup B]
    {J : ℕ} (hJ : 0 < J) {k : ℤ} (a : ℝ → B) (r : ℝ) (hr : 1 ≤ r)
    (x : aux_dyadicInterval k) :
    (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r ≤
      (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ.ne'
  let c : {u : Fin (M + 1 + 1) → aux_dyadicInterval k // Monotone u} :=
    ⟨aux_dyadicPairChain (M + 1) k x, aux_dyadicPairChain_mono x⟩
  have hc := aux_chainVariation_le (fun s : aux_dyadicInterval k ↦ a s) r (M + 1) c.1 c.2
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpos : 0 ≤ r := hrpos.le
  have hne : r ≠ 0 := ne_of_gt hrpos
  have hp := ENNReal.rpow_le_rpow hc hpos
  rw [show (∑ j : Fin (M + 1),
      (‖(fun s : aux_dyadicInterval k ↦ a s) (c.1 j.succ) -
        (fun s : aux_dyadicInterval k ↦ a s) (c.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) =
      (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r by
        simpa [c] using aux_dyadicPair_sum (M := M) (k := k) a r hrpos x] at hp
  simpa [ENNReal.rpow_inv_rpow hne] using hp

/-- The dyadic interval index of a real number; values outside the positive
half-line are immaterial to `shortlongJumps`. -/
private noncomputable def aux_dyadicIndex (x : ℝ) : ℤ :=
  if hx : 0 < x then
    (exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)).choose
  else 0

/-- A positive point belongs to the dyadic interval indexed by
`aux_dyadicIndex`. -/
private theorem aux_dyadicIndex_spec (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ^ aux_dyadicIndex x ≤ x ∧ x < (2 : ℝ) ^ (aux_dyadicIndex x + 1) := by
  rw [aux_dyadicIndex, dif_pos hx]
  simpa only [Set.mem_Ico] using
    (exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)).choose_spec

/-- Dyadic interval indices respect the order on positive reals. -/
private theorem aux_dyadicIndex_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    aux_dyadicIndex x ≤ aux_dyadicIndex y := by
  have hy : 0 < y := hx.trans_le hxy
  by_contra h
  have hlt : aux_dyadicIndex y < aux_dyadicIndex x := lt_of_not_ge h
  have hsucc : aux_dyadicIndex y + 1 ≤ aux_dyadicIndex x := Int.add_one_le_iff.mpr hlt
  have hpow : (2 : ℝ) ^ (aux_dyadicIndex y + 1) ≤ (2 : ℝ) ^ aux_dyadicIndex x :=
    (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hsucc
  exact (not_lt_of_ge (hpow.trans ((aux_dyadicIndex_spec x hx).1.trans hxy)))
    (aux_dyadicIndex_spec y hy).2

/-- The dyadic interval label is unique. -/
private theorem aux_dyadicIndex_eq_of_mem {x : ℝ} {k : ℤ} (hx : 0 < x)
    (hk : (2 : ℝ) ^ k ≤ x ∧ x < (2 : ℝ) ^ (k + 1)) : aux_dyadicIndex x = k := by
  apply le_antisymm
  · by_contra h
    have hlt : k < aux_dyadicIndex x := lt_of_not_ge h
    have hsucc : k + 1 ≤ aux_dyadicIndex x := Int.add_one_le_iff.mpr hlt
    have hpow : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ aux_dyadicIndex x :=
      (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hsucc
    exact (not_lt_of_ge (hpow.trans (aux_dyadicIndex_spec x hx).1)) hk.2
  · by_contra h
    have hlt : aux_dyadicIndex x < k := lt_of_not_ge h
    have hsucc : aux_dyadicIndex x + 1 ≤ k := Int.add_one_le_iff.mpr hlt
    have hpow : (2 : ℝ) ^ (aux_dyadicIndex x + 1) ≤ (2 : ℝ) ^ k :=
      (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hsucc
    exact (not_lt_of_ge (hpow.trans hk.1)) (aux_dyadicIndex_spec x hx).2

/-- The finite set of occupied dyadic intervals of a finite positive chain. -/
private noncomputable def aux_dyadicSet {J : ℕ} (t : Fin (J + 1) → ℝ) : Finset ℤ :=
  Finset.univ.image (fun j ↦ aux_dyadicIndex (t j))

/-- Characterize the occupied dyadic interval set. -/
private theorem aux_mem_dyadicSet_iff {J : ℕ} (t : Fin (J + 1) → ℝ)
    (ht : ∀ j, 0 < t j) (k : ℤ) :
    k ∈ aux_dyadicSet t ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1) := by
  constructor
  · intro hk
    rcases Finset.mem_image.mp hk with ⟨j, -, rfl⟩
    exact ⟨j, aux_dyadicIndex_spec _ (ht j)⟩
  · rintro ⟨j, hj₁, hj₂⟩
    have heq := aux_dyadicIndex_eq_of_mem (ht j) ⟨hj₁, hj₂⟩
    rw [← heq]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- The transitions that cross to a strictly later dyadic interval. -/
private def aux_crossIndices {J : ℕ} (b : Fin (J + 1) → ℤ) : Finset (Fin J) :=
  Finset.univ.filter fun j ↦ b j.castSucc < b j.succ

/-- A monotone label sequence leaves every occupied dyadic interval at most once. -/
private theorem aux_crossIndices_b_injective {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) :
    Function.Injective (fun j : aux_crossIndices b ↦ b j.1.castSucc) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hcross := Finset.mem_filter.mp i.2 |>.2
    have hsuc_le : i.1.succ ≤ j.1.castSucc :=
      Fin.succ_le_castSucc_iff.mpr hijlt
    have hlt : b i.1.castSucc < b j.1.castSucc := hcross.trans_le (hb hsuc_le)
    exact hlt.ne hij
  · have hcross := Finset.mem_filter.mp j.2 |>.2
    have hsuc_le : j.1.succ ≤ i.1.castSucc :=
      Fin.succ_le_castSucc_iff.mpr hjilt
    have hlt : b j.1.castSucc < b i.1.castSucc := hcross.trans_le (hb hsuc_le)
    exact hlt.ne hij.symm

/-- Sum terms supported on dyadic crossings using their distinct source labels. -/
private theorem aux_sum_cross_le_image {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) (q : Fin J → ℝ≥0∞) (V : ℤ → ℝ≥0∞)
    (hsupport : ∀ j, j ∉ aux_crossIndices b → q j = 0)
    (hle : ∀ j ∈ aux_crossIndices b, q j ≤ V (b j.castSucc)) :
    ∑ j, q j ≤ ∑ k ∈ (aux_crossIndices b).image (fun j ↦ b j.castSucc), V k := by
  let S := aux_crossIndices b
  calc
    ∑ j, q j = ∑ j ∈ S, q j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      exact hsupport j hj
    _ ≤ ∑ j ∈ S, V (b j.castSucc) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hle j hj
    _ = ∑ k ∈ S.image (fun j ↦ b j.castSucc), V k := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      have hsub : (⟨x, hx⟩ : S) = ⟨y, hy⟩ := aux_crossIndices_b_injective hb hxy
      exact congrArg Subtype.val hsub

/-- Extend the crossing estimate to the full finite set of occupied labels. -/
private theorem aux_sum_cross_le_kappa {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) (q : Fin J → ℝ≥0∞) (V : ℤ → ℝ≥0∞)
    (hsupport : ∀ j, j ∉ aux_crossIndices b → q j = 0)
    (hle : ∀ j ∈ aux_crossIndices b, q j ≤ V (b j.castSucc))
    (κ : Finset ℤ)
    (hκ : (aux_crossIndices b).image (fun j ↦ b j.castSucc) ⊆ κ) :
    ∑ j, q j ≤ ∑ k ∈ κ, V k := by
  exact (aux_sum_cross_le_image hb q V hsupport hle).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hκ fun _ _ _ ↦ by positivity)

/-- A diagonal finite sum is bounded by the sum of all its fibers. -/
private theorem aux_diagonal_sum_le {J : ℕ} {κ : Finset ℤ} (c : Fin J → ℤ)
    (hc : ∀ j, c j ∈ κ) (F : ℤ → Fin J → ℝ≥0∞) :
    ∑ j, F (c j) j ≤ ∑ k ∈ κ, ∑ j, F k j := by
  calc
    ∑ j, F (c j) j ≤ ∑ j, ∑ k ∈ κ, F k j := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.single_le_sum (f := fun k ↦ F k j) (fun _ _ ↦ by positivity) (hc j)
    _ = ∑ k ∈ κ, ∑ j, F k j := by
      rw [Finset.sum_comm]

/-- Lemma \ref{lem:shortlongjumps}. For every increasing positive sequence,
the finite variation of its jumps is controlled by its short dyadic variations and
its long dyadic variation; consequently the corresponding global variation obeys
the same estimate. -/
theorem shortlongJumps {B : Type*} [SeminormedAddCommGroup B]
    (a : ℝ → B) (J : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    (∀ (t : Fin (J + 1) → ℝ), Monotone t → (∀ j, 0 < t j) →
      ∃ κ : Finset ℤ,
        (∀ k, k ∈ κ ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) ∧
        (∑ j : Fin J,
          (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
          2 * (∑ k ∈ κ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
          finiteVariationSeminorm
            (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J) ∧
    finiteVariationSeminorm (fun s : Set.Ioi (0 : ℝ) ↦ a s) r J ≤
      2 * (∑' k : ℤ,
        (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
      finiteVariationSeminorm
        (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
  classical
  have hlocalFinite :
      ∀ (t : Fin (J + 1) → ℝ), Monotone t → (∀ j, 0 < t j) →
        ∃ κ : Finset ℤ,
          (∀ k, k ∈ κ ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) ∧
          (∑ j : Fin J,
            (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
            2 * (∑ k ∈ κ,
              (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
            finiteVariationSeminorm
              (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
    intro t ht htpos
    let L : Fin (J + 1) → ℤ := fun j ↦ aux_dyadicIndex (t j)
    let κ : Finset ℤ := aux_dyadicSet t
    refine ⟨κ, ?_, ?_⟩
    · simpa [κ] using aux_mem_dyadicSet_iff t htpos
    have hLmono : Monotone L := by
      intro i j hij
      exact aux_dyadicIndex_mono (htpos i) (ht hij)
    let d : Fin J → ℝ≥0∞ := fun j ↦ ‖a (t j.succ) - a (t j.castSucc)‖₊
    let u : Fin J → ℝ≥0∞ := fun j ↦
      if L j.castSucc = L j.succ then
        ‖a (t j.succ) - a (t j.castSucc)‖₊
      else ‖a (t j.succ) - a ((2 : ℝ) ^ L j.succ)‖₊
    let v : Fin J → ℝ≥0∞ := fun j ↦
      ‖a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)‖₊
    let w : Fin J → ℝ≥0∞ := fun j ↦
      if L j.castSucc < L j.succ then
        ‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊
      else 0
    have hd_uvw (j : Fin J) : d j ≤ u j + v j + w j := by
      dsimp [d, u, v, w]
      by_cases hEq : L j.castSucc = L j.succ
      · simp [hEq]
      · have hle : L j.castSucc ≤ L j.succ := hLmono (Fin.castSucc_le_succ j)
        have hlt : L j.castSucc < L j.succ := lt_of_le_of_ne hle hEq
        rw [if_neg hEq, if_pos hlt]
        have hid : a (t j.succ) - a (t j.castSucc) =
            (a (t j.succ) - a ((2 : ℝ) ^ L j.succ)) +
              (a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)) +
              (a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)) := by
          abel
        rw [hid]
        have htri :
            ‖(a (t j.succ) - a ((2 : ℝ) ^ L j.succ)) +
                  (a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)) +
                  (a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc))‖₊ ≤
                ‖a (t j.succ) - a ((2 : ℝ) ^ L j.succ)‖₊ +
                  ‖a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc)‖₊ +
                  ‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊ := by
          calc
            _ ≤ ‖(a (t j.succ) - a ((2 : ℝ) ^ L j.succ)) +
                  (a ((2 : ℝ) ^ L j.succ) - a ((2 : ℝ) ^ L j.castSucc))‖₊ +
                  ‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊ :=
                nnnorm_add_le _ _
            _ ≤ _ := by
              gcongr
              exact nnnorm_add_le _ _
        exact_mod_cast htri
    have hMink := aux_lrpow_three_le r hr d u v w hd_uvw
    have hA : (∑ j : Fin J, u j ^ r) ≤
        ∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
      let F : ℤ → Fin J → ℝ≥0∞ := fun k j ↦
        (‖a (aux_dyadicLocalChain J k t j.succ) -
          a (aux_dyadicLocalChain J k t j.castSucc)‖₊ : ℝ≥0∞) ^ r
      have hlabel_mem (j : Fin J) : L j.succ ∈ κ := by
        simp [κ, aux_dyadicSet, L]
      have hdiag := aux_diagonal_sum_le (fun j ↦ L j.succ) hlabel_mem F
      have hF_le (k : ℤ) : ∑ j : Fin J, F k j ≤
          (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
        exact aux_dyadicLocal_sum_le_variation_rpow ht a r hr
      calc
        ∑ j : Fin J, u j ^ r ≤ ∑ j : Fin J, F (L j.succ) j := by
          apply Finset.sum_le_sum
          intro j _
          dsimp [u, F]
          by_cases hEq : L j.castSucc = L j.succ
          · simp [hEq]
            have hs : t j.succ ∈ Set.Icc ((2 : ℝ) ^ L j.succ)
                ((2 : ℝ) ^ (L j.succ + 1)) := by
              simpa [L] using
                ⟨(aux_dyadicIndex_spec _ (htpos j.succ)).1,
                  (aux_dyadicIndex_spec _ (htpos j.succ)).2.le⟩
            have hp : t j.castSucc ∈ Set.Icc ((2 : ℝ) ^ L j.succ)
                ((2 : ℝ) ^ (L j.succ + 1)) := by
              have hlabel : aux_dyadicIndex (t j.castSucc) =
                  aux_dyadicIndex (t j.succ) := by
                simpa [L] using hEq
              have hspec := aux_dyadicIndex_spec (t j.castSucc) (htpos j.castSucc)
              rw [hlabel] at hspec
              simpa [L] using ⟨hspec.1, hspec.2.le⟩
            rw [aux_dyadicLocalChain_eq_of_mem hs,
              aux_dyadicLocalChain_eq_of_mem hp]
          · have hle := hLmono (Fin.castSucc_le_succ j)
            have hlt : L j.castSucc < L j.succ := lt_of_le_of_ne hle hEq
            simp [hEq]
            have hs : t j.succ ∈ Set.Icc ((2 : ℝ) ^ L j.succ)
                ((2 : ℝ) ^ (L j.succ + 1)) := by
              simpa [L] using
                ⟨(aux_dyadicIndex_spec _ (htpos j.succ)).1,
                  (aux_dyadicIndex_spec _ (htpos j.succ)).2.le⟩
            have hstep : L j.castSucc + 1 ≤ L j.succ := Int.add_one_le_iff.mpr hlt
            have hpw : (2 : ℝ) ^ (L j.castSucc + 1) ≤ (2 : ℝ) ^ L j.succ :=
              (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hstep
            have hp : t j.castSucc ≤ (2 : ℝ) ^ L j.succ :=
              (aux_dyadicIndex_spec _ (htpos j.castSucc)).2.le.trans hpw
            rw [aux_dyadicLocalChain_eq_of_mem hs,
              aux_dyadicLocalChain_eq_left hp]
        _ ≤ ∑ k ∈ κ, ∑ j, F k j := hdiag
        _ ≤ ∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
          apply Finset.sum_le_sum
          intro k hk
          exact hF_le k
    have hB : (∑ j : Fin J, v j ^ r) ^ r⁻¹ ≤
        finiteVariationSeminorm
          (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
      let q : {x : Fin (J + 1) → Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) // Monotone x} :=
        ⟨fun i ↦ ⟨(2 : ℝ) ^ L i, ⟨L i, rfl⟩⟩, by
          intro i j hij
          exact (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr
            (hLmono hij)⟩
      simpa [v, q] using
        aux_chainVariation_le
          (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J q.1 q.2
    have hCsum : (∑ j : Fin J, w j ^ r) ≤
        ∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by
      apply aux_sum_cross_le_kappa hLmono (fun j ↦ w j ^ r)
        (fun k ↦ (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r)
      · intro j hj
        dsimp [w]
        have hj' : ¬ L j.castSucc < L j.succ := by
          intro h
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        simp [hj', ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hr)]
      · intro j hj
        have hlt := Finset.mem_filter.mp hj |>.2
        dsimp [w]
        rw [if_pos hlt]
        let x : aux_dyadicInterval (L j.castSucc) :=
          ⟨t j.castSucc, (aux_dyadicIndex_spec _ (htpos j.castSucc)).1,
            (aux_dyadicIndex_spec _ (htpos j.castSucc)).2.le⟩
        have hp := aux_dyadicPair_le_variation_rpow (Nat.zero_lt_of_lt j.isLt) a r hr x
        have hrev :
            (‖a ((2 : ℝ) ^ L j.castSucc) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r =
              (‖a (t j.castSucc) - a ((2 : ℝ) ^ L j.castSucc)‖₊ : ℝ≥0∞) ^ r := by
          congr 2
          apply NNReal.eq
          exact norm_sub_rev _ _
        exact hrev.trans_le (by simpa [x] using hp)
      · intro k hk
        rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
        simp [κ, aux_dyadicSet, L]
    have hC : (∑ j : Fin J, w j ^ r) ^ r⁻¹ ≤
        (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ :=
      ENNReal.rpow_le_rpow hCsum (by positivity)
    have hAsh : (∑ j : Fin J, u j ^ r) ^ r⁻¹ ≤
        (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ :=
      ENNReal.rpow_le_rpow hA (by positivity)
    calc
      (∑ j : Fin J, (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ =
          (∑ j : Fin J, d j ^ r) ^ r⁻¹ := by rfl
      _ ≤ (∑ j, u j ^ r) ^ r⁻¹ + (∑ j, v j ^ r) ^ r⁻¹ + (∑ j, w j ^ r) ^ r⁻¹ := hMink
      _ ≤ (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
          finiteVariationSeminorm (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J +
          (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ := by
        gcongr
      _ = 2 * (∑ k ∈ κ, (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
          finiteVariationSeminorm (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
        ring
  constructor
  · exact hlocalFinite
  · unfold finiteVariationSeminorm
    apply iSup_le
    intro q
    have hlocal := hlocalFinite (fun j ↦ q.1 j) q.2
      (fun j ↦ (q.1 j).2)
    rcases hlocal with ⟨κ, hκ, hlocal⟩
    calc
      (∑ j : Fin J, (‖a (q.1 j.succ) - a (q.1 j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
          2 * (∑ k ∈ κ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
            finiteVariationSeminorm
              (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := hlocal
      _ ≤ 2 * (∑' k : ℤ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
            finiteVariationSeminorm
              (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by
        gcongr
        exact ENNReal.sum_le_tsum κ

/-- Consecutive intervals cut out by a monotone finite chain are disjoint, so
their nonnegative integrals are bounded by the integral on the ambient
interval. -/
private theorem aux_sum_lintegral_Ioc_le {J : ℕ} {μ : Measure ℝ}
    (t : Fin (J + 1) → ℝ) (ht : Monotone t) (f : ℝ → ℝ≥0∞)
    {α β : ℝ} (hα : α ≤ t 0) (hβ : t (Fin.last J) ≤ β) :
    (∑ j : Fin J, ∫⁻ x in Set.Ioc (t j.castSucc) (t j.succ), f x ∂μ) ≤
      ∫⁻ x in Set.Icc α β, f x ∂μ := by
  let s : Fin J → Set ℝ := fun j ↦ Set.Ioc (t j.castSucc) (t j.succ)
  have hs_meas (j : Fin J) : MeasurableSet (s j) := measurableSet_Ioc
  have hs_disjoint : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin J))) s := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact Ioc_disjoint_Ioc_of_le (ht (Fin.succ_le_castSucc_iff.mpr hijlt))
    · exact (Ioc_disjoint_Ioc_of_le
        (ht (Fin.succ_le_castSucc_iff.mpr hjilt))).symm
  have hsum : (∑ j : Fin J, ∫⁻ x in s j, f x ∂μ) =
      ∫⁻ x in ⋃ j ∈ (Finset.univ : Finset (Fin J)), s j, f x ∂μ := by
    symm
    simpa using (lintegral_biUnion_finset hs_disjoint (fun j _ ↦ hs_meas j) f)
  rw [hsum]
  apply lintegral_mono_set
  intro x hx
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨j, hj, hx⟩
  have hfirst : (0 : Fin (J + 1)) ≤ j.castSucc := Fin.zero_le _
  have hleft : α < x := (hα.trans (ht hfirst)).trans_lt hx.1
  have hjle : j.succ ≤ Fin.last J := Fin.le_last _
  have hright : x ≤ β := hx.2.trans ((ht hjle).trans hβ)
  exact ⟨hleft.le, hright⟩

/-- On the interior of the ambient interval, ordinary and interval derivatives
agree almost everywhere for the logarithmic measure. -/
private theorem aux_deriv_eq_derivWithin_ae {α β : ℝ} (a : ℝ → ℝ) :
    deriv a =ᵐ[aux_logarithmicMeasure α β] derivWithin a (Set.Icc α β) := by
  apply (withDensity_absolutelyContinuous (volume.restrict (Set.Icc α β))
    (fun t ↦ ENNReal.ofReal t⁻¹)).ae_eq
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  exact (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm

/-- On a positive subinterval, multiplying the derivative by the logarithmic
density cancels the displayed factor of `t`. -/
private theorem aux_log_local_integral_eq {α β x y : ℝ} (hα : 0 < α)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (a : ℝ → ℝ) :
    (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ∂aux_logarithmicMeasure α β) =
      ∫⁻ t in Set.Icc x y, ‖deriv a t‖ₑ := by
  rw [aux_logarithmicMeasure]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable]
  · rw [Measure.restrict_restrict_of_subset]
    · apply lintegral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      have htpos : 0 < t := lt_of_lt_of_le hα (hx.1.trans ht.1)
      simp only [Pi.mul_apply]
      rw [← ofReal_norm, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      rw [Real.norm_of_nonneg htpos.le, ENNReal.ofReal_inv_of_pos htpos]
      rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr htpos)
        ENNReal.ofReal_ne_top]
      simpa only [one_mul, Real.norm_eq_abs] using (ofReal_norm (deriv a t))
    · exact fun t ht => ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  · exact ENNReal.measurable_ofReal.comp measurable_inv
  · exact measurableSet_Icc
  · filter_upwards with t
    exact ENNReal.ofReal_ne_top.lt_top

/-- The logarithmic mass of a subinterval is bounded by the elementary
`(β - α) / α` estimate. -/
private theorem aux_log_measure_le {α β x y : ℝ} (hα : 0 < α)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) :
    aux_logarithmicMeasure α β (Set.Icc x y) ≤ ENNReal.ofReal ((β - α) / α) := by
  rw [aux_logarithmicMeasure, withDensity_apply _ measurableSet_Icc]
  rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc hx.1 hy.2)]
  calc
    ∫⁻ a in Set.Icc x y, ENNReal.ofReal a⁻¹ ∂volume ≤
        ∫⁻ _a in Set.Icc x y, ENNReal.ofReal α⁻¹ ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      gcongr
      exact hx.1.trans ht.1
    _ = ENNReal.ofReal α⁻¹ * ENNReal.ofReal (y - x) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
    _ ≤ ENNReal.ofReal α⁻¹ * ENNReal.ofReal (β - α) := by
      gcongr
      all_goals linarith [hx.1, hy.2]
    _ = ENNReal.ofReal ((β - α) / α) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hα.le)]
      field_simp

/-- Measurability of the weighted derivative on an interval. -/
private theorem aux_derivmul_aemeasurable_local {α β x y : ℝ} (hαβ : α < β)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    AEMeasurable (fun t ↦ ‖t * deriv a t‖ₑ)
      ((aux_logarithmicMeasure α β).restrict (Set.Icc x y)) := by
  have hcont : ContinuousOn (id * derivWithin a (Set.Icc α β)) (Set.Icc α β) :=
    continuousOn_id.mul (ha.continuousOn_derivWithin (uniqueDiffOn_Icc hαβ) (by norm_num))
  have hcontLocal : ContinuousOn (id * derivWithin a (Set.Icc α β)) (Set.Icc x y) :=
    hcont.mono (Icc_subset_Icc hx.1 hy.2)
  have hwithin_meas0 : AEMeasurable (id * derivWithin a (Set.Icc α β))
      ((aux_logarithmicMeasure α β).restrict (Set.Icc x y)) :=
    hcontLocal.aemeasurable measurableSet_Icc
  have hwithin_meas : AEMeasurable (fun t ↦ ‖t * derivWithin a (Set.Icc α β) t‖ₑ)
      ((aux_logarithmicMeasure α β).restrict (Set.Icc x y)) := by
    simpa only [Pi.mul_apply, id_eq] using hwithin_meas0.enorm
  apply hwithin_meas.congr
  filter_upwards [(aux_deriv_eq_derivWithin_ae (α := α) (β := β) a).restrict] with t ht
  simp only [ht]

/-- The `L¹`--`L²` Cauchy--Schwarz estimate on an arbitrary measure. -/
private theorem aux_cauchy_lintegral_two {mu : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f mu) :
    ∫⁻ t, f t ∂mu ≤ (∫⁻ t, f t ^ (2 : ℝ) ∂mu) ^ ((2 : ℝ)⁻¹) *
      (mu Set.univ) ^ ((2 : ℝ)⁻¹) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  simpa [one_div] using
    (ENNReal.lintegral_mul_le_Lp_mul_Lq mu hpq hf (g := fun _ : ℝ ↦ 1)
      measurable_const.aemeasurable)

/-- Squaring a product of two square roots in `ℝ≥0∞`. -/
private theorem aux_half_mul_half_sq (C E : ℝ≥0∞) :
    (C ^ ((2 : ℝ)⁻¹) * E ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = C * E := by
  rw [ENNReal.rpow_two, mul_pow]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  norm_num

/-- The squared fundamental-theorem/Cauchy--Schwarz estimate for one pair of
points in the finite variation chain. -/
private theorem aux_pair_sq_le {α β x y : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal ((β - α) / α) *
      ∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
        ∂aux_logarithmicMeasure α β := by
  have hftc : ‖a y - a x‖ₑ ≤
      ∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ∂aux_logarithmicMeasure α β := by
    rw [aux_log_local_integral_eq hα hx hy]
    exact enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
      (ha.mono (Icc_subset_Icc hx.1 hy.2)) hxy
  have hcs := aux_cauchy_lintegral_two
    (aux_derivmul_aemeasurable_local hαβ hx hy a ha)
  have hmeasure := aux_log_measure_le hα hx hy
  have hlin : ‖a y - a x‖ₑ ≤
      ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) *
        (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) := by
    calc
      ‖a y - a x‖ₑ ≤ ∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ
          ∂aux_logarithmicMeasure α β := hftc
      _ ≤ (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) *
          (aux_logarithmicMeasure α β (Set.Icc x y)) ^ ((2 : ℝ)⁻¹) := by
        simpa only [Measure.restrict_apply_univ] using hcs
      _ ≤ (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) *
          ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) := by
        gcongr
      _ = ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) *
          (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
            ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹) := mul_comm _ _
  calc
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤
        (ENNReal.ofReal ((β - α) / α) ^ ((2 : ℝ)⁻¹) *
          (∫⁻ t in Set.Icc x y, ‖t * deriv a t‖ₑ ^ (2 : ℝ)
            ∂aux_logarithmicMeasure α β) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow hlin (by norm_num)
    _ = _ := aux_half_mul_half_sq _ _

/-- Summing the first FTC estimate over a monotone finite chain. -/
private theorem aux_chain_sq_energy_le {J : ℕ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((β - α) / α) *
        ∫⁻ x in Set.Icc α β, ‖x * deriv a x‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β := by
  letI : NullSingletonClass (aux_logarithmicMeasure α β) := by
    unfold aux_logarithmicMeasure
    infer_instance
  have ht' : Monotone (fun j ↦ (t j : ℝ)) := fun i j hij ↦ ht hij
  calc
    (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ≤
        ∑ j : Fin J, ENNReal.ofReal ((β - α) / α) *
          ∫⁻ x in Set.Icc (t j.castSucc : ℝ) (t j.succ : ℝ),
            ‖x * deriv a x‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
      apply Finset.sum_le_sum
      intro j _
      exact aux_pair_sq_le hα hαβ (t j.castSucc).2 (t j.succ).2
        (ht (Fin.castSucc_le_succ j)) a ha
    _ = ENNReal.ofReal ((β - α) / α) *
        ∑ j : Fin J, ∫⁻ x in Set.Icc (t j.castSucc : ℝ) (t j.succ : ℝ),
          ‖x * deriv a x‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal ((β - α) / α) *
        ∑ j : Fin J, ∫⁻ x in Set.Ioc (t j.castSucc : ℝ) (t j.succ : ℝ),
          ‖x * deriv a x‖ₑ ^ (2 : ℝ) ∂aux_logarithmicMeasure α β := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← restrict_Ioc_eq_restrict_Icc]
    _ ≤ ENNReal.ofReal ((β - α) / α) *
        ∫⁻ x in Set.Icc α β, ‖x * deriv a x‖ₑ ^ (2 : ℝ)
          ∂aux_logarithmicMeasure α β := by
      gcongr
      exact aux_sum_lintegral_Ioc_le (fun j ↦ (t j : ℝ)) ht'
        (fun x ↦ ‖x * deriv a x‖ₑ ^ (2 : ℝ)) (t 0).2.1 (t (Fin.last J)).2.2

/-- The first finite-variation FTC estimate for one fixed monotone chain. -/
private theorem aux_chain_first_ftc {J : ℕ} {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
      (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
  let E : ℝ≥0∞ := ∫⁻ x in Set.Icc α β, ‖x * deriv a x‖ₑ ^ (2 : ℝ)
    ∂aux_logarithmicMeasure α β
  have hsquare := aux_chain_sq_energy_le hα hαβ a ha t ht
  have hroot :
      (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) ≤
        (ENNReal.ofReal ((β - α) / α) * E) ^ ((2 : ℝ)⁻¹) := by
    apply ENNReal.rpow_le_rpow
    · simpa only [E] using hsquare
    · positivity
  have hELp : aux_logarithmicL2 α β (fun t ↦ t * deriv a t) = E ^ ((2 : ℝ)⁻¹) := by
    unfold aux_logarithmicL2 E
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    norm_num
    have hsupport : (aux_logarithmicMeasure α β).restrict (Set.Icc α β) =
        aux_logarithmicMeasure α β := by
      unfold aux_logarithmicMeasure
      rw [restrict_withDensity measurableSet_Icc,
        Measure.restrict_restrict_of_subset Subset.rfl]
    rw [hsupport]
  calc
    (∑ j : Fin J,
      (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) =
        (∑ j : Fin J, ‖a (t j.succ) - a (t j.castSucc)‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
      simp only [← enorm_eq_nnnorm]
    _ ≤ (ENNReal.ofReal ((β - α) / α) * E) ^ ((2 : ℝ)⁻¹) := hroot
    _ = (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) * E ^ ((2 : ℝ)⁻¹) :=
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by rw [hELp]

/-- The endpoint estimate for the square of a continuously differentiable
function.  This is the common analytic input to the sign-sensitive variation
bound below. -/
private theorem aux_square_endpoint_le_lintegral {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y * a y - a x * a x‖ₑ ≤
      ∫⁻ z in Set.Icc x y, (2 : ℝ≥0∞) * ‖a z‖ₑ * ‖deriv a z‖ₑ := by
  have hsubset : Set.Icc x y ⊆ Set.Icc α β := by
    intro z hz
    exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
  have hsq := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
    ((ha.mul ha).mono hsubset) hxy
  refine hsq.trans ?_
  apply lintegral_mono_ae
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with z hz
  have hzαβ : z ∈ Set.Ioo α β :=
    ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  have hdiff : DifferentiableAt ℝ a z :=
    ((ha z ⟨hzαβ.1.le, hzαβ.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
      (Icc_mem_nhds hzαβ.1 hzαβ.2)
  change ‖deriv (a * a) z‖ₑ ≤ _
  rw [deriv_mul hdiff hdiff]
  rw [show deriv a z * a z + a z * deriv a z = 2 * a z * deriv a z by ring]
  have htwo : ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) := by norm_num [enorm_eq_nnnorm]
  simp [enorm_mul, htwo]

/-- The elementary same-sign algebraic estimate used after applying the FTC
to `a^2`. -/
private theorem aux_same_sign_square_le (u v : ℝ) (huv : 0 ≤ u * v) :
    ‖u - v‖ₑ ^ (2 : ℕ) ≤ ‖u * u - v * v‖ₑ := by
  rw [show u * u - v * v = (u - v) * (u + v) by ring]
  rw [enorm_mul]
  have hsq : |u - v| ≤ |u + v| := by
    rw [← sq_le_sq]
    nlinarith
  rw [show ‖u - v‖ₑ ^ (2 : ℕ) = ‖u - v‖ₑ * ‖u - v‖ₑ by ring]
  gcongr
  apply ENNReal.coe_le_coe.mpr
  exact_mod_cast hsq

/-- A coarse algebraic estimate used when an interval crosses a zero of the
function. -/
private theorem aux_cross_square_le (u v : ℝ) :
    ‖u - v‖ₑ ^ (2 : ℕ) ≤
      2 * (‖u * u‖ₑ + ‖v * v‖ₑ) := by
  apply ENNReal.coe_le_coe.mpr
  exact (show ‖u - v‖₊ ^ (2 : ℕ) ≤
      2 * (‖u * u‖₊ + ‖v * v‖₊) by
    have hreal : |u - v| ^ 2 ≤ 2 * (|u * u| + |v * v|) := by
      rw [sq_abs, abs_of_nonneg (mul_self_nonneg u),
        abs_of_nonneg (mul_self_nonneg v)]
      nlinarith [sq_nonneg (u + v)]
    exact_mod_cast hreal)

/-- Endpoint changes have zero Lebesgue mass, so `Icc` and `Ioc` give the
same nonnegative integral. -/
private theorem aux_lintegral_Icc_eq_Ioc (f : ℝ → ℝ≥0∞) (x y : ℝ) :
    (∫⁻ z in Set.Icc x y, f z) = ∫⁻ z in Set.Ioc x y, f z := by
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]

/-- Pairwise squared variation is controlled by the unweighted product
integral.  The crossing case is split at an intermediate zero. -/
private theorem aux_pairwise_square_le_lintegral {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y - a x‖ₑ ^ (2 : ℕ) ≤
      8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
  let F : ℝ → ℝ≥0∞ := fun z ↦ (2 : ℝ≥0∞) * ‖a z‖ₑ * ‖deriv a z‖ₑ
  by_cases hsign : 0 ≤ a x * a y
  · calc
      ‖a y - a x‖ₑ ^ (2 : ℕ) ≤ ‖a y * a y - a x * a x‖ₑ :=
        aux_same_sign_square_le (a y) (a x) (by simpa [mul_comm] using hsign)
      _ ≤ ∫⁻ z in Set.Icc x y, F z := aux_square_endpoint_le_lintegral a ha hx hy hxy
      _ = ∫⁻ z in Set.Ioc x y, F z := aux_lintegral_Icc_eq_Ioc F x y
      _ ≤ 8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
        simp only [F]
        calc
          (∫⁻ z in Set.Ioc x y, 2 * ‖a z‖ₑ * ‖deriv a z‖ₑ) ≤
              ∫⁻ z in Set.Ioc x y, 8 * (‖a z‖ₑ * ‖deriv a z‖ₑ) := by
                apply lintegral_mono
                intro z
                calc
                  2 * ‖a z‖ₑ * ‖deriv a z‖ₑ =
                      2 * (‖a z‖ₑ * ‖deriv a z‖ₑ) := by ring
                  _ ≤ 8 * (‖a z‖ₑ * ‖deriv a z‖ₑ) := by gcongr <;> norm_num
          _ = 8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ :=
            lintegral_const_mul' 8 _ (by norm_num)
  · have hcross : a x * a y < 0 := lt_of_not_ge hsign
    have hzero : (0 : ℝ) ∈ Set.uIcc (a x) (a y) := by
      rw [mem_uIcc]
      rcases (mul_neg_iff.mp hcross) with ⟨hxp, hyn⟩ | ⟨hxn, hyp⟩
      · exact Or.inr ⟨hyn.le, hxp.le⟩
      · exact Or.inl ⟨hxn.le, hyp.le⟩
    have hcont : ContinuousOn a (Set.uIcc x y) := by
      simpa [uIcc_of_le hxy] using ha.continuousOn.mono (Icc_subset_Icc hx.1 hy.2)
    rcases intermediate_value_uIcc hcont hzero with ⟨z, hz, hz0⟩
    have hzIcc : z ∈ Set.Icc x y := by simpa [uIcc_of_le hxy] using hz
    have hzαβ : z ∈ Set.Icc α β :=
      ⟨hx.1.trans hzIcc.1, hzIcc.2.trans hy.2⟩
    have hxz := aux_square_endpoint_le_lintegral a ha hx hzαβ hzIcc.1
    have hzy := aux_square_endpoint_le_lintegral a ha hzαβ hy hzIcc.2
    have hxz' : ‖a x * a x - a z * a z‖ₑ ≤ ∫⁻ q in Set.Icc x z, F q := by
      simpa [F, enorm_sub_rev] using hxz
    have hcross' : ‖a y - a x‖ₑ ^ (2 : ℕ) ≤
        2 * (‖a x * a x - a z * a z‖ₑ + ‖a y * a y - a z * a z‖ₑ) := by
      rw [hz0]
      simpa [add_comm] using aux_cross_square_le (a y) (a x)
    calc
      ‖a y - a x‖ₑ ^ (2 : ℕ) ≤
          2 * (‖a x * a x - a z * a z‖ₑ + ‖a y * a y - a z * a z‖ₑ) := hcross'
      _ ≤ 2 * ((∫⁻ q in Set.Icc x z, F q) + ∫⁻ q in Set.Icc z y, F q) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hxz' hzy) (by norm_num)
      _ = 2 * ((∫⁻ q in Set.Ioc x z, F q) + ∫⁻ q in Set.Ioc z y, F q) := by
        rw [aux_lintegral_Icc_eq_Ioc F x z, aux_lintegral_Icc_eq_Ioc F z y]
      _ = 2 * ∫⁻ q in Set.Ioc x y, F q := by
        rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
          Set.Ioc_union_Ioc_eq_Ioc hzIcc.1 hzIcc.2]
      _ ≤ 8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
        simp only [F]
        calc
          2 * (∫⁻ q in Set.Ioc x y, 2 * ‖a q‖ₑ * ‖deriv a q‖ₑ) =
              4 * ∫⁻ q in Set.Ioc x y, ‖a q‖ₑ * ‖deriv a q‖ₑ := by
            rw [show (fun q ↦ 2 * ‖a q‖ₑ * ‖deriv a q‖ₑ) =
              fun q ↦ 2 * (‖a q‖ₑ * ‖deriv a q‖ₑ) by
                funext q
                ring]
            rw [lintegral_const_mul' 2 _ (by norm_num)]
            ring
          _ ≤ 8 * ∫⁻ q in Set.Ioc x y, ‖a q‖ₑ * ‖deriv a q‖ₑ := by
            gcongr <;> norm_num

/-- Cancellation of the logarithmic density on an `Ioc` interval. -/
private theorem aux_enorm_mul_inv_cancel {z d : ℝ} (hz : 0 < z) :
    ENNReal.ofReal z⁻¹ * ‖z * d‖ₑ = ‖d‖ₑ := by
  rw [enorm_mul, Real.enorm_eq_ofReal hz.le, ENNReal.ofReal_inv_of_pos hz]
  rw [← mul_assoc, ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr hz)) ENNReal.ofReal_ne_top, one_mul]

/-- Restricting the logarithmic measure to a contained open-closed interval. -/
private theorem aux_restrict_logarithmicMeasure_Ioc {α β x y : ℝ}
    (hsub : Set.Ioc x y ⊆ Set.Icc α β) :
    (aux_logarithmicMeasure α β).restrict (Set.Ioc x y) =
      (volume.restrict (Set.Ioc x y)).withDensity fun t ↦ ENNReal.ofReal t⁻¹ := by
  rw [aux_logarithmicMeasure, restrict_withDensity measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr hsub]

/-- Convert the ordinary product integral on an `Ioc` interval to its
logarithmically weighted form. -/
private theorem aux_log_weight_conversion_Ioc {α β x y : ℝ} (hx : 0 < x)
    (hsub : Set.Ioc x y ⊆ Set.Icc α β) (a d : ℝ → ℝ) :
    ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖d z‖ₑ =
      ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖z * d z‖ₑ
        ∂aux_logarithmicMeasure α β := by
  rw [show (aux_logarithmicMeasure α β).restrict (Set.Ioc x y) =
      (volume.restrict (Set.Ioc x y)).withDensity fun t ↦ ENNReal.ofReal t⁻¹ by
        exact aux_restrict_logarithmicMeasure_Ioc hsub]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
  · apply lintegral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
    have hzpos : 0 < z := hx.trans hz.1
    change ‖a z‖ₑ * ‖d z‖ₑ =
      ENNReal.ofReal z⁻¹ * (‖a z‖ₑ * ‖z * d z‖ₑ)
    rw [show ENNReal.ofReal z⁻¹ * (‖a z‖ₑ * ‖z * d z‖ₑ) =
        ‖a z‖ₑ * (ENNReal.ofReal z⁻¹ * ‖z * d z‖ₑ) by ring]
    rw [aux_enorm_mul_inv_cancel hzpos]
  · exact (measurable_inv.comp measurable_id).ennreal_ofReal.aemeasurable
  · exact ae_of_all _ fun _ ↦ lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top

/-- Global logarithmic `L²` Hölder estimate. -/
private theorem aux_log_holder_lintegral {α β : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    ∫⁻ z, ‖a z‖ₑ * ‖z * deriv a z‖ₑ ∂aux_logarithmicMeasure α β ≤
      aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by
  have hameas : AEStronglyMeasurable a (aux_logarithmicMeasure α β) :=
    AEStronglyMeasurable.mono_ac
      (withDensity_absolutelyContinuous (volume.restrict (Set.Icc α β))
        (fun t ↦ ENNReal.ofReal t⁻¹))
      (ha.continuousOn.aestronglyMeasurable measurableSet_Icc)
  have hdmeas : AEStronglyMeasurable (fun z ↦ z * deriv a z)
      (aux_logarithmicMeasure α β) :=
    (measurable_id.mul (measurable_deriv a)).aestronglyMeasurable
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1)
    hameas hdmeas (· * ·) 1
    (Filter.Eventually.of_forall fun _ ↦ by simp)
  rw [eLpNorm_one_eq_lintegral_enorm] at h
  simpa [aux_logarithmicL2, enorm_mul] using h

/-- Restate the pairwise bound with real `rpow` exponent notation. -/
private theorem aux_pairwise_square_rpow_le_lintegral {α β x y : ℝ} (a : ℝ → ℝ)
    (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (hx : x ∈ Set.Icc α β) (hy : y ∈ Set.Icc α β) (hxy : x ≤ y) :
    ‖a y - a x‖ₑ ^ (2 : ℝ) ≤
      8 * ∫⁻ z in Set.Ioc x y, ‖a z‖ₑ * ‖deriv a z‖ₑ := by
  convert aux_pairwise_square_le_lintegral a ha hx hy hxy using 1 <;>
    norm_num [ENNReal.rpow_natCast]

/-- The second FTC estimate summed over one monotone chain. -/
private theorem aux_chain_second_energy_le {J : ℕ} {α β : ℝ} (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β))
    (t : Fin (J + 1) → Set.Icc α β) (ht : Monotone t) :
    (∑ j : Fin J,
      ((‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by
  let u : Fin (J + 1) → ℝ := fun j ↦ t j
  have hu : Monotone u := by
    intro i j hij
    exact ht hij
  let g : ℝ → ℝ≥0∞ := fun z ↦ ‖a z‖ₑ * ‖z * deriv a z‖ₑ
  have hsub (j : Fin J) : Set.Ioc (u j.castSucc) (u j.succ) ⊆ Set.Icc α β := by
    intro z hz
    exact ⟨(t j.castSucc).property.1.trans hz.1.le,
      hz.2.trans (t j.succ).property.2⟩
  have hpair (j : Fin J) :
      ((‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ)) ≤
        8 * ∫⁻ z in Set.Ioc (u j.castSucc) (u j.succ), g z
          ∂aux_logarithmicMeasure α β := by
    have h := aux_pairwise_square_rpow_le_lintegral a ha
      (t j.castSucc).property (t j.succ).property (ht (Fin.castSucc_le_succ j))
    rw [aux_log_weight_conversion_Ioc
      (lt_of_lt_of_le hα (t j.castSucc).property.1) (hsub j) a (deriv a)] at h
    simpa only [u, g, ← enorm_eq_nnnorm] using h
  calc
    (∑ j : Fin J,
        ((‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ≤
        ∑ j : Fin J, 8 * ∫⁻ z in Set.Ioc (u j.castSucc) (u j.succ), g z
          ∂aux_logarithmicMeasure α β := Finset.sum_le_sum (fun j _ ↦ hpair j)
    _ = 8 * (∑ j : Fin J, ∫⁻ z in Set.Ioc (u j.castSucc) (u j.succ), g z
          ∂aux_logarithmicMeasure α β) := by rw [Finset.mul_sum]
    _ ≤ 8 * ∫⁻ z in Set.Icc α β, g z ∂aux_logarithmicMeasure α β := by
      gcongr
      exact aux_sum_lintegral_Ioc_le u hu g (t 0).property.1
        (t (Fin.last J)).property.2
    _ ≤ 8 * (aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z)) := by
      gcongr
      calc
        (∫⁻ z in Set.Icc α β, g z ∂aux_logarithmicMeasure α β) ≤
            ∫⁻ z, g z ∂aux_logarithmicMeasure α β := by
          exact lintegral_mono' Measure.restrict_le_self le_rfl
        _ ≤ _ := by
          simpa only [g] using aux_log_holder_lintegral a ha
    _ = 8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun z ↦ z * deriv a z) := by ring

/-- The `rpow`/supremum closure of the second FTC estimate. -/
private theorem aux_second_ftcCsR {J : ℕ} {α β : ℝ} (hα : 0 < α)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
  let R : ℝ≥0∞ := 8 * aux_logarithmicL2 α β a *
    aux_logarithmicL2 α β (fun t ↦ t * deriv a t)
  have hchain (t : {u : Fin (J + 1) → Set.Icc α β // Monotone u}) :
      (∑ j : Fin J,
        ((‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ≤ R := by
    simpa only [R] using aux_chain_second_energy_le hα a ha t.1 t.2
  have hroot (t : {u : Fin (J + 1) → Set.Icc α β // Monotone u}) :
      (∑ j : Fin J,
        ((‖a (t.1 j.succ) - a (t.1 j.castSucc)‖₊ : ℝ≥0∞) ^ (2 : ℝ))) ^
          ((2 : ℝ)⁻¹) ≤ R ^ ((2 : ℝ)⁻¹) :=
    ENNReal.rpow_le_rpow (hchain t) (by norm_num)
  have hsup : finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J ≤
      R ^ ((2 : ℝ)⁻¹) := by
    rw [finiteVariationSeminorm]
    apply iSup_le
    intro t
    exact hroot t
  calc
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
        (R ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) :=
      ENNReal.rpow_le_rpow hsup (by norm_num)
    _ = R := by
      rw [← ENNReal.rpow_mul]
      norm_num
    _ = 8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by rfl

/-- Lemma \ref{lem:ftccs-R}. If `0 < α < β` and `a` is continuously
differentiable on `[α, β]`, its finite `2`-variation is bounded by the two
fundamental-theorem-of-calculus/Cauchy--Schwarz estimates from the manuscript. -/
theorem ftcCsR (J : ℕ) {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (a : ℝ → ℝ) (ha : ContDiffOn ℝ 1 a (Set.Icc α β)) :
    finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J ≤
      (ENNReal.ofReal ((β - α) / α)) ^ ((2 : ℝ)⁻¹) *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) ∧
    (finiteVariationSeminorm (fun t : Set.Icc α β ↦ a t) 2 J) ^ (2 : ℝ) ≤
      8 * aux_logarithmicL2 α β a *
        aux_logarithmicL2 α β (fun t ↦ t * deriv a t) := by
  constructor
  · unfold finiteVariationSeminorm
    apply iSup_le
    intro t
    exact aux_chain_first_ftc hα hαβ a ha t.1 t.2
  · exact aux_second_ftcCsR hα a ha

end Codex.Reduction.VariationSeminorms
