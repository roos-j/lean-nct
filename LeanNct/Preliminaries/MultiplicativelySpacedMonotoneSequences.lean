import Mathlib

/-!
# Multiplicatively spaced monotone sequences

This file formalizes the subsection “Multiplicatively spaced monotone sequences” of the
manuscript.
-/

namespace Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences

open Set

/--
\begin{definition}[Multiplicatively spaced monotone sequences]\label{multiplicatively spaced monotone sequences}
A sequence $a:\Z\to\R$ with $a(j)>0$ for every $j\in\Z$ is called multiplicatively spaced if, for each $j\in\Z$
\begin{equation}\label{auto:spaced-sequence-growth}
    2a(j)\le a(j+1)\, .
\end{equation}
Let $\mathrm{A}$ be the set of such sequences.
\end{definition}
-/
def SpacedSequence (a : ℤ → ℝ) : Prop :=
  ∀ j : ℤ, 0 < a j ∧ 2 * a j ≤ a (j + 1)

/--
\begin{definition}[Multiplicatively spaced monotone sequences]
Let ${\rm A}$ be the set of such sequences.
\end{definition}
-/
def A : Set (ℤ → ℝ) := {a | SpacedSequence a}

/-- This auxiliary theorem extracts positivity from the defining conditions of a spaced sequence. -/
theorem aux_spacedSequence_pos {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) : 0 < a j :=
  (ha j).1

/-- This auxiliary theorem records the one-step monotonicity implied by multiplicative spacing. -/
theorem aux_spacedSequence_le_succ {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) :
    a j ≤ a (j + 1) := by
  have hpos := (ha j).1
  have hspace := (ha j).2
  nlinarith

/-- This auxiliary theorem gives the monotonicity used in the distance estimates below. -/
theorem aux_spacedSequence_monotone {a : ℤ → ℝ} (ha : SpacedSequence a) : Monotone a :=
  monotone_int_of_le_succ (aux_spacedSequence_le_succ ha)

/-- This auxiliary theorem iterates the defining spacing inequality forward. -/
theorem aux_pow_two_mul_le_shift {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) (k : ℕ) :
    (2 : ℝ) ^ k * a j ≤ a (j + k) := by
  induction k with
  | zero => simpa
  | succ k ih =>
      have hstep := (ha (j + k)).2
      have hmul : 2 * ((2 : ℝ) ^ k * a j) ≤ 2 * a (j + k) := by
        gcongr
      calc
        (2 : ℝ) ^ (Nat.succ k) * a j = 2 * ((2 : ℝ) ^ k * a j) := by
          rw [pow_succ]
          ring
        _ ≤ 2 * a (j + k) := hmul
        _ ≤ a (j + Nat.succ k) := by
          convert hstep using 1 <;> push_cast <;> ring

/-- This auxiliary theorem is the backwards form of the iterated spacing inequality. -/
theorem aux_pow_two_mul_shift_le {a : ℤ → ℝ} (ha : SpacedSequence a) (j : ℤ) (k : ℕ) :
    (2 : ℝ) ^ k * a (j - k) ≤ a j := by
  convert aux_pow_two_mul_le_shift ha (j - k) k using 1 <;> ring

/-- Auxiliary explicit extension used in Proposition \ref{Extension of sequences}, formalized by
`extensionOfSequences`. -/
noncomputable def aux_extensionOfSequence (J : ℕ) (a : ℤ → ℝ) : ℤ → ℝ := fun j =>
  if j < 0 then (2 : ℝ) ^ j * a 0
  else if j < (J : ℤ) then a j
  else (2 : ℝ) ^ (j - J + 1) * a (J - 1)

/--
\begin{proposition}[Extension of sequences]\label{Extension of sequences}
Let $J\in\N$ with $J\ge1$ and let $a:[J)\to\R$ satisfy $a(j)>0$ for every $j\in[J)$ and, for all $j\in[J-1)$, we have $a(j+1)\ge 2a(j)$.
Then there is a unique $b\in A$ such that for all $j\in [J)$ we have $a(j)=b(j)$ and for $j\ge J$ we have $b(j)=2^{j-J+1} a(J-1)$ and for $j<0$ we have $b(j)=2^j a(0)$\, .
\end{proposition}
-/
theorem extensionOfSequences (J : ℕ) (hJ : 0 < J) (a : ℤ → ℝ)
    (ha_pos : ∀ j : ℤ, 0 ≤ j → j < (J : ℤ) → 0 < a j)
    (ha_space : ∀ j : ℤ, 0 ≤ j → j + 1 < (J : ℤ) → 2 * a j ≤ a (j + 1)) :
    ∃! b : ℤ → ℝ, SpacedSequence b ∧
      (∀ j : ℤ, 0 ≤ j → j < (J : ℤ) → b j = a j) ∧
      (∀ j : ℤ, (J : ℤ) ≤ j → b j = (2 : ℝ) ^ (j - J + 1) * a (J - 1)) ∧
      (∀ j : ℤ, j < 0 → b j = (2 : ℝ) ^ j * a 0) := by
  let b := aux_extensionOfSequence J a
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hfirst : 0 < a 0 := ha_pos 0 (by omega) (by omega)
  have hlast : 0 < a (J - 1) := by
    apply ha_pos (J - 1)
    · omega
    · omega
  have hb_pos : ∀ j : ℤ, 0 < b j := by
    intro j
    by_cases hneg : j < 0
    · rw [show b j = (2 : ℝ) ^ j * a 0 by simp [b, aux_extensionOfSequence, hneg]]
      exact mul_pos (zpow_pos (by norm_num) _) hfirst
    · by_cases hmid : j < (J : ℤ)
      · rw [show b j = a j by simp [b, aux_extensionOfSequence, hneg, hmid]]
        exact ha_pos j (le_of_not_gt hneg) hmid
      · rw [show b j = (2 : ℝ) ^ (j - J + 1) * a (J - 1) by
          simp [b, aux_extensionOfSequence, hneg, hmid]]
        exact mul_pos (zpow_pos (by norm_num) _) hlast
  have hb_space : ∀ j : ℤ, 2 * b j ≤ b (j + 1) := by
    intro j
    by_cases hneg : j < 0
    · by_cases hmone : j = -1
      · subst j
        have hbneg : b (-1) = (2 : ℝ) ^ (-1 : ℤ) * a 0 := by
          simp [b, aux_extensionOfSequence]
        have hbzero : b 0 = a 0 := by
          have hJz : (0 : ℤ) < J := by exact_mod_cast hJ
          simp [b, aux_extensionOfSequence, hJ, hJz]
        rw [hbneg]
        norm_num
        rw [hbzero]
        norm_num [zpow_neg]
        apply le_of_eq
        ring
      · have hneg' : j + 1 < 0 := by omega
        rw [show b j = (2 : ℝ) ^ j * a 0 by simp [b, aux_extensionOfSequence, hneg]]
        rw [show b (j + 1) = (2 : ℝ) ^ (j + 1) * a 0 by
          simp [b, aux_extensionOfSequence, hneg']]
        rw [zpow_add₀ htwo j 1]
        norm_num
        apply le_of_eq
        ring
    · have hj0 : 0 ≤ j := le_of_not_gt hneg
      by_cases hbefore : j + 1 < (J : ℤ)
      · have hj : j < (J : ℤ) := by omega
        have hnextneg : ¬ (j + 1 < 0) := by omega
        simp [b, aux_extensionOfSequence, hneg, hj, hnextneg, hbefore]
        exact ha_space j hj0 hbefore
      · have hjge : (J : ℤ) ≤ j + 1 := le_of_not_gt hbefore
        by_cases hjlast : j = (J : ℤ) - 1
        · subst j
          have hJneg : ¬ ((J : ℤ) - 1 < 0) := by omega
          have hJlt : (J : ℤ) - 1 < (J : ℤ) := by omega
          have hJnextneg : ¬ ((J : ℤ) - 1 + 1 < 0) := by omega
          have hJnext : ¬ ((J : ℤ) - 1 + 1 < (J : ℤ)) := by omega
          rw [show b ((J : ℤ) - 1) = a ((J : ℤ) - 1) by
            simp [b, aux_extensionOfSequence, hJneg, hJlt]]
          rw [show b (((J : ℤ) - 1) + 1) = 2 * a ((J : ℤ) - 1) by
            simp [b, aux_extensionOfSequence, hJneg, hJlt, hJnextneg, hJnext]]
        · have hjgeJ : (J : ℤ) ≤ j := by omega
          have hnextneg : ¬ (j + 1 < 0) := by omega
          have hjnotlt : ¬ (j < (J : ℤ)) := by omega
          have hnextnotlt : ¬ (j + 1 < (J : ℤ)) := by omega
          rw [show b j = (2 : ℝ) ^ (j - J + 1) * a (J - 1) by
            simp [b, aux_extensionOfSequence, hneg, hjnotlt]]
          rw [show b (j + 1) = (2 : ℝ) ^ (j + 1 - J + 1) * a (J - 1) by
            simp [b, aux_extensionOfSequence, hnextneg, hnextnotlt]]
          rw [show j + 1 - J + 1 = (j - J + 1) + 1 by ring,
            zpow_add₀ htwo (j - J + 1) 1]
          norm_num
          apply le_of_eq
          ring
  refine ⟨b, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      exact ⟨hb_pos j, hb_space j⟩
    · intro j hj0 hjJ
      simp [b, aux_extensionOfSequence, not_lt.mpr hj0, hjJ]
    · intro j hj
      simp [b, aux_extensionOfSequence, not_lt.mpr (by omega : 0 ≤ j), not_lt.mpr hj]
    · intro j hj
      simp [b, aux_extensionOfSequence, hj]
  · intro c hc
    funext j
    by_cases hjneg : j < 0
    · rw [hc.2.2.2 j hjneg]
      simp [b, aux_extensionOfSequence, hjneg]
    · by_cases hjmid : j < (J : ℤ)
      · rw [hc.2.1 j (le_of_not_gt hjneg) hjmid]
        simp [b, aux_extensionOfSequence, hjneg, hjmid]
      · rw [hc.2.2.1 j (le_of_not_gt hjmid)]
        simp [b, aux_extensionOfSequence, hjneg, hjmid]

/--
\begin{proposition}[Operations on spaced sequences]\label{Operations on spaced sequences}
Let $a,b\in {\rm A}$. Then the following hold:

(i) $\max(a,b)\in {\rm A}$
\end{proposition}
-/
theorem max_mem_A {a b : ℤ → ℝ} (ha : SpacedSequence a) (hb : SpacedSequence b) :
    SpacedSequence (fun j => max (a j) (b j)) := by
  intro j
  constructor
  · exact lt_of_lt_of_le (aux_spacedSequence_pos ha j) (le_max_left _ _)
  · change 2 * max (a j) (b j) ≤ max (a (j + 1)) (b (j + 1))
    by_cases hab : a j ≤ b j
    · rw [max_eq_right hab]
      exact (hb j).2.trans (le_max_right _ _)
    · rw [max_eq_left (le_of_not_ge hab)]
      exact (ha j).2.trans (le_max_left _ _)

/--
\begin{proposition}[Operations on spaced sequences]\label{Operations on spaced sequences}
Let $a,b\in {\rm A}$. Then the following hold:

(ii) $t\cdot a\in {\rm A}$ for every $t>0$.
\end{proposition}
-/
theorem smul_mem_A {a : ℤ → ℝ} (ha : SpacedSequence a) {t : ℝ} (ht : 0 < t) :
    SpacedSequence (fun j => t * a j) := by
  intro j
  constructor
  · exact mul_pos ht (ha j).1
  · calc
      2 * (t * a j) = t * (2 * a j) := by ring
      _ ≤ t * a (j + 1) := by gcongr; exact (ha j).2

/--
\begin{proposition}[Operations on spaced sequences]\label{Operations on spaced sequences}
Let $a,b\in {\rm A}$. Then the following hold:

(iii) Let $n\in\mathbb{Z}$. If $c:\Z\to(0,\infty)$ is defined by $c(j)=a(j+n)$ for all $j\in\mathbb{Z}$, then $c\in {\rm A}$.
\end{proposition}
-/
theorem shift_mem_A {a : ℤ → ℝ} (ha : SpacedSequence a) (n : ℤ) :
    SpacedSequence (fun j => a (j + n)) := by
  intro j
  constructor
  · exact (ha (j + n)).1
  · convert (ha (j + n)).2 using 1 <;> ring

/--
\begin{proposition}[Operations on spaced sequences]\label{Operations on spaced sequences}
Let $a,b\in {\rm A}$. Then the following hold:

(iv) If $c:\Z\to (0,\infty)$ is defined by $c(j)=\sqrt{a(j)^2+b(j)^2}$ for all $j\in\Z$, then $c\in {\rm A}$.
\end{proposition}
-/
theorem sqrt_sq_add_sq_mem_A {a b : ℤ → ℝ} (ha : SpacedSequence a) (hb : SpacedSequence b) :
    SpacedSequence (fun j => Real.sqrt (a j ^ 2 + b j ^ 2)) := by
  intro j
  have hsum : 0 ≤ a j ^ 2 + b j ^ 2 := by positivity
  have hsum' : 0 ≤ a (j + 1) ^ 2 + b (j + 1) ^ 2 := by positivity
  constructor
  · apply Real.sqrt_pos.2
    nlinarith [(ha j).1, (hb j).1]
  · have ha' := (ha j).2
    have hb' := (hb j).2
    have hsq : 4 * (a j ^ 2 + b j ^ 2) ≤ a (j + 1) ^ 2 + b (j + 1) ^ 2 := by
      have ha_nonneg := le_of_lt (ha j).1
      have hb_nonneg := le_of_lt (hb j).1
      nlinarith [sq_nonneg (a (j + 1) - 2 * a j),
        sq_nonneg (b (j + 1) - 2 * b j)]
    have hsqrt := Real.sq_sqrt hsum
    have hsqrt' := Real.sq_sqrt hsum'
    nlinarith [Real.sqrt_nonneg (a j ^ 2 + b j ^ 2),
      Real.sqrt_nonneg (a (j + 1) ^ 2 + b (j + 1) ^ 2)]

/-- The finite-shift comparison occurring in Definition
\ref{Distance of spaced sequences}; it is used by 'SequenceDistance'. -/
def WithinSequenceDistance (a b : ℤ → ℝ) (k : ℕ) : Prop :=
  ∀ j : ℤ, a (j - k) ≤ b j ∧ b j ≤ a (j + k)

/--
\begin{definition}[Distance of spaced sequences]\label{Distance of spaced sequences}
Given $a,b\in {\rm A}$, define
\begin{equation}\label{auto:spaced-sequence-distance}
    \dist(a,b)=\min\{k\in\mathbb{Z}_{\ge 0}\,:\,\forall j, a(j-k)\le b(j)\le a(j+k)\}
\end{equation}
with the understanding that the value is $\infty$ if there is no such $k$.
\end{definition}
-/
noncomputable def SequenceDistance (a b : ℤ → ℝ) : WithTop ℕ :=
  by
    classical
    exact if h : ∃ k : ℕ, WithinSequenceDistance a b k then (Nat.find h : WithTop ℕ) else ⊤

/-- This auxiliary theorem is useful for deriving all distance estimates from an explicit
comparison at a particular integer shift. -/
theorem aux_sequenceDistance_le_of_within {a b : ℤ → ℝ} {k : ℕ}
    (hk : WithinSequenceDistance a b k) : SequenceDistance a b ≤ (k : WithTop ℕ) := by
  classical
  by_cases h : ∃ l : ℕ, WithinSequenceDistance a b l
  · simp only [SequenceDistance, dif_pos h]
    exact_mod_cast Nat.find_min' h hk
  · exact (h ⟨k, hk⟩).elim

/-- This auxiliary theorem transports a distance comparison after exchanging its two sequences. -/
theorem aux_withinSequenceDistance_symm {a b : ℤ → ℝ} {k : ℕ} :
    WithinSequenceDistance a b k ↔ WithinSequenceDistance b a k := by
  constructor <;> intro h <;> intro j
  · constructor
    · have h' := (h (j - k)).2
      convert h' using 1 <;> ring
    · have h' := (h (j + k)).1
      convert h' using 1 <;> ring
  · constructor
    · have h' := (h (j - k)).2
      convert h' using 1 <;> ring
    · have h' := (h (j + k)).1
      convert h' using 1 <;> ring

/-- This auxiliary theorem composes the pointwise comparisons used to define sequence distance. -/
theorem aux_withinSequenceDistance_trans {a b c : ℤ → ℝ} {k l : ℕ}
    (hab : WithinSequenceDistance a b k) (hbc : WithinSequenceDistance b c l) :
    WithinSequenceDistance a c (k + l) := by
  intro j
  constructor
  · calc
      a (j - (k + l)) = a ((j - l) - k) := by ring
      _ ≤ b (j - l) := (hab (j - l)).1
      _ ≤ c j := (hbc j).1
  · calc
      c j ≤ b (j + l) := (hbc j).2
      _ ≤ a ((j + l) + k) := (hab (j + l)).2
      _ = a (j + (k + l)) := by ring

/-- Pointwise maxima remain within a common finite sequence-distance comparison.
This is used when finite bracket majorants produce the maximum of two nearby
scale sequences. -/
theorem aux_withinSequenceDistance_max {a b c : ℤ → ℝ} {k : ℕ}
    (hab : WithinSequenceDistance a b k) (hac : WithinSequenceDistance a c k) :
    WithinSequenceDistance a (fun j => max (b j) (c j)) k := by
  intro j
  constructor
  · exact (hab j).1.trans (le_max_left _ _)
  · exact max_le (hab j).2 (hac j).2

/--
\begin{proposition}[Properties of distance of sequences]\label{Properties of distance of sequences}
Let $a,b,c\in {\rm A}$.
Then

(i) If $\dist(a,b)=0$, then $a=b$.
\end{proposition}
-/
theorem sequenceDistance_zero_eq {a b : ℤ → ℝ} (h : SequenceDistance a b = 0) : a = b := by
  classical
  by_cases hab : ∃ k : ℕ, WithinSequenceDistance a b k
  · have hfind : (Nat.find hab : WithTop ℕ) = 0 := by
      simpa [SequenceDistance, hab] using h
    have hfind' : Nat.find hab = 0 := by exact_mod_cast hfind
    have hwithin : WithinSequenceDistance a b 0 := by
      simpa [hfind'] using Nat.find_spec hab
    funext j
    exact le_antisymm (by simpa using (hwithin j).1) (by simpa using (hwithin j).2)
  · simp [SequenceDistance, hab] at h

/--
\begin{proposition}[Properties of distance of sequences]\label{Properties of distance of sequences}
Let $a,b,c\in {\rm A}$.
Then

(ii) $\dist(a,b)=\dist(b,a)$
\end{proposition}
-/
theorem sequenceDistance_comm (a b : ℤ → ℝ) : SequenceDistance a b = SequenceDistance b a := by
  classical
  by_cases h : ∃ k : ℕ, WithinSequenceDistance a b k
  · have h' : ∃ k : ℕ, WithinSequenceDistance b a k := by
      rcases h with ⟨k, hk⟩
      exact ⟨k, (aux_withinSequenceDistance_symm).1 hk⟩
    apply le_antisymm
    · rw [show SequenceDistance b a = (Nat.find h' : WithTop ℕ) by simp [SequenceDistance, h']]
      exact aux_sequenceDistance_le_of_within
        ((aux_withinSequenceDistance_symm).1 (Nat.find_spec h'))
    · rw [show SequenceDistance a b = (Nat.find h : WithTop ℕ) by simp [SequenceDistance, h]]
      exact aux_sequenceDistance_le_of_within
        ((aux_withinSequenceDistance_symm).2 (Nat.find_spec h))
  · have h' : ¬ ∃ k : ℕ, WithinSequenceDistance b a k := by
      intro hb
      rcases hb with ⟨k, hk⟩
      exact h ⟨k, (aux_withinSequenceDistance_symm).2 hk⟩
    simp [SequenceDistance, h, h']

/--
\begin{proposition}[Properties of distance of sequences]\label{Properties of distance of sequences}
Let $a,b,c\in {\rm A}$.
Then

(iii) $\dist(a,c)\le \dist(a,b)+\dist(b,c)$
\end{proposition}
-/
theorem sequenceDistance_triangle (a b c : ℤ → ℝ) :
    SequenceDistance a c ≤ SequenceDistance a b + SequenceDistance b c := by
  classical
  by_cases hab : ∃ k : ℕ, WithinSequenceDistance a b k
  · by_cases hbc : ∃ l : ℕ, WithinSequenceDistance b c l
    · have hcomp : WithinSequenceDistance a c (Nat.find hab + Nat.find hbc) :=
        aux_withinSequenceDistance_trans (Nat.find_spec hab) (Nat.find_spec hbc)
      rw [show SequenceDistance a b = (Nat.find hab : WithTop ℕ) by simp [SequenceDistance, hab],
        show SequenceDistance b c = (Nat.find hbc : WithTop ℕ) by simp [SequenceDistance, hbc]]
      calc
        SequenceDistance a c ≤ ((Nat.find hab + Nat.find hbc : ℕ) : WithTop ℕ) :=
          aux_sequenceDistance_le_of_within hcomp
        _ = (Nat.find hab : WithTop ℕ) + (Nat.find hbc : WithTop ℕ) := by simp
    · simp [SequenceDistance, hbc]
  · simp [SequenceDistance, hab]

/--
\begin{proposition}[Properties of distance of sequences]\label{Properties of distance of sequences}
Let $a,b,c\in {\rm A}$.
Then

(iv) If $c(j)=b(j+1)$, then $\dist(a,c)\le \dist(a,b)+1$.
\end{proposition}
-/
theorem sequenceDistance_shift_le {a b c : ℤ → ℝ} (ha : SpacedSequence a) (hb : SpacedSequence b)
    (hc : ∀ j : ℤ, c j = b (j + 1)) :
    SequenceDistance a c ≤ SequenceDistance a b + 1 := by
  classical
  by_cases hab : ∃ k : ℕ, WithinSequenceDistance a b k
  · have hwithin : WithinSequenceDistance a c (Nat.find hab + 1) := by
      intro j
      constructor
      · calc
          a (j - (Nat.find hab + 1)) ≤ a (j - Nat.find hab) := by
            apply (aux_spacedSequence_monotone ha)
            omega
          _ ≤ b j := (Nat.find_spec hab j).1
          _ ≤ b (j + 1) := aux_spacedSequence_le_succ hb j
          _ = c j := (hc j).symm
      · rw [hc j]
        have h' := (Nat.find_spec hab (j + 1)).2
        simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h'
    rw [show SequenceDistance a b = (Nat.find hab : WithTop ℕ) by simp [SequenceDistance, hab]]
    calc
      SequenceDistance a c ≤ ((Nat.find hab + 1 : ℕ) : WithTop ℕ) :=
        aux_sequenceDistance_le_of_within hwithin
      _ = (Nat.find hab : WithTop ℕ) + 1 := by simp
  · simp [SequenceDistance, hab]

/--
\begin{proposition}[Properties of distance of sequences]\label{Properties of distance of sequences}
Let $a,b,c\in {\rm A}$.
Then

(v) For all $t>0$, $\dist(t\cdot a,t\cdot b)=\dist(a,b)$
\end{proposition}
-/
theorem sequenceDistance_smul (a b : ℤ → ℝ) {t : ℝ} (ht : 0 < t) :
    SequenceDistance (fun j => t * a j) (fun j => t * b j) = SequenceDistance a b := by
  classical
  have hiff (k : ℕ) :
      WithinSequenceDistance (fun j => t * a j) (fun j => t * b j) k ↔
        WithinSequenceDistance a b k := by
    constructor <;> intro h <;> intro j
    · constructor
      · nlinarith [(h j).1]
      · nlinarith [(h j).2]
    · constructor
      · exact mul_le_mul_of_nonneg_left (h j).1 (le_of_lt ht)
      · exact mul_le_mul_of_nonneg_left (h j).2 (le_of_lt ht)
  by_cases h : ∃ k : ℕ, WithinSequenceDistance a b k
  · have h' : ∃ k : ℕ, WithinSequenceDistance (fun j => t * a j) (fun j => t * b j) k := by
      rcases h with ⟨k, hk⟩
      exact ⟨k, (hiff k).2 hk⟩
    apply le_antisymm
    · rw [show SequenceDistance a b = (Nat.find h : WithTop ℕ) by simp [SequenceDistance, h]]
      exact aux_sequenceDistance_le_of_within ((hiff (Nat.find h)).2 (Nat.find_spec h))
    · rw [show SequenceDistance (fun j => t * a j) (fun j => t * b j) =
        (Nat.find h' : WithTop ℕ) by simp [SequenceDistance, h']]
      exact aux_sequenceDistance_le_of_within ((hiff (Nat.find h')).1 (Nat.find_spec h'))
  · have h' : ¬ ∃ k : ℕ, WithinSequenceDistance (fun j => t * a j) (fun j => t * b j) k := by
      intro h'
      rcases h' with ⟨k, hk⟩
      exact h ⟨k, (hiff k).1 hk⟩
    simp [SequenceDistance, h, h']

/--
\begin{proposition}[Properties of distance of sequences]\label{Properties of distance of sequences}
Let $a,b,c\in {\rm A}$.
Then

(vi) For all $h\in\mathbb{Z}$,
$\dist(a,2^h a)\le |h|$.
\end{proposition}
-/
theorem sequenceDistance_pow_two_smul_le {a : ℤ → ℝ} (ha : SpacedSequence a) (h : ℤ) :
    SequenceDistance a (fun j => (2 : ℝ) ^ h * a j) ≤ (Int.natAbs h : WithTop ℕ) := by
  classical
  rcases Int.eq_nat_or_neg h with ⟨m, rfl | rfl⟩
  · have hpow : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hwithin : WithinSequenceDistance a (fun j => (2 : ℝ) ^ (m : ℤ) * a j) m := by
      intro j
      constructor
      · calc
          a (j - m) ≤ a j := aux_spacedSequence_monotone ha (by omega)
          _ ≤ (2 : ℝ) ^ (m : ℤ) * a j := by
            rw [zpow_natCast]
            nlinarith [(ha j).1]
      · calc
          (2 : ℝ) ^ (m : ℤ) * a j = (2 : ℝ) ^ m * a j := by rw [zpow_natCast]
          _ ≤ a (j + m) := aux_pow_two_mul_le_shift ha j m
    simpa [zpow_natCast] using aux_sequenceDistance_le_of_within hwithin
  · have hpow_pos : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) _
    have hpow : 1 ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    have hinv (j : ℤ) : (2 : ℝ) ^ (-(m : ℤ)) * a j = a j / (2 : ℝ) ^ m := by
      rw [zpow_neg, zpow_natCast]
      field_simp
    have hwithin : WithinSequenceDistance a (fun j => (2 : ℝ) ^ (-(m : ℤ)) * a j) m := by
      intro j
      constructor
      · change a (j - (m : ℤ)) ≤ (2 : ℝ) ^ (-(m : ℤ)) * a j
        rw [hinv j]
        apply (le_div_iff₀ hpow_pos).2
        simpa [mul_comm] using aux_pow_two_mul_shift_le ha j m
      · calc
          (2 : ℝ) ^ (-(m : ℤ)) * a j = a j / (2 : ℝ) ^ m := hinv j
          _ ≤ a j := by
            apply (div_le_iff₀ hpow_pos).2
            nlinarith [(ha j).1]
          _ ≤ a (j + m) := aux_spacedSequence_monotone ha (by omega)
    simpa [Int.natAbs_neg, zpow_natCast] using aux_sequenceDistance_le_of_within hwithin

/--
\begin{definition}[Closed balls in $\mathrm{A}$]\label{closed balls in A}
For $a\in\mathrm{A}$ and $r>0$ denote
\begin{equation}\label{auto:spaced-sequence-distance-ball}B_{\mathrm{dist}}(a,r)=\{b\in\mathrm{A}\,:\,\dist(a,b)\le r\}.\end{equation}
\end{definition}
-/
def sequenceDistanceBall (a : ℤ → ℝ) (r : WithTop ℕ) : Set (ℤ → ℝ) :=
  {b | SpacedSequence b ∧ SequenceDistance a b ≤ r}

end Codex.Preliminaries.MultiplicativelySpacedMonotoneSequences
