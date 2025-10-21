import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
-- import Mathlib.LinearAlgebra.Matrix
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

open Matrix

structure LP (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)

structure Tableau (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)
  (v : ℝ)
  (B : Fin m → Fin n) -- basic variables
  (N : Fin n → Fin n) -- non-basic variables

def WellFormed {m n : ℕ} (t : Tableau m n) : Prop :=
  Function.Injective t.B ∧
  Function.Injective t.N ∧
  Set.range t.B ∪ Set.range t.N = Set.univ ∧
  Set.range t.B ∩ Set.range t.N = ∅

def basicSolution {m n : ℕ} (t : Tableau m n) : Fin n → ℝ :=
  fun j =>
    match (List.finRange m).find? (fun i => t.B i = j) with
    | some i => t.b i
    | none   => 0

def feasible {m n : ℕ} (t : Tableau m n) : Prop :=
  ∀ i, t.b i ≥ 0

noncomputable def pivot {m n : ℕ}
  (t : Tableau m n) (enter : Fin n) (r : Fin m)
  (h_enter_in_N : ∃ k : Fin n, t.N k = enter)
  : Tableau m n :=

  let piv := t.A r enter
  let oldB := t.B r
  -- find the index k in N such that N[k] = enter
  let k := Classical.choose h_enter_in_N
  -- updated A, b, c, v
  let A' := fun i j => if i = r then t.A r j / piv else t.A i j - (t.A i enter / piv) * t.A r j
  let b' := fun i => if i = r then t.b i / piv else t.b i - (t.A i enter / piv) * t.b r
  let c' := fun j => t.c j - (t.c enter / piv) * t.A r j
  let v' := t.v + (t.c enter / piv) * t.b r
  -- updated B and N
  let B' := Function.update t.B r enter
  let N' := Function.update t.N k oldB
  ⟨A', b', c', v', B', N'⟩

lemma le_mul : ∀ (a b c : ℝ), 0 < c → a ≤ b → c*a ≤ c*b := by
  intros a b c h1 h2
  simp_all


lemma some_linear_arith : ∀ (a b c d : ℝ),
  0 < a  → a * (b/c) ≤ a * (d/a) → (a/c) * b ≤ d := by
  intros a b c d h1 h2
  have h4 := mul_comm_div a c b
  rewrite [← h4] at h2
  have h5 := mul_comm_div a a d
  rewrite [← h5] at h2
  have h6 : a ≠ 0 := by
    by_contra
    simp_all
  have h7 := div_self h6
  rewrite [h7] at h2
  simp at h2
  exact h2

lemma pivot_preserves_feasibility {m n : ℕ} (t : Tableau m n)
  (enter : Fin n) (r : Fin m)
  (h_enter_in_N : ∃ k : Fin n, t.N k = enter)
  (h_pivot_pos : 0 < t.A r enter)
  (h_feasible : feasible t)
  (h_ratio : ∀ i : Fin m, t.A i enter > 0 → t.b r / t.A r enter ≤ t.b i / t.A i enter)
  : feasible (pivot t enter r h_enter_in_N) :=
by
  intro i
  let t' := pivot t enter r h_enter_in_N
  by_cases h : i = r
  · -- leaving row
    rw [h]
    dsimp [pivot, basicSolution]
    have hr_nonneg : 0 ≤ t.b r := h_feasible r
    simp
    exact div_nonneg hr_nonneg (le_of_lt h_pivot_pos)
  · -- other rows
    dsimp [pivot, basicSolution]
    let A_i_enter := t.A i enter
    let b_i := t.b i
    let b_r := t.b r
    let piv := t.A r enter
    -- new value: b[i]' = b[i] - (A[i][enter]/piv)*b[r]
    by_cases hA_pos : A_i_enter > 0
    -- If A[i,enter] > 0 use ratio test: (b_r / piv) ≤ (b_i / A_i_enter)
    · have ratio := h_ratio i hA_pos
      -- multiply the ratio inequality by A_i_enter > 0:
      -- (A_i_enter / piv) * b_r = A_i_enter * (b_r / piv) ≤ A_i_enter * (b_i / A_i_enter) = b_i
      have h3 : (A_i_enter / piv) * b_r ≤ b_i := by
        -- rewrite (A_i_enter / piv) * b_r as A_i_enter * (b_r / piv)
        rw [div_eq_mul_inv]
        -- now multiply both sides of ratio by A_i_enter > 0
        have h_temp := mul_le_mul_of_nonneg_left ratio (le_of_lt hA_pos)
        -- simp_all
        have h_temp3 := (le_mul (t.b r / t.A r enter) (t.b i / t.A i enter)
                                (t.A i enter)) hA_pos ratio
        exact some_linear_arith (t.A i enter) (t.b r) (t.A r enter) (t.b i) hA_pos h_temp3
      simp [h]
      exact h3

    · -- If A[i,enter] ≤ 0 then (A_i_enter / piv) ≤ 0, so subtracting it
      -- b_i - (A_i_enter/piv)*b_r = b_i + (-(A_i_enter/piv))*b_r which is ≥ 0
      have hdiv_nonpos : A_i_enter / piv ≤ 0 := by
        have h3 : A_i_enter ≤ 0 → A_i_enter / piv ≤ 0 / piv
          := (div_le_div_iff_of_pos_right h_pivot_pos).mpr
        have h4 := le_of_not_gt hA_pos
        apply h3 at h4
        simp_all

      have term_nonneg : 0 ≤ -(A_i_enter / piv) * b_r := by
        -- -(A_i_enter / piv) ≥ 0 and b_r ≥ 0, so product ≥ 0
        have : 0 ≤ -(A_i_enter / piv) := by
          let h1 := neg_le_neg hdiv_nonpos
          rewrite [neg_zero] at h1
          exact h1

        exact mul_nonneg this (h_feasible r)
      -- now sum of nonnegatives is nonneg

      simp_all
      have h3 : A_i_enter ≤ 0 → A_i_enter / piv ≤ 0 / piv
        := (div_le_div_iff_of_pos_right h_pivot_pos).mpr
      -- have h4 := le_of_not_gt hA_pos
      apply h3 at hA_pos
      simp_all
      have zero_leq_piv : 0 = piv ∨ 0 < piv := by
        right
        exact h_pivot_pos

      -- exact le_trans term_nonneg (le_of_eq_or_lt zero_leq_piv)
      -- exact add_nonneg (h_feasible i) term_nonneg
      exact le_trans term_nonneg (h_feasible i)
