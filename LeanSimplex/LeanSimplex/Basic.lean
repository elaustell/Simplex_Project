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

--  Tableau representation (standard form)
    /- LP in standard form: maximize c^T subject to Ax = b, x >= 0

        A: The constraint matrix
            - len(A) = number of constraints m
            - len(A[0]) = number of variables n
            - each row A[r] corresponds to one linear constraint (coefficients of the variables)

        b: RHS of the constraints
            - Each b[r] is the value that the corresponding row of A should sum to
            - len(b) = # constraints = len(A)

        v: Current value of objective function

        B: Indices of basic variables
            - a basic feasible solution (BFS) is defined by selecting a set of variables
              that correspond to the columns of A forming a non-singular square matrix.
            - B[i] is the column index in A of the i-th basic variable.
            - len(B) = number of constraints = m
              (since the basis must have exactly one variable per constraint).

        N: indices of non-basic variables
            - All variables not in the basis are in N.
            - partition the set {0, 1, …, n-1} together with B.
            - candidates for entering the basis during pivoting.


            Simplex Tableau

                        x0      x1      x2   ...    xn-1   |  RHS b
                B0   A[0][0] A[0][1] A[0][2] ... A[0][n-1] |   b[0]
                B1   A[1][0] A[1][1] A[1][2] ... A[1][n-1] |   b[1]
                B2   A[2][0] A[2][1] A[2][2] ... A[2][n-1] |   b[2]
                ...
                Bm-1 A[m-1][0]  ...               ...      | b[m-1]
                -------------------------------------------
                        c[0]   c[1]    c[2]  ...   c[n-1]  |  v

    -/

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
  (t : Tableau m n) (enter : Fin n) (r : Fin m) (k : Fin n)
  (h_enter_in_N : t.N k = enter)
  : Tableau m n :=

  let piv := t.A r enter
  let oldB := t.B r

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
  (k : Fin n) (h_enter_in_N : t.N k = enter)
  (h_pivot_pos : 0 < t.A r enter)
  (h_feasible : feasible t)
  (h_ratio : ∀ i : Fin m, t.A i enter > 0 → t.b r / t.A r enter ≤ t.b i / t.A i enter)
  : feasible (pivot t enter r k h_enter_in_N) :=
by
  intro i
  let t' := pivot t enter r k h_enter_in_N
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
      simp_all
      exact le_trans term_nonneg (h_feasible i)


lemma x_in_N_implies_x_not_in_B {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t)
                      (x : Fin n) (k : Fin n) (x_in_N : t.N k = x) :
  ∀ (y : Fin m), t.B y ≠ x := by
  intros y
  unfold WellFormed at h_wf
  obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
  by_contra h_cont
  have h1 : x ∈ (Set.range t.B) := by
    simp
    apply Exists.intro y
    exact h_cont
  have h2 : x ∈ (Set.range t.N) := by
    simp
    apply Exists.intro k
    exact x_in_N
  have B_N_subeq_empty : Set.range t.B ∩ Set.range t.N ⊆ ∅ := Set.subset_empty_iff.mpr B_N_disjoint
  have B_N_disjoint2 : Disjoint (Set.range t.B) (Set.range t.N)
      := Set.disjoint_iff.mpr B_N_subeq_empty
  have h_dis := Set.disjoint_left.mp B_N_disjoint2
  apply h_dis at h1
  simp_all

theorem pivot_preserves_well_formedness {m n : ℕ}
  (t : Tableau m n) (enter : Fin n) (r : Fin m)
  (k : Fin n) (h_enter_in_N : t.N k = enter)
  (h_wf : WellFormed t)
  : WellFormed (pivot t enter r k h_enter_in_N) := by
  unfold WellFormed at *
  -- obtain ⟨h1, h2, h3, h4⟩ := h_wf
  let t' := (pivot t enter r k h_enter_in_N)
  constructor
  · -- WTS B' is Injective
    unfold pivot
    simp_all
    unfold Function.Injective at *
    intros a1 a2 h5
    by_cases a1_r_eq : a1 = r
    · -- case a1 == r
      simp_all
      by_cases a2_r_eq : a2 = r
      · symm
        exact a2_r_eq
      ·
        unfold Function.update at h5
        simp_all
        -- SO we have a hypothesis that says enter = t.B a2
        -- In other words, that enter was in B
        -- However, enter was actually in N
        -- and B and N are disjoint
        -- hence contradiction
        have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf enter k h_enter_in_N a2
        simp_all
    · -- case a1 ≠ r
      by_cases a2_r_eq : a2 = r
      ·
        simp_all
        unfold Function.update at h5
        simp_all
        have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf enter k h_enter_in_N a1
        simp_all
      ·
        unfold Function.update at h5
        simp_all
        obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
        apply B_inj at h5
        exact h5

  · constructor
    · -- WTS N' is injective
      unfold pivot
      simp_all
      unfold Function.Injective at *
      intros a1 a2 h5
      by_cases a1_r_eq : a1 = k
      · -- case a1 == k
        simp_all
        by_cases a2_r_eq : a2 = k
        · symm
          exact a2_r_eq
        ·
          unfold Function.update at h5
          simp_all
          -- SO we have a hypothesis that says enter = t.B a2
          -- In other words, that enter was in B
          -- However, enter was actually in N
          -- and B and N are disjoint
          -- hence contradiction
          have lem : t.N a2 = t.N a2 := by rfl
          have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf (t.N a2) a2 lem r
          simp_all
      · -- case a1 ≠ k
        by_cases a2_r_eq : a2 = k
        ·
          simp_all
          unfold Function.update at h5
          simp_all
          have lem : t.N a1 = t.N a1 := by rfl
          have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf (t.N a1) a1 lem r
          simp_all
        ·
          unfold Function.update at h5
          simp_all
          obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
          apply N_inj at h5
          exact h5


-- TODO
lemma pivot_improves_objective {m n : ℕ} (t : Tableau m n)
  (enter : Fin n) (r : Fin m)
  (h_enter_in_N : ∃ k, t.N k = enter)
  (h_pivot_pos : 0 < t.A r enter)
  (h_feasible : feasible t)
  (h_ratio : ∀ i, t.A i enter > 0 → t.b r / t.A r enter ≤ t.b i / t.A i enter)
  (h_c_pos : 0 < t.c enter)
  : (pivot t enter r h_enter_in_N).v > t.v :=
  sorry
