import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
-- import Mathlib.LinearAlgebra.Matrix
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

open Matrix

inductive CmpOp
  | leq
  | eq
  | geq

def CmpOp.eval (op : CmpOp) (x y : ℝ) : Prop :=
  match op with
  | .leq => x ≤ y
  | .eq => x = y
  | .geq => x ≥ y

-- infix:50 " ⋈ " => CmpOp.eval

structure constraints (n : ℕ) where
  (A : Fin n → ℝ)
  (b : ℝ)
  (ops : CmpOp)

inductive objective
  | max
  | min

structure generic_LP (m n : ℕ) where
  (cons : Fin m → constraints n)
  (obj : objective)
  (x : Fin n → ℝ)
  (c : Fin n → ℝ)


def my_sum_helper (index : ℕ) (f : ℕ → ℝ) : ℝ :=
  match index with
  | .zero => 0
  | .succ n => f index + my_sum_helper n f

def my_sum {n : ℕ} (index : ℕ) (f : (Fin n) → ℝ) :=
  my_sum_helper index (fun x => if h : x < n then
    let i : Fin n := ⟨x, h⟩
    f i
  else 0)

lemma split_sum (n m : ℕ) (index : ℕ) (f : Fin n → ℝ) :
  my_sum index (fun (i : Fin (n+m)) => if h : i.val < n then f (i.castLT h) else 0)
  = my_sum index f := by
  induction m with
  | zero =>
    simp_all
    sorry
  | succ m =>
    rename_i IH
    rewrite [← IH]
    have hf_equal :
      (fun (i : Fin (n + (m + 1))) ↦ if h : ↑i < n then f (i.castLT h) else 0)
      = (fun (i : Fin (n + m)) ↦ if h : ↑i < n then f (i.castLT h) else 0) := by




-- max ∑ᵢ cᵢ xᵢ
-- s.t. ∑ᵢ Aⱼᵢxᵢ ≤ bⱼ, ∀j
-- xᵢ ≥ 0, ∀i
structure standard_LP (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)

def solution_is_feasible_standard_LP {m n : ℕ} (lp : standard_LP m n) (x : Fin n → ℝ) : Prop :=
  -- (∀ (j : Fin m), ∑ i, (lp.A j i * x i) ≤ lp.b j) ∧
  (∀ (j : Fin m), my_sum n (fun i => lp.A j i * x i) ≤ lp.b j) ∧
  ∀ (i : Fin n), x i ≥ 0


def get_objective_value_standard_LP {m n : ℕ} (lp : standard_LP m n) (solution : Fin n → ℝ) : ℝ :=
  -- ∑ i, ((lp.c i) * (solution i))
  my_sum n (fun i => ((lp.c i) * (solution i)))

def make_standard {m n : ℕ} (lp : generic_LP m n) : standard_LP m n :=
  let c := match lp.obj with
    | .min => (fun i => -1 * lp.c i)
    | .max => lp.c
  let b := fun i => (lp.cons i).b
  let A := fun i : Fin m => fun j => match (lp.cons i).ops with
    | .leq => (lp.cons i).A j
    | .eq => (lp.cons i).A j
    | .geq =>  -1 * ((lp.cons i).A j)
  ⟨A,b,c⟩

structure LP (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)

def solution_is_feasible_LP {m n : ℕ} (lp : LP m n) (x : Fin n → ℝ) : Prop :=
  -- (∀ (j : Fin m), ∑ i, (lp.A j i * x i) = lp.b j) ∧
  (∀ (j : Fin m), my_sum n (fun i => (lp.A j i * x i)) = lp.b j) ∧
  ∀ (i : Fin n), x i ≥ 0

def get_objective_value_LP {m n : ℕ} (lp : LP m n) (solution : Fin n → ℝ) : ℝ :=
  -- ∑ i, ((lp.c i) * (solution i))
  my_sum n (fun i => ((lp.c i) * (solution i)))

/-- Adds a slack variable to the jth constraint by putting a coefficient
    of 1 at the n+jth index and all other variables past n are 0
-/
def add_slack_to_constraint {m n : ℕ} (A_j : Fin n → ℝ) (j : Fin m) : Fin (n+m) → ℝ :=
  fun i => if h : i.val < n then A_j (Fin.castLT i h) else
    if i = (n + j) then 1 else 0

lemma feasible_constraint_slack {m n : ℕ} (A_j : Fin n → ℝ) (j : Fin m) (b_j : ℝ) :
  ∀(x : Fin n → ℝ), my_sum n (fun i => A_j i * x i) ≤ b_j ↔
    my_sum (n+m) (fun i => (add_slack_to_constraint A_j j) i *
      (fun j => if h : j.val < n then x (j.castLT h) else 0) i) = b_j := by

  intro x
  constructor
  · intro h
    unfold add_slack_to_constraint


def add_slack_variables {m n : ℕ} (lp : standard_LP m n) : LP m (n + m) :=
  let c := fun i : Fin (n + m) => if h : i.val < n then lp.c (Fin.castLT i h) else 0
  let b := lp.b
  let A := fun j : Fin m => add_slack_to_constraint (lp.A j) j
  ⟨A,b,c⟩

-- def add_slack_variables {m n : ℕ} (lp : standard_LP m n) : LP m (n + m) :=
--   let c := fun i : Fin (n + m) => if h : i.val < n then lp.c (Fin.castLT i h) else 0
--   let b := lp.b
--   let A := fun j : Fin m => fun i : Fin (n + m) =>
--     if h : i.val < n then lp.A j (Fin.castLT i h) else 1
--   ⟨A,b,c⟩

lemma le_imp_exists_add_real {a b : ℝ} : a ≤ b → ∃ (c : ℝ), a + c = b := by
  intro h
  apply Exists.intro (b-a)
  simp_all

-- lemma split_sum (n m : ℕ) (f : Fin (n + m) → ℝ) : ∑ i : Fin (n+m), f i
--         =
--       (∑ i : {i : Fin (n+m) // i < n}, f i)
--       +
--       (∑ i : {i : Fin (n+m) // n ≤ i}, f i) := by

--     induction m with
--     | zero =>
--       simp_all
--       unfold Finset.sum

lemma sum_f_eq_sum_g {m n : ℕ}
    (f : Fin (n + m) → ℝ)
    (g : Fin n → ℝ)
    (h1 : ∀ (i : Fin (n + m)) (h : i < n), f i = g (Fin.castLT i h))
    (h2 : ∀ (i : Fin (n + m)), n ≤ i → f i = 0) :
    my_sum (n+m) f = my_sum n g := by
    unfold my_sum
    unfold my_sum_helper
    induction n with
    | zero =>
      simp_all
      induction m with
      | zero => simp_all
      | succ =>
        simp_all
        unfold my_sum_helper
        simp_all
    | succ num1 IH1 =>
        simp_all
        have h3 : num1 + 1 + m = Nat.succ (num1 + m) := by
          simp
          grind
        simp [h3]
        induction m with
        | zero =>
          simp
          unfold my_sum_helper
          sorry
        | succ num2 IH2 =>
          simp_all
          sorry



-- lemma sum_f_eq_sum_g {m n : ℕ}
--     (f : Fin (n+m) → ℝ)
--     (g : Fin n → ℝ)
--     (h1 : ∀ (i : Fin (n + m)) (h : i < n), f i = g (Fin.castLT i h))
--     (h2 : ∀ (i : Fin (n + m)), n ≤ i → f i = 0) :
--     ∑ i : Fin (n+m), f i = ∑ i : Fin n, g i := by
--   classical

--   -- Split the sum over Fin (n+m) into indices < n and ≥ n
--   have :
--       ∑ i : Fin (n+m), f i
--         =
--       (∑ i : {i : Fin (n+m) // i < n}, f i)
--       +
--       (∑ i : {i : Fin (n+m) // n ≤ i}, f i) := by
--     -- apply Finset.sum_univ
--     -- simpa [Fin.sum_univ_split]  -- Mathlib lemma
--     have h3 := Finset.sum_fin_eq_sum_range f
--     simp [h3]
--     have h4 := Fintype.sum_eq_add_sum_subtype_ne f
--     -- apply Fintype.sum
--     sorry

--   simp [this]

--   -- Evaluate the < n part: use h1
--   have hlt :
--       (∑ i : {i : Fin (n+m) // i < n}, f i)
--         =
--       (∑ i : {i : Fin (n+m) // i < n}, g ⟨i, i.property⟩) := by


--     refine sum_congr rfl ?_ ?_
--     intro i _
--     simpa [h1 _ i.property]

--   -- {i // i < n} is equivalent to Fin n
--   have h_equiv :
--       (∑ i : {i : Fin (n+m) // i < n}, g ⟨i, i.property⟩)
--         =
--       ∑ i : Fin n, g i := by
--     -- Use equivalence Fin (n+m) < n  ≃  Fin n
--     classical
--     simpa using
--       (Fin.sum_subtype_lt_equiv (n := n) (f := g))

--   -- Evaluate the ≥ n part: it's all zeros by h2
--   have hge :
--       (∑ i : {i : Fin (n+m) // n ≤ i}, f i) = 0 := by
--     simp [h2]

--   -- Combine results
--   simpa [hlt, h_equiv, hge]




-- v is a feasible objective value for an LP iff
-- v is a feasible objective value for the LP after adding slack vars
theorem adding_slack_equivalent_LP {m n : ℕ} : ∀ (lp : standard_LP m n) (v : ℝ),
  (∃x, solution_is_feasible_standard_LP lp x
    ∧ get_objective_value_standard_LP lp x = v)
  ↔
  (∃y, solution_is_feasible_LP (add_slack_variables lp) y
    ∧ get_objective_value_LP (add_slack_variables lp) y = v) := by

  intros lp v
  constructor
  · intro h
    obtain ⟨x, h_feasible, h_v⟩ := h
    let c := fun i : Fin (n + m) => if h : i.val < n then lp.c (Fin.castLT i h) else 0
    apply Exists.intro c
    unfold solution_is_feasible_LP
    unfold add_slack_variables
    unfold get_objective_value_LP
    unfold add_slack_to_constraint
    simp_all
    unfold solution_is_feasible_standard_LP at h_feasible
    unfold get_objective_value_standard_LP at h_v
    constructor
    · constructor
      · intro j
        obtain ⟨h1,h2⟩ := h_feasible
        have h3 := h1 j
        apply le_imp_exists_add_real at h3
        obtain ⟨a,h3⟩ := h3
        rewrite [← h3]
        have h5 := sum_f_eq_sum_g
          (fun i ↦ if h : ↑i < n then lp.A j (i.castLT h) * c i else c i)
          (fun i ↦ lp.A j i * x i)

        unfold my_sum at *

        simp_all




    sorry
  · intro h
    obtain ⟨y, h_feasible, h_v⟩ := h
    unfold solution_is_feasible_LP at h_feasible
    obtain ⟨h1,h2⟩ := h_feasible
    sorry





noncomputable def zeros {n : Type} [Fintype n] (f : n → ℝ) : Finset n :=
  Finset.univ.filter (fun x => f x = 0)

noncomputable def nonzeros {n : Type} [Fintype n] (f : n → ℝ) : Finset n :=
  Finset.univ.filter (fun x => f x ≠ 0)

def WellFormed_LP {m n : ℕ} (lp : LP m n) : Prop :=
  (n > m) -- because we have a basic variable per constraint + nonbasic variables
  ∧ (zeros lp.c).toList.length = m -- num basic variables
  ∧ (nonzeros lp.c).toList.length = n-m -- num nonbasic variables
  ∧ (zeros lp.c) ∩ (nonzeros lp.c) = ∅

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
          - is it true that v = c_B^⊤ (A_B^{-1} b) ?

        c: Objective function to maximize

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
                     A[0][0] A[0][1] A[0][2] ... A[0][n-1] |   b[0]
                     A[1][0] A[1][1] A[1][2] ... A[1][n-1] |   b[1]
                     A[2][0] A[2][1] A[2][2] ... A[2][n-1] |   b[2]
                        ⋮       ⋮       ⋮      ⋮      ⋮           ⋮
                     A[m-1][0]  ...   ...         ...      | b[m-1]
                -------------------------------------------
                        c[0]   c[1]    c[2]  ...   c[n-1]  |  v

    -/

structure Tableau (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)
  (v : ℝ)
  (B : Fin m → Fin n) -- basic variables
  (N : Fin (n-m) → Fin n) -- non-basic variables
  (Visited_Bases : Finset (Fin m → Fin n))
  (Original_LP : LP m n)

def basicSolution {m n : ℕ} (t : Tableau m n) : Fin n → ℝ :=
  fun j =>
    match (List.finRange m).find? (fun i => t.B i = j) with
    | some i => t.b i
    | none   => 0

def Tableau.objective_value {m n : ℕ} (t : Tableau m n) : ℝ :=
  ∑ x, ((t.c x) * (basicSolution t x))


-- The values in b correspond to the basic feasible solution.
-- because every constraint has one basic variable and all others
-- are nonbasic variables set to 0.
def feasible {m n : ℕ} (t : Tableau m n) : Prop :=
  ∀ i, t.b i ≥ 0

def WellFormed {m n : ℕ} (t : Tableau m n) : Prop :=
  Function.Injective t.B ∧
  Function.Injective t.N ∧
  Set.range t.B ∪ Set.range t.N = Set.univ ∧
  Set.range t.B ∩ Set.range t.N = ∅ ∧
  n > m ∧
  (∀x, t.c x ≠ 0 ↔ x ∈ Set.range t.N)

  -- (∀x, t.c x = 0 ↔ x ∈ Set.range t.B) ∧

  -- t.v = t.objective_value


  -- TODO: need one basic variable per constaint aka row of A?
  -- basically, exactly one row in a column from B should be nonzero.
  -- ∧ ∀ (i : Fin n), (∃k, t.B k = i) → (∃j, A[i][j] ≠ 0 ∧ ∀l, l ≠ j → A[i][j] == 0)

noncomputable def make_B {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) : Fin m → Fin n :=
  have h : (zeros lp.c).toList.length = m := by
    unfold WellFormed_LP at h_wf
    simp_all
  have h2 : m = (zeros lp.c).toList.length := by
    simp_all
  -- have h2 : ∀ j : Fin m, ∃ i : Fin ((zeros lp.c).toList.length), i = j := by
  fun j => (zeros lp.c).toList.get (Fin.cast h2 j)

noncomputable def make_N {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) : Fin (n-m) → Fin n :=
  have h : (nonzeros lp.c).toList.length = (n-m) := by
    unfold WellFormed_LP at h_wf
    simp_all
  have h2 : n-m = (nonzeros lp.c).toList.length := by
    simp_all
  fun j => (nonzeros lp.c).toList.get (Fin.cast h2 j)

noncomputable def make_tableau {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) : Tableau m n :=
  ⟨lp.A, lp.b, lp.c, 0, make_B lp h_wf, make_N lp h_wf, {make_B lp h_wf}, lp⟩

lemma List.Nodup.get_inj {α : Type} {l : List α} (h : l.Nodup) (i j : Fin l.length) :
    l.get i = l.get j ↔ i = j := by
    apply List.Nodup.get_inj_iff
    simp_all

lemma nodup_inj {α : Type} {n : ℕ} (l : List α)
  (h : n = l.length)
  (a1 a2 : Fin n)
  (nodup : l.Nodup)
  (eq : l[Fin.cast h a1] = l[Fin.cast h a2]) :
  a1 = a2 :=
by
  -- have nodup := Finset.nodup_toList s
  have h2 := (List.Nodup.get_inj nodup)
  -- simp_all
  have h3 := h2 (Fin.cast h a1) (Fin.cast h a2)
  obtain ⟨h4, h5⟩ := h3
  simp_all

lemma list_mem_explicit {α : Type} (l : List α) (a : α) : a ∈ l ↔ ∃ n, l.get n = a := by
  apply List.mem_iff_get

lemma wf_lp_to_tableau {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) :
  WellFormed (make_tableau lp h_wf) := by
  unfold WellFormed
  unfold WellFormed_LP at h_wf
  obtain ⟨h1, h2, h3, h4⟩ := h_wf
  unfold make_tableau
  simp_all
  constructor
  · unfold Function.Injective
    unfold make_B
    unfold zeros at *
    have no_duplicates := Finset.nodup_toList {x | lp.c x = 0}
    intro a1 a2
    exact nodup_inj ({x | lp.c x = 0} : Finset (Fin n)).toList
                            h2.symm a1 a2 no_duplicates
  · constructor
    · unfold Function.Injective
      unfold make_N
      unfold nonzeros at *
      have no_duplicates := Finset.nodup_toList {x | lp.c x ≠ 0}
      intro a1 a2
      exact nodup_inj ({x | lp.c x ≠ 0} : Finset (Fin n)).toList
                              h3.symm a1 a2 no_duplicates
    · constructor
      -- B ∪ N = universe
      · unfold make_B
        unfold make_N
        unfold zeros
        unfold nonzeros
        simp_all
        apply Set.eq_univ_iff_forall.mpr
        intro y
        by_cases y_is_zero : lp.c y = 0
        · left
          have h6 := list_mem_explicit ({x | lp.c x = 0} : Finset (Fin n)).toList y
          simp
          obtain ⟨h7,h8⟩ := h6
          have h9 : y ∈  ({x | lp.c x = 0} : Finset (Fin n)).toList := by
            simp_all
          simp_all
          obtain ⟨ind, h10⟩ := h7
          unfold zeros at h2
          apply Exists.intro (Fin.cast h2 ind)
          simp_all
        · simp_all
          right
          have h6 := list_mem_explicit ({x | lp.c x ≠ 0} : Finset (Fin n)).toList y
          obtain ⟨h7,h8⟩ := h6
          have h9 : y ∈  ({x | lp.c x ≠ 0} : Finset (Fin n)).toList := by
            simp_all
          simp_all
          obtain ⟨ind, h10⟩ := h7
          unfold nonzeros at h3
          apply Exists.intro (Fin.cast h3 ind)
          simp_all
      · constructor
        · -- B ∩ N = ∅
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x
          simp_all
          intro y x_in_B z
          unfold make_B at x_in_B
          by_contra x_in_N
          unfold make_N at x_in_N
          unfold zeros nonzeros at *
          have h5 := (list_mem_explicit ({x | lp.c x ≠ 0} : Finset (Fin n)).toList x).mpr
          have h6 := (list_mem_explicit ({x | lp.c x = 0} : Finset (Fin n)).toList x).mpr
          have h7 : (∃ n_1, ({x | lp.c x ≠ 0} : Finset (Fin n)).toList.get n_1 = x) := by
            apply Exists.intro (Fin.cast h3.symm z)
            simp_all
          have h8 : (∃ n_1, ({x | lp.c x = 0} : Finset (Fin n)).toList.get n_1 = x) := by
            apply Exists.intro (Fin.cast h2.symm y)
            simp_all
          apply h5 at h7
          apply h6 at h8
          simp_all
        · intro x
          constructor
          · unfold make_N
            intro h
            unfold nonzeros at *
            simp_all
            have h_mem : x ∈ ({x | ¬lp.c x = 0} : Finset (Fin n)).toList := by simp_all
            apply List.getElem_of_mem at h_mem
            simp_all
            obtain ⟨y, hy, h_mem⟩ := h_mem

            apply Exists.intro ⟨y,hy⟩
            rewrite [← h_mem]
            rfl
          · intro h
            obtain ⟨y,hy⟩ := h
            unfold make_N at hy
            unfold nonzeros at hy
            apply List.mem_of_getElem at hy
            simp_all
