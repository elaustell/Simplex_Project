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

-- def make_standard {m n : ℕ} (lp : generic_LP m n) : LP m n :=
--   let c := match lp.obj with
--     | min => (fun i => -1 * lp.c i)
--     | max => lp.c
--   let A := fun i : Fin m => fun j => match lp.constraints.ops with
--     | leq => lp.constraints.A i j
--     | eq => lp.constraints.A i j
--     | geq =>  -1 * (lp.constraints.A i j)

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


def add_slack_variables {m n : ℕ} (lp : standard_LP m n) : LP m (n + m) :=
  let c := fun i : Fin (n + m) => if h : i.val < n then lp.c (Fin.castLT i h) else 0
  let b := lp.b
  let A := fun j : Fin m => fun i : Fin (n + m) =>
    if h : i.val < n then lp.A j (Fin.castLT i h) else 1
  ⟨A,b,c⟩

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
  (∀x, t.c x ≠ 0 → x ∈ Set.range t.N)

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
  ⟨lp.A, lp.b, lp.c, 0, make_B lp h_wf, make_N lp h_wf, {make_B lp h_wf}⟩


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


        -- · constructor
        --   · intro x
        --     constructor
        --     · intro h5
        --       unfold make_B
        --       unfold zeros
        --       simp_all
        --       have h6 : x ∈ ({x | lp.c x = 0}: Finset (Fin n)) := by
        --         simp_all
        --       -- apply
        --       -- apply List.get_of_mem
        --       have h7 : x ∈ ({x | lp.c x = 0} : Finset (Fin n)).toList := by
        --         apply Finset.mem_toList.mpr h6
        --       have h8 := List.mem_iff_getElem.mp h7
        --       obtain ⟨y, hy, h8⟩ := h8
        --       sorry
        --     · intro h5
        --       unfold make_B at h5
        --       unfold zeros at h5
        --       obtain ⟨y,h5⟩ := h5
        --       sorry
        --   · intro x
        --     sorry


lemma N_nonempty {m n : ℕ} (t : Tableau m n) : WellFormed t → ∃ enter, (∃k, t.N k = enter) := by
  intro h
  unfold WellFormed at h
  obtain ⟨_,_,_,_,h1,_,_,_⟩ := h
  have h2 := n-m
  sorry




-- An entering variable should be NEGATIVE in c
-- A leaving variable should have the minimum positive
-- ratio in the ratio test.
noncomputable def pivot {m n : ℕ}
  (t : Tableau m n) (enter : Fin n) (r : Fin m) (k : Fin (n - m))
  (_ : t.N k = enter) (_ : t.c enter > 0)
  (new_basis : Function.update t.B r enter ∉ t.Visited_Bases)
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
  let Visited_Bases' := t.Visited_Bases.cons B' new_basis
  ⟨A', b', c', v', B', N', Visited_Bases'⟩

-- lemma pivot_preserves_v {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t)
--   (enter : Fin n) (r : Fin m) (k : Fin (n - m))
--   (h_enter_in_N : t.N k = enter) (h_c_enter_pos : t.c enter > 0)
--   (h_new_basis : Function.update t.B r enter ∉ t.Visited_Bases) :

--   (pivot t enter r k h_enter_in_N h_c_enter_pos h_new_basis).v
--   = (pivot t enter r k h_enter_in_N h_c_enter_pos h_new_basis).objective_value := by

--   unfold pivot
--   obtain ⟨_,_,_,_,_,_,_,h⟩ := h_wf
--   unfold Tableau.objective_value at *
--   unfold basicSolution at *
--   simp
--   apply Finset.sum_eq


noncomputable def helper_find_argmin {α : Type} (l : List α) (f : α → ℝ) (current_min : α) : α :=
  match l with
  | [] => current_min
  | head :: tail =>
    if f current_min < f head
      then helper_find_argmin tail f current_min
      else helper_find_argmin tail f head


lemma helper_find_argmin_membership {α : Type} (l : List α) (f : α → ℝ) :
    ∀ (current_min : α),
    (helper_find_argmin l f current_min) ∈ l
  ∨ (helper_find_argmin l f current_min) = current_min := by

  induction l with
  | nil =>
    unfold helper_find_argmin
    simp_all
  | cons head tail IH =>
    simp_all
    intro current_min
    by_cases h : f current_min < f head
    · unfold helper_find_argmin
      simp_all
      have IH1 := IH current_min
      cases IH1
      · rename_i IH1
        left
        right
        exact IH1
      · rename_i IH1
        right
        exact IH1
    · unfold helper_find_argmin
      simp [h]
      have IH1 := IH head
      cases IH1
      · rename_i IH1
        left
        right
        exact IH1
      · rename_i IH1
        left
        left
        exact IH1


-- Returns the element of type α from l that results in the minimum
-- value in the range of f
noncomputable def List.find_argmin {α : Type} (l : List α) (f : α → ℝ) : Option α :=
  match l with
  | [] => none
  | head :: tail => some (helper_find_argmin tail f head)

lemma List.find_argmin_preserves_membership {α : Type} (l : List α) (f : α → ℝ) (a : α)
  (h : l.find_argmin f = some a) : a ∈ l := by
  unfold List.find_argmin at h
  induction l with
  | nil =>
    simp_all
  | cons head1 tail1 IH1 =>
    simp_all
    have h1 := helper_find_argmin_membership tail1 f head1
    simp_all
    cases h1
    · rename_i h1
      right
      exact h1
    · rename_i h2
      left
      exact h2

-- We want to find a variable that is in N
-- with a negative coefficient
-- more specifically, the most negative coefficient in c
noncomputable def find_entering_variable {m n : ℕ} (t : Tableau m n)
  : Option (Fin n) :=
  let neg_candidates_indices := (Finset.univ.image t.N).filter (fun x => t.c x > 0)
  neg_candidates_indices.toList.find_argmin t.c

lemma enter_var_pos_coefficient {m n : ℕ} (t : Tableau m n) (enter : Fin n) :
  (find_entering_variable t) = some enter → t.c enter > 0 := by
  intro h
  unfold find_entering_variable at h
  simp_all
  have h2 := List.find_argmin_preserves_membership
      {x ∈ Finset.image t.N Finset.univ | 0 < t.c x}.toList t.c enter h
  simp_all

lemma entering_in_N {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t) :
  (∃x, t.c x > 0) → ∃k, t.N k = find_entering_variable t := by
  intro h
  unfold find_entering_variable
  simp_all
  unfold List.find_argmin
  obtain ⟨x,h⟩ := h
  unfold WellFormed at h_wf
  obtain ⟨_,_,_,_,_,h2⟩ := h_wf
  split
  · rename_i l h_contra
    have h1 : x ∈ {x ∈ Finset.image t.N Finset.univ | t.c x > 0} := by
      simp
      have h3 := h2 x
      have h4 : t.c x < 0 ∨ 0 < t.c x := by
        right
        exact h
      have h5 := ne_iff_lt_or_gt.mpr h4
      apply h3 at h5
      simp_all
    have h2 := Finset.mem_toList.mpr h1
    rewrite [h_contra] at h2
    simp at h2
  · rename_i head tail h_list
    have h3 := helper_find_argmin_membership tail t.c head
    cases h3
    · rename_i h_case
      have h4 : helper_find_argmin tail t.c head ∈ head :: tail := by
        simp
        right
        exact h_case
      rewrite [← h_list] at h4
      have h5 := Finset.mem_toList.mp h4
      simp_all
    · rename_i h_case
      rewrite [h_case]
      have h4 : head ∈ {x ∈ Finset.image t.N Finset.univ | 0 < t.c x}.toList := by simp_all
      have h5 := Finset.mem_toList.mp h4
      simp_all


-- A leaving variable should have the minimum positive
-- ratio in the ratio test.
-- h_ratio : ∀ i : Fin m, t.A i enter > 0
--         → t.b r / t.A r enter ≤ t.b i / t.A i enter)
-- Should be in B
noncomputable def find_leaving_variable {m n : ℕ} (t : Tableau m n) (enter : Fin n)
      : Option (Fin m) :=
  let candidates := (Finset.univ).filter (fun x : Fin m => (t.b x) / (t.A x enter) > 0)
  candidates.toList.find_argmin (fun x : Fin m => (t.b x) / (t.A x enter))


lemma piv_in_candidates {m n : ℕ} (t : Tableau m n) (enter : Fin n) (leaving : Fin m)
      (h_leaving : find_leaving_variable t enter = some leaving) :
  leaving ∈ (Finset.univ).filter (fun x : Fin m => (t.b x) / (t.A x enter) > 0) := by

  unfold find_leaving_variable at h_leaving
  have h1 := (List.find_argmin_preserves_membership
      ({x | 0 < t.b x / t.A x enter} : Finset (Fin m)).toList
      (fun x ↦ t.b x / t.A x enter)
      leaving) h_leaving
  simp_all


lemma piv_positive {m n : ℕ} (t : Tableau m n)
    (h_feasible : feasible t) (enter : Fin n) (leaving : Fin m)
    (h_leaving : find_leaving_variable t enter = some leaving) :
  0 < t.A leaving enter := by

  have h_mem := piv_in_candidates t enter leaving h_leaving
  simp_all
  unfold feasible at h_feasible
  by_contra h_contra
  simp_all
  have h3 := h_feasible leaving
  have h4 := div_nonpos_of_nonneg_of_nonpos h3 h_contra
  have h5 : ¬(t.b leaving / t.A leaving enter > 0) := by
    apply not_lt_of_ge
    exact h4
  simp_all

lemma leaving_ratio_positive {m n : ℕ} (t : Tableau m n) (enter : Fin n) (leaving : Fin m)
      (h_leaving : find_leaving_variable t enter = some leaving) :
  t.b leaving / t.A leaving enter > 0 := by

  have h_mem := piv_in_candidates t enter leaving h_leaving
  simp_all


lemma leaving_min_pos_ratio {m n : ℕ} (t : Tableau m n)
    (enter : Fin n) (leaving : Fin m)
    (h_leaving : find_leaving_variable t enter = some leaving) :

    ∀ i : Fin m, (t.b i) / (t.A i enter) ≤ t.b i / t.A i enter := by
      sorry

-- lemma leaving_min_pos_ratio {m n : ℕ} (t : Tableau m n) (h_feasible : feasible t)
--     (enter : Fin n) (leaving : Fin m)
--     (h_leaving : find_leaving_variable t enter = some leaving) :
--   ∀ i : Fin m, t.A i enter > 0 →
--   t.b leaving
--     / t.A leaving enter
--     ≤ t.b i / t.A i enter := by
--   intro i h
--   have h_leaving2 := h_leaving
--   unfold find_leaving_variable at h_leaving
--   unfold feasible at h_feasible
--   simp_all
--   unfold List.find_argmin at h_leaving
--   unfold helper_find_argmin at h_leaving
--   split at h_leaving
--   · simp_all
--   · simp_all
--     rename_i l head tail h2
--     induction tail with
--     | nil =>
--       -- basically there was only one candidate for leaving variable
--       -- so it turns out that i = leaving
--       simp at h_leaving

--     --   simp_all
--       by_cases h_cases : leaving = i
--       · simp_all
--       · have h3 : i ∉ ({x | 0 < t.b x / t.A x enter} : Finset (Fin m)) := by
--           simp_all
--           have h4 := Finset.eq_singleton_iff_nonempty_unique_mem.mp h2
--           obtain ⟨h4, h5⟩ := h4
--           by_contra h_contra
--           simp_all
--         have h4 : i ∈ ({x | 0 < t.b x / t.A x enter} : Finset (Fin m)) := by
--           simp
--           simp_all

--         have h4 : t.b i = 0 := by
--           apply eq_iff_le_not_lt.mpr
--           simp_all




        -- have h_contra : ¬(0 < t.b i / t.A i enter) := by
        --   by_contra h4
        --   have h5 : i ∈ ({x | 0 < t.b x / t.A x enter} : Finset (Fin m)) := by
        --     simp
        --     exact h4
        --   simp_all
        -- have h4 : t.b i = 0 := by
        --   apply eq_iff_le_not_lt.mpr
        --   simp_all

        -- simp_all
        -- have h_pos_ratio := leaving_ratio_positive t enter leaving h_leaving2








lemma enter_is_unique {m n : ℕ} (t1 t2 : Tableau m n) :
  find_entering_variable t1 = find_entering_variable t2 →
  (find_entering_variable t1).isSome = true → t1.N = t2.N := by

  unfold find_entering_variable
  unfold List.find_argmin
  simp_all
  by_cases h1 : {x ∈ Finset.image t1.N Finset.univ | 0 < t1.c x}.toList = []
  · rewrite [h1]
    simp
    intro h
    by_cases h2 : {x ∈ Finset.image t2.N Finset.univ | 0 < t2.c x}.toList = []
    · rewrite [h2]
      simp_all
    · have h3 := List.cons_head_tail h2
      rewrite [← h3] at *
      rename_i h4
      simp at h
  · have h3 := List.cons_head_tail h1
    by_cases h2 : {x ∈ Finset.image t2.N Finset.univ | 0 < t2.c x}.toList = []
    · rewrite [h2]
      simp
    · have h4 := List.cons_head_tail h2
      rewrite [← h4]
      rewrite [← h3]
      simp
      intro h
      by_contra h_contra
      have h9 := Function.ne_iff.mp h_contra
      obtain ⟨a, h9⟩ := h9



      rename_i h_neq
      have h_bad : t1.N = t2.N → False := by
        intro h10
        simp_all
      have h6 := h_contra.mp



  intro h


def all_bases (m n : ℕ) : Finset (Fin m → Fin n) := Finset.univ

def decreasing_measure {m n : ℕ} (t : Tableau m n) : Nat :=
  (all_bases m n).card - t.Visited_Bases.card

lemma pivot_decreases_measure
  {m n : ℕ} (t : Tableau m n) (enter : Fin n) (r : Fin m) (k : Fin (n - m))
  (enter_in_N : t.N k = enter) (enter_pos_c : t.c enter > 0)
  (new_basis : Function.update t.B r enter ∉ t.Visited_Bases) :
    decreasing_measure (pivot t enter r k enter_in_N enter_pos_c new_basis)
    < decreasing_measure t := by

  let B' := Function.update t.B r enter

  have hB' : B' ∈ all_bases m n := by
    unfold all_bases
    simp_all

  -- Because B' ∈ all_bases but B' ∉ t.Visited_Bases, and t.Visited_Bases ⊆ all_bases,
  -- we get strict inequality:
  have hcard_lt : t.Visited_Bases.card < (all_bases m n).card := by
    unfold all_bases
    apply Finset.card_lt_card
    apply Finset.ssubset_univ_iff.mpr
    by_contra h_contra
    apply Finset.eq_univ_iff_forall.mp at h_contra
    simp_all

  -- from `C < A` we get `C + 1 ≤ A`
  have hsucc_le : t.Visited_Bases.card + 1 ≤ (all_bases m n).card := Nat.succ_le_of_lt hcard_lt

  unfold decreasing_measure
  unfold pivot
  simp_all
  apply Nat.sub_lt_sub_left
  · exact hcard_lt
  simp_all

structure pivot_arguments (m n : ℕ) where
  t : Tableau m n
  entering : Fin n
  leaving : Fin m
  k : Fin (n - m)
  h_enter_in_N : t.N k = entering
  h_c_pos : t.c entering > 0
  -- h_new_basis : Function.update t.B leaving entering ∉ t.Visited_Bases
  -- h_pivot_pos : 0 < t.A leaving entering
  -- h_ratio : t.b leaving / t.A leaving entering > 0

noncomputable def get_pivot_arguments {m n : ℕ} (t : Tableau m n)
              (h_wf : WellFormed t) : Option (pivot_arguments m n) :=
  match h : (find_entering_variable t) with
  | none => none
  | some enter =>
    have h_issome : (find_entering_variable t).isSome := by
      rewrite [h]
      apply Option.isSome_some
    match h2 : (find_leaving_variable t enter) with
    | none => none
    | some leaving =>
        have h1 :  ∃ x, t.c x > 0 := by
          apply Exists.intro enter
          simp_all
          apply (enter_var_pos_coefficient t enter h)
        have h_enter_in_N := entering_in_N t h_wf h1
        have N_k_is_enter : t.N (Classical.choose h_enter_in_N) = enter := by
          have h1 := Classical.choose_spec h_enter_in_N
          simp_all
        have t_c_positive : t.c enter > 0 := by
          have h2 := enter_var_pos_coefficient t enter
          simp_all
        -- have h_pivot_pos : 0 < t.A leaving enter := by
        --   unfold find_leaving_variable at h2
        --   simp at h2
        --   unfold List.find_argmin at h2
        --   by_cases match_none : ({x | 0 < t.b x / t.A x enter} : Finset (Fin m)).toList = []
        --   · simp_all
        --   · apply List.ne_nil_iff_exists_cons.mp at match_none
        --     obtain ⟨head, tail, match_some⟩ := match_none
        --     simp_all
        --     unfold helper_find_argmin at h2
        --   have h3 := Option.eq_some_iff_get_eq.mp h2


        -- h_ratio : t.b leaving / t.A leaving entering > 0
        -- have new_base : Function.update t.B leaving enter ∉ t.Visited_Bases := by
        --   sorry
        -- pivot_until_done
        some {
          t := t
          entering := enter
          leaving := leaving
          k := (Classical.choose h_enter_in_N)
          h_enter_in_N := N_k_is_enter
          h_c_pos := t_c_positive
        }


lemma pivot_args_some_implies_entering_some {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t) :
  (get_pivot_arguments t h_wf).isSome = true → (find_entering_variable t).isSome = true := by
  simp [get_pivot_arguments]
  split
  · simp
  · split
    · simp
    · simp_all


lemma pivot_args_some_implies_leaving_some {m n : ℕ}
  (t : Tableau m n) (h_wf : WellFormed t) (enter : Fin n)
  (h : (get_pivot_arguments t h_wf).isSome = true)
  (h2 : find_entering_variable t = some enter) :
  (find_leaving_variable t enter).isSome = true := by


  unfold get_pivot_arguments at h
  apply Option.isSome_iff_exists.mpr
  apply Option.isSome_iff_exists.mp at h

  obtain ⟨args, h_args⟩ := h
  split at h_args
  · simp_all
  · split at h_args
    · simp_all
    · rename_i enter2 h4 leaving2 h5
      simp_all


noncomputable def pivot2 {m n : ℕ} (args : pivot_arguments m n)
  : Tableau m n :=

  let t := args.t
  let r := args.leaving
  let enter := args.entering
  let k := args.k

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
  -- let Visited_Bases' := t.Visited_Bases.cons B' new_basis
  let Visited_Bases' := t.Visited_Bases ∪ {B'}
  ⟨A', b', c', v', B', N', Visited_Bases'⟩



-- returns true if there is some finite amount of pivots that can turn
-- t1 into t2
-- inductive PivotedFrom {m n : ℕ} : Tableau m n → Tableau m n → Prop
-- | step (t : Tableau m n) (args : pivot_arguments m n)
--     (h_args : get_pivot_arguments t = some args) :
--     PivotedFrom t (pivot2 args)
-- | trans {t1 t2 t3}
--     (h12 : PivotedFrom t1 t2) (h23 : PivotedFrom t2 t3) :
--     PivotedFrom t1 t3

inductive PivotedFrom (m n : ℕ) :
    Tableau m n → Tableau m n → Prop
| step :
    ∀ {t t'} (args : pivot_arguments m n)
      (h_wf : WellFormed t),
      get_pivot_arguments t h_wf = some args →
      t' = pivot2 args →
      PivotedFrom m n t t'
| trans :
    ∀ {t₁ t₂ t₃},
      PivotedFrom m n t₁ t₂ →
      PivotedFrom m n t₂ t₃ →
      PivotedFrom m n t₁ t₃

lemma get_piv_arguments_unchanged_t {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t)
  (args : pivot_arguments m n) (h : get_pivot_arguments t h_wf = some args) :
    t = args.t := by

  have h_piv_args_isSome : (get_pivot_arguments t h_wf).isSome := by
    simp_all
  unfold get_pivot_arguments at h
  have h_entering_isSome := pivot_args_some_implies_entering_some t h_wf h_piv_args_isSome
  apply Option.isSome_iff_exists.mp at h_entering_isSome
  obtain ⟨enter, h_enter⟩ := h_entering_isSome
  have h_leaving := pivot_args_some_implies_leaving_some t h_wf enter h_piv_args_isSome h_enter
  apply Option.isSome_iff_exists.mp at h_leaving
  obtain ⟨leaving, h_leaving⟩ := h_leaving
  split at h
  · simp_all
  · split at h
    · simp_all
    · simp_all
      rewrite [← h]
      simp_all

lemma pivot2_improves_objective {m n : ℕ} (t : Tableau m n) (h_feasible : feasible t)
    (h_wf : WellFormed t) (args : pivot_arguments m n)
    (h_args : get_pivot_arguments t h_wf = some args) :
    (pivot2 args).v > args.t.v := by
  unfold pivot2
  simp_all
  have h_enter_in_N := args.h_enter_in_N
  have h_c_pos := args.h_c_pos
  have h_unchanged_t := get_piv_arguments_unchanged_t t h_wf args h_args
  have args_feasible : feasible args.t := by simp_all
  have h_args2 : (get_pivot_arguments t h_wf).isSome = true := by
    simp_all
  have h_entering_isSome := pivot_args_some_implies_entering_some t h_wf h_args2
  have h_enter_eq_enter := Option.isSome_iff_exists.mp h_entering_isSome
  obtain ⟨enter, h_enter_eq_enter⟩ := h_enter_eq_enter
  have h_leaving_isSome := pivot_args_some_implies_leaving_some t h_wf args.entering h_args2
  have h_args_enter_eq_enter : enter = args.entering := by
    unfold get_pivot_arguments at h_args
    simp_all
    split at h_args
    · simp_all
    · split at h_args
      · simp_all
      · simp_all
        rewrite [← h_args]
        simp_all
        rename_i h1 enter2 h_enter2 leaving2 h_leaving2
        rewrite [h1] at h_enter2
        simp_all
  have h_leave : find_leaving_variable args.t args.entering = some args.leaving := by
    simp_all
    unfold get_pivot_arguments at h_args
    simp_all
    split at h_args
    · simp_all
    · split at h_args
      · simp_all
      · simp_all
        rewrite [← h_args]
        simp_all

  have h_pivot_pos := piv_positive args.t args_feasible args.entering args.leaving h_leave
  have h_ratio : args.t.b args.leaving / args.t.A args.leaving args.entering > 0 :=
    leaving_ratio_positive args.t args.entering args.leaving h_leave
  simp_all

-- lemma le_div_iff_mul_le_explicit (a b c : ℝ) : a ≤ c / b → a * b ≤ c := by
--   intro h
--   rewrite [div_eq_inv_mul] at h
--   rewrite [mul_comm] at h
--   apply
--   -- have h2 := le_mul_inv_iff_mul_le.mp h
--   have h1 := le_div_iff_mul_le.mp h

lemma le_div_iff_mul_le_explicit (a c b : ℝ) (hb : 0 < b) :
  a ≤ c / b → a * b ≤ c :=
by
  intro h
  -- multiply both sides by b (positive)
  have := mul_le_mul_of_nonneg_right h (le_of_lt hb)
  -- rewrite c / b * b = c
  simpa [div_mul_eq_mul_div, hb.ne'] using this

lemma mul_div_eq (a b c d : ℝ) (hd : 0 < d) : a / b ≤ c / d → d / b * a ≤ c := by
  intro h
  have h2 := le_div_iff_mul_le_explicit (a / b) c d hd h
  rewrite [mul_comm]
  rewrite [← mul_div_left_comm]
  rewrite [mul_comm]
  exact h2



-- lemma le_div_iff_mul_le_explicit {a b c : ℝ} (h : 0 < b) :
--   a ≤ c / b → a * b ≤ c :=
-- by
--   intro h1
--   have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt h)
--   -- rewrite [div_mul_eq_mul_div] at h2
--   rewrite [div_eq_inv_mul] at h2
--   have h3 : c * b⁻¹ = b⁻¹ * c := by
--     rewrite [mul_comm]
--     simp_all
--   rewrite [← h3] at h2
--   rewrite [mul_assoc] at h2
--   have h4 : b⁻¹ * b = 1 := by
--     rewrite [mul_comm]
--     rewrite [mul_inv_cancel]


lemma pivot2_preserves_feasibility {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t)
  (h_feasible : feasible t) (args : pivot_arguments m n) (h : get_pivot_arguments t h_wf = some args) :
    feasible (pivot2 args) := by

  unfold feasible at *
  intro i
  simp_all
  unfold pivot2
  simp
  by_cases h_cases : i = args.leaving
  · simp [h_cases]
    apply div_nonneg_iff.mpr
    left
    constructor
    · have h3 := h_feasible args.leaving
      have h4 := get_piv_arguments_unchanged_t t h_wf args h
      simp_all
    · have h2 : ∃a, get_pivot_arguments t h_wf = some a := by simp_all
      have h3 := Option.isSome_iff_exists.mpr h2
      have h_entering_isSome := pivot_args_some_implies_entering_some t h_wf h3
      obtain ⟨enter, h_enter⟩ := Option.isSome_iff_exists.mp h_entering_isSome
      have h_leaving_isSome := pivot_args_some_implies_leaving_some t h_wf enter h3 h_enter
      unfold get_pivot_arguments at h
      have h4 := piv_positive t h_feasible args.entering args.leaving
      split at h
      · simp_all
      · split at h
        · simp at h
        · rename_i enter2 h_enter2 leaving2 h_leaving
          simp_all
          rewrite [← h] at h4
          simp at h4
          apply h4 at h_leaving
          rewrite [← h]
          apply le_iff_lt_or_eq.mpr
          simp_all
  · -- Case i ≠ args.leaving
    simp [h_cases]
    have h2 : ∃a, get_pivot_arguments t h_wf = some a := by simp_all
    have h3 := Option.isSome_iff_exists.mpr h2
    have h_entering_isSome := pivot_args_some_implies_entering_some t h_wf h3
    obtain ⟨enter, h_enter⟩ := Option.isSome_iff_exists.mp h_entering_isSome
    have h_leaving_isSome := pivot_args_some_implies_leaving_some t h_wf enter h3 h_enter
    have enters_eq : args.entering = enter := by
      unfold get_pivot_arguments at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · simp_all
          rewrite [← h]
          simp
    rewrite [← enters_eq] at h_leaving_isSome
    have h_leaving_eq : find_leaving_variable t args.entering = some args.leaving := by
      simp_all
      unfold get_pivot_arguments at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · simp at h
          rewrite [← h]
          simp_all
    have h_ratio : t.b i / t.A i enter > 0 →
      t.b args.leaving / t.A args.leaving enter ≤ t.b i / t.A i enter := by
        intro h_pos
        rewrite [← enters_eq] at h_pos
        have h9 := leaving_min_pos_ratio t args.entering args.leaving h_leaving_eq i h_pos
        simp_all
    by_cases h_pos : t.b i / t.A i enter > 0
    · have h5 := h_ratio h_pos
      apply mul_div_eq at h5
      · simp_all
        have h_args_t_eq_t := get_piv_arguments_unchanged_t t h_wf args h
        simp_all
      · simp_all
        apply div_pos_iff.mp at h_pos
        cases h_pos
        · rename_i h_pos_cases
          simp_all
        · rename_i h_pos_cases
          have h_contra : ¬ t.b i < 0 := by
            simp
            exact h_feasible i
          simp_all
    · -- Case t.b i / t.A i enter ≤ 0
      -- Since t.b i ≥ 0, it follows that either t.b i = 0 or t.A i enter < 0
      -- if t.b i = 0, then i ∈ B
      have h0 : t.A i enter ≤ 0 := by
        simp at h_pos
        apply div_nonpos_iff.mp at h_pos
        cases h_pos
        · simp_all
        · have h_tbi_0 : t.b i = 0 := by
          sorry
        sorry




      have h1 : args.t.A i enter / args.t.A args.leaving enter * args.t.b args.leaving ≤ 0 := by
        simp_all
        sorry
      sorry







    -- by_cases hA_positive : t.A i args.entering > 0
    -- · have h_ratio2 := h_ratio hA_positive

    --   have h_ratio2 := h_ratio h_leaving_isSome i hA_positive
    --   have h_same_t := get_piv_arguments_unchanged_t t args h
    --   have h4 : (t.b ((find_leaving_variable t args.entering).get h3) /
    --     t.A ((find_leaving_variable t args.entering).get h3) args.entering)
    --     * t.A i args.entering ≤ t.b i := sorry
    --       -- le_div_iff_mul_le.mp h_ratio2
    --   simp_all
    --   have h_args_eq : ((find_leaving_variable t args.entering).get h3) = args.leaving := by
    --     sorry







-- lemma pivot2_preserves_feasibility (m n : ℕ) (t1 t2 : Tableau m n)
--     (h_feasible : feasible t1) (h_pivoted : PivotedFrom m n t1 t2) :
--       feasible t2 := by
--     induction h_pivoted with
--     | step args h_get h_eq =>

lemma pivoted_from_preserves_feasibility {m n : ℕ} (t1 t2 : Tableau m n) :
    feasible t1 → PivotedFrom m n t1 t2 → feasible t2 := by
  intro h1 h2
  induction h2 with
  | step args h_wf h_args h_eq =>
    rename_i t3 t4
    have h3 := pivot2_preserves_feasibility t3 h_wf h1 args h_args
    simp_all
  | trans h12 ih12 h23 ih23 =>
      rename_i t3 t4 t5
      simp_all


lemma pivoted_from_preserves_well_formedness {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotedFrom m n t1 t2 → WellFormed t1 := by
  intro h
  induction h with
  | step => simp_all
  | trans h12 ih12 h23 ih23 =>
      rename_i t3 t4 t5
      simp_all

theorem pivoted_from_increases_v {m n : ℕ}
    (t1 t2 : Tableau m n) (h1_feasible : feasible t1) (h2_feasible : feasible t2) :
    PivotedFrom m n t1 t2 → (t2.v > t1.v) := by
  intro h
  induction h with
  | step args h_wf h_get h_eq =>
    rename_i t3 t4
    have h_args_isSome : (get_pivot_arguments t3 h_wf).isSome = true := by simp_all
    have h_pivot_increases := pivot2_improves_objective t3 h1_feasible h_wf args h_get
    simp_all
    have h_args_t := get_piv_arguments_unchanged_t t3 h_wf args h_get
    simp_all
  | trans h12 ih12 h23 ih23 =>
    rename_i t3 t4 t5
    simp_all
    have h_t3_wf := pivoted_from_preserves_well_formedness t3 t4 h12
    have h_t4_feasible := pivoted_from_preserves_feasibility t3 t4 h1_feasible h12
    simp_all
    exact lt_trans (h23) (ih23)

lemma pivoted_from_previous_bases {m n : ℕ} (t1 : Tableau m n) (B : Fin m → Fin n) :
  B ∈ t1.Visited_Bases → ∃t2, PivotedFrom m n t1 t2 ∧ t2.B = B := by
  intro h

lemma basis_determines_v {m n : ℕ} (t1 t2 : Tableau m n) :
    PivotedFrom m n t1 t2 → t2.B ∉ t1.Visited_Bases := by
    intro h
    induction h with
    | step args h_wf h_get h_eq =>
      rename_i t3 t4
      -- unfold get_pivot_arguments at h_get
      unfold pivot2 at h_eq
      rewrite [h_eq]
      simp





noncomputable def Simplex_Algorithm {m n : ℕ} (lp : LP m n) (h_wflp : WellFormed_LP lp) : ℝ :=
  let t := make_tableau lp h_wflp


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

theorem pivot_preserves_feasibility {m n : ℕ} (t : Tableau m n)
  (enter : Fin n) (r : Fin m)
  (k : Fin (n - m)) (h_enter_in_N : t.N k = enter)
  (h_pivot_pos : 0 < t.A r enter)
  (h_feasible : feasible t)
  (h_ratio : ∀ i : Fin m, t.A i enter > 0 → t.b r / t.A r enter ≤ t.b i / t.A i enter)
  (h_c_pos : t.c enter > 0)
  (h_newBase: Function.update t.B r enter ∉ t.Visited_Bases)
  : feasible (pivot t enter r k h_enter_in_N h_c_pos h_newBase) :=
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
                      (x : Fin n) (k : Fin (n - m)) :
  (t.N k = x) → (∀ (y : Fin m), t.B y ≠ x) := by
  intros x_in_N y
  unfold WellFormed at h_wf
  obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint, _⟩ := h_wf
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

lemma x_not_in_B_implies_x_in_N {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t) (x : Fin n) :
  (¬∃ (y : Fin m), t.B y = x) → (∃p, t.N p = x) := by
  intro h
  unfold WellFormed at h_wf
  obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
  -- B_N_universe will be the key here
  by_contra h_cont
  rewrite [Set.union_def] at B_N_universe
  simp at B_N_universe
  apply Set.eq_univ_iff_forall.mp at B_N_universe
  have contra := B_N_universe x
  simp [h_cont] at contra
  simp_all

lemma contrapose_injectivity {α β : Type} (f : α → β) :
  Function.Injective f → (∀ (a1 a2 : α), a1 ≠ a2 → f a1 ≠ f a2) := by
  intro h
  intros a1 a2
  contrapose
  unfold Function.Injective at h
  simp_all
  apply h

-- Everything that was zero should stay zero
-- except that entering and leaving variables switch
lemma pivot_preserves_zeros_cardinality {m n : ℕ}
  (t : Tableau m n) (enter : Fin n) (leaving : Fin m)
  (k : Fin (n - m)) (h_enter_in_N : t.N k = enter)
  (h_wf : WellFormed t)
  (h_tc_enter_neg : t.c enter > 0)
  (h_newBase : Function.update t.B r enter ∉ t.Visited_Bases)
  (h_ratio : ∀ i : Fin m, t.A i enter > 0 → t.b leaving / t.A leaving enter ≤ t.b i / t.A i enter)
   :
    ∀x, x ∈ (zeros t.c) →
        x ∈ (zeros (pivot t enter leaving k h_enter_in_N h_tc_enter_neg h_newBase).c)
      ∨ x == enter := by

    intros x h
    by_cases x_is_enter : x = enter
    · right
      simp_all
    · left
      unfold pivot
      unfold zeros at *
      simp_all
      unfold WellFormed at h_wf


theorem pivot_preserves_well_formedness {m n : ℕ}
  (t : Tableau m n) (enter : Fin n) (r : Fin m)
  (k : Fin (n - m)) (h_enter_in_N : t.N k = enter)
  (h_wf : WellFormed t)
  (h_c_pos : t.c enter > 0)
  (h_newBase : Function.update t.B r enter ∉ t.Visited_Bases)
  : WellFormed (pivot t enter r k h_enter_in_N h_c_pos h_newBase) := by

  let t' := (pivot t enter r k h_enter_in_N h_c_pos h_newBase)
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
      · unfold Function.update at h5
        simp_all
        have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf enter k h_enter_in_N a2
        simp_all
    · -- case a1 ≠ r
      by_cases a2_r_eq : a2 = r
      · simp_all
        unfold Function.update at h5
        simp_all
        have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf enter k h_enter_in_N a1
        simp_all
      · unfold Function.update at h5
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
        · unfold Function.update at h5
          simp_all
          have lem : t.N a2 = t.N a2 := by rfl
          have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf (t.N a2) a2 lem r
          simp_all
      · -- case a1 ≠ k
        by_cases a2_r_eq : a2 = k
        · simp_all
          unfold Function.update at h5
          simp_all
          have lem : t.N a1 = t.N a1 := by rfl
          have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf (t.N a1) a1 lem r
          simp_all
        · unfold Function.update at h5
          simp_all
          obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
          apply N_inj at h5
          exact h5
    · constructor
      · -- WTS N' ∪ B' = universe
        unfold pivot
        simp_all
        apply Set.eq_univ_iff_forall.mpr
        intro x
        rewrite [Set.union_def]
        simp_all
        unfold Function.update
        simp_all
        by_cases x_in_B : ∃p, t.B p = x
        · -- case x ∈ B
          obtain ⟨p,x_in_B⟩ := x_in_B
          by_cases p_is_r : p = r
          · -- case x == t.B r, need y = k
            right
            apply Exists.intro k
            simp_all
          · left
            apply Exists.intro p
            simp_all
        · -- case x ∈ N
          have x_in_N := x_not_in_B_implies_x_in_N t h_wf x x_in_B
          obtain ⟨p,x_in_N⟩ := x_in_N
          by_cases x_is_enter : x = enter
          · -- case x == enter
            left
            apply Exists.intro r
            simp_all
          · right
            -- need to find a y ≠ k
            apply Exists.intro p
            by_cases p_is_k : p = k
            · simp_all
            · simp_all
      · constructor
        · -- WTS N' ∩ B' = ∅
          unfold pivot
          simp_all
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x1
          simp_all
          intros x2 h1 x3
          unfold Function.update
          by_cases x3_is_k : x3 = k
          · simp_all
            unfold Function.update at h1
            by_cases x2_is_r : x2 = r
            · simp_all
              rewrite [← h1]
              have h4 := x_in_N_implies_x_not_in_B t h_wf enter k
              apply h4 at h_enter_in_N
              exact h_enter_in_N r
            · simp_all
              rewrite [← h1]
              unfold WellFormed at h_wf
              obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
              unfold Function.Injective at B_inj
              contrapose B_inj
              simp_all
              apply Exists.intro x2
              simp_all
              apply Exists.intro r
              simp_all
          · simp_all
            unfold Function.update at h1
            by_cases x2_is_r : x2 = r
            · simp_all
              rewrite [← h1]
              rewrite [← h_enter_in_N]
              obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
              have h_N_inj := contrapose_injectivity t.N N_inj x3 k
              simp_all
            · simp_all
              rewrite [← h1]
              have h3 := x_in_N_implies_x_not_in_B t h_wf (t.N x3) x3
              simp at h3
              have h4 := h3 x2
              rewrite [← ne_eq] at *
              symm
              exact h4
        · constructor
          · unfold WellFormed at h_wf
            simp_all
          · intro x h
            unfold pivot
            simp_all
            unfold Function.update
            unfold WellFormed at h_wf
            obtain ⟨_,_,_,_,_,h1⟩ := h_wf
            -- obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h_wf
            simp_all
          -- constructor
          -- · intro x
          --   constructor
          --   · intro hyp
          --     unfold Function.update

theorem pivot_improves_objective {m n : ℕ} (t : Tableau m n)
  (enter : Fin n) (leave : Fin m) (k : Fin (n - m))
  (h_enter_in_N : t.N k = enter)
  (h_pivot_pos : 0 < t.A leave enter)
  (h_ratio : t.b leave / t.A leave enter > 0)
  (h_c_pos : t.c enter > 0)
  (h_newBase : Function.update t.B leave enter ∉ t.Visited_Bases)
  : (pivot t enter leave k h_enter_in_N h_c_pos h_newBase).v > t.v := by

  unfold pivot at *
  simp_all

-- lemma pivoted_from_new_base :

noncomputable def pivot_until_done {m n : ℕ}
  (t : Tableau m n) (h_wf : WellFormed t) : Tableau m n :=
  match h : (find_entering_variable t) with
  | none => t
  | some enter =>
    have h_issome : (find_entering_variable t).isSome := by
      rewrite [h]
      apply Option.isSome_some
    match find_leaving_variable t enter with
    | none => t
    | some leaving =>
        have h1 :  ∃ x, t.c x > 0 := by
          apply Exists.intro enter
          simp_all
          apply (enter_var_pos_coefficient t enter h)
        have h_enter_in_N := entering_in_N t h_wf h1
        have N_k_is_enter : t.N (Classical.choose h_enter_in_N) = enter := by
          have h1 := Classical.choose_spec h_enter_in_N
          simp_all
        have t_c_positive : t.c enter > 0 := by
          have h2 := enter_var_pos_coefficient t enter
          simp_all
        have new_base : Function.update t.B leaving enter ∉ t.Visited_Bases := by

          sorry
        pivot_until_done
          (pivot t enter leaving (Classical.choose h_enter_in_N) N_k_is_enter t_c_positive new_base)
          (pivot_preserves_well_formedness t enter leaving
            (Classical.choose h_enter_in_N) N_k_is_enter h_wf t_c_positive new_base)

termination_by decreasing_measure t
decreasing_by
  unfold decreasing_measure
  apply pivot_decreases_measure
