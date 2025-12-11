import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
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

def feasible_standard_LP {m n : ℕ} (lp : standard_LP m n) : Prop :=
∃x, solution_is_feasible_standard_LP lp x


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

def Feasible_LP {m n : ℕ} (lp : LP m n) : Prop :=
∃x, solution_is_feasible_LP lp x

def Feasible_LP2 {m n : ℕ} (lp : LP m n) : Prop :=
  ∀i, lp.b i ≥ 0

def feas_equiv {m n : ℕ} (lp : LP m n) : Feasible_LP lp ↔ Feasible_LP2 lp := by
  constructor
  · intro h
    unfold Feasible_LP at h
    unfold Feasible_LP2
    intro i
    sorry
  · intro h
    unfold Feasible_LP
    unfold Feasible_LP2 at h
    apply Exists.intro  fun j =>
      match (List.finRange m).find? (fun i => t.B i = j) with
      | some i => t.b i
      | none   => 0


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

def feasible2 {m n : ℕ} (t : Tableau m n) : Prop :=
  ∃ (x : Fin n → ℝ), (∀ (j : Fin m), my_sum n (fun i => (t.A j i * x i)) = t.b j) ∧
  ∀ (i : Fin n), x i ≥ 0

lemma feasible_equiv {m n : ℕ} (t : Tableau m n) :
  feasible2 t ↔ feasible t := by
  constructor
  · intro h
    unfold feasible
    unfold feasible2 at h
    intro i
    obtain ⟨x, h1, h2⟩ := h
    specialize h1 i
    rewrite [← h1]
    by_contra
    simp_all
    unfold my_sum at h1
    unfold my_sum_helper at h1
    cases n with
    | zero => simp_all
    | succ n =>
      simp at h1
    sorry
  · intro h
    unfold feasible at h
    unfold feasible2
    apply Exists.intro fun j =>
      match (List.finRange m).find? (fun i => t.B i = j) with
      | some i => t.b i
      | none   => 0
    simp_all
    constructor
    · intro j
      simp


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

lemma feasible_lp_to_tableau {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) (h_feas : Feasible_LP lp) :
  feasible (make_tableau lp h_wf) := by
  unfold feasible
  unfold Feasible_LP at h_feas
  unfold solution_is_feasible_LP at h_feas
  intro i
  unfold make_tableau
  simp_all
  obtain ⟨x,h_feas1, h_feas2⟩ := h_feas
  specialize h_feas1 i
  rewrite [← h_feas1]
  unfold my_sum
  simp
  induction n with
  | zero =>
    simp
    unfold my_sum_helper
    simp
  | succ n =>
    rename_i IH
    specialize IH lp




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

def List.helper_min {n : ℕ} (l : List (Fin n)) (current_min : (Fin n)) : Fin n :=
  match l with
  | [] => current_min
  | head :: tail =>
    if current_min < head
      then tail.helper_min current_min
      else tail.helper_min head

def List.min {n : ℕ} (l : List (Fin n)) : Option (Fin n):=
  match l with
  | [] => none
  | head :: tail => some (tail.helper_min head)

@[simp]
lemma List.min_none_iff {n : ℕ} (l : List (Fin n)) : l.min = none ↔ l = [] := by
  unfold List.min
  constructor
  · intro h
    split at h
    · simp_all
    · simp_all
  · intro h
    simp_all

lemma List.helper_min_mem {n : ℕ} (l : List (Fin n)) :
  ∀(current_min : (Fin n)),
  l.helper_min current_min = current_min ∨ l.helper_min current_min ∈ l := by
  induction l with
  | nil => unfold helper_min ; simp_all
  | cons head tail IH =>
    simp_all
    unfold List.helper_min
    intro current_min
    by_cases h_cases : current_min < head
    · simp_all
      specialize IH current_min
      cases IH
      · simp_all
      · simp_all
    · simp [h_cases]
      specialize IH head
      cases IH
      · simp_all
      · simp_all

@[simp]
lemma List.min_some_membership {n : ℕ} (l : List (Fin n)) (a : Fin n) :
  l.min = some a → a ∈ l := by
  intro h
  induction l with
  | nil =>
    unfold List.min at h
    simp_all
  | cons head tail IH =>
    simp_all
    unfold List.min at h
    simp at h
    have h_helper := List.helper_min_mem tail head
    simp_all

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
-- Bland's Rule: choose the lowest-numbered nonbasic column with a positive cost
noncomputable def find_entering_variable {m n : ℕ} (t : Tableau m n)
  : Option (Fin n) :=
  ((Finset.univ.image t.N).filter (fun x => t.c x > 0)).min

-- A leaving variable should have the minimum positive
-- ratio in the ratio test.
-- h_ratio : ∀ i : Fin m, t.A i enter > 0
--         → t.b r / t.A r enter ≤ t.b i / t.A i enter)
-- Should be in B
noncomputable def find_leaving_variable {m n : ℕ} (t : Tableau m n) (enter : Fin n)
      : Option (Fin m) :=
  let candidates := (Finset.univ).filter (fun x : Fin m => (t.b x) / (t.A x enter) > 0)
  candidates.toList.find_argmin (fun x : Fin m => (t.b x) / (t.A x enter))

noncomputable def leavingCandidates {m n : ℕ} (t : Tableau m n) (enter : Fin n) :
    List (Fin m × ℝ) :=
  (Finset.univ.filter (fun i => t.A i enter > 0)).toList.map (fun i =>
    (i, t.b i / t.A i enter))

noncomputable def compare {m : ℕ} (cur : Fin m × ℝ) (l : List (Fin m × ℝ)) :=
  match l with
  | [] => cur.fst
  | (index,ratio) :: tail =>
      if ratio < cur.snd then compare (index,ratio) tail
      else if ratio = cur.snd ∧ index < cur.fst then compare (index,ratio) tail
      else compare cur tail

noncomputable def findLeaving {m n : ℕ} (t : Tableau m n) (enter : Fin n)
    : Option (Fin m) :=
  match leavingCandidates t enter with
  | [] => none
  | (i,r) :: rest =>
      some (compare (i,r) rest)



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
  ⟨A', b', c', v', B', N', Visited_Bases', t.Original_LP⟩



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

-- def CanPivot {m n : ℕ} (t : Tableau m n) : Prop :=
--   ∃(h : WellFormed t), (get_pivot_arguments t h).isSome = true

-- def is_pivot_list {m n : ℕ} (l : List (Tableau m n)) : Prop :=
--   match l with
--   | [] => True
--   | head :: tail => match tail with
--     | [] => True
--     | head2 :: tail2 =>
--       is_pivot_list (head2 :: tail2) ∧
--       (∃ (h_wf : WellFormed head) (h : (get_pivot_arguments head h_wf).isSome = true),
--         pivot2 ((get_pivot_arguments head h_wf).get h) = head2)

noncomputable instance {m n} : DecidableEq (Tableau m n) :=
 Classical.decEq _

def piv_list_helper {m n : ℕ} (l : List (Tableau m n)) (t2 : Tableau m n) : Prop :=
  match l with
  | [] => False
  | [val] => val = t2
  | head1 :: head2 :: tail =>
      piv_list_helper (head2 :: tail) t2 ∧
      (∃ (h_wf : WellFormed head1) (h : (get_pivot_arguments head1 h_wf).isSome = true),
        pivot2 ((get_pivot_arguments head1 h_wf).get h) = head2)


def is_pivot_list {m n : ℕ} (l : List (Tableau m n)) (t1 t2 : Tableau m n) : Prop :=
  match l with
  | [] => False
  | head :: _ => head = t1 ∧ piv_list_helper l t2

-- There is some number of pivots from beginning to end
lemma pivot_list {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotedFrom m n t1 t2 → ∃l, is_pivot_list l t1 t2 := by
  intro h
  sorry

def Cycles {m n : ℕ} (t : Tableau m n) : Prop :=
∃l, is_pivot_list l t t



-- Call a variable fickle if it
-- enters or leaves the basis at
-- some point
def Fickle {m n : ℕ}
  (l : List (Tableau m n))
  (t1 t2 : Tableau m n)
  (_ : is_pivot_list l t1 t2)
  (var : Fin n) : Prop :=
  ∃ (i j : Fin (l.length)),
  var ∈ Set.range (l.get i).B ∧ var ∈ Set.range (l.get j).N

def get_fickle_var_largest_index {m n : ℕ}
  (t1 t2 : Tableau m n)
  (l : List (Tableau m n))


-- This must be true bc pivot changes the basis
-- And we must apply pivot at least once
-- So there must be at least one var that switches
-- from basic to nonbasic or vice versa
lemma cycle_implies_fickle {m n : ℕ}
  (t1 t2 : Tableau m n)
  (l : List (Tableau m n))
  (h_eq : t1.B = t2.B)
  (h : is_pivot_list l t1 t2) :
  ∃var, Fickle l t1 t2 h var := by
  unfold Fickle
  unfold is_pivot_list at h
  sorry

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

lemma pivot2_unchanged_og_lp {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t)
  (args : pivot_arguments m n) (h : get_pivot_arguments t h_wf = some args) :
    t.Original_LP = (pivot2 args).Original_LP := by

  unfold pivot2
  simp_all
  rewrite [get_piv_arguments_unchanged_t t h_wf args h]
  simp


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

-- lemma pivoted_from_previous_bases {m n : ℕ} (t1 : Tableau m n) (B : Fin m → Fin n) :
--   B ∈ t1.Visited_Bases → ∃t2, PivotedFrom m n t1 t2 ∧ t2.B = B := by
--   intro h

lemma pivoted_from_basis_subset {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotedFrom m n t1 t2 → t1.Visited_Bases ⊆ t2.Visited_Bases := by
  intro h_piv
  rewrite [Finset.subset_iff]
  intros B hB
  induction h_piv with
  | step args h_wf h_get h_eq =>
    rename_i t3 t4
    rewrite [h_eq]
    unfold pivot2
    simp_all
    unfold get_pivot_arguments at h_get
    split at h_get
    · simp_all
    · split at h_get
      · simp_all
      · rename_i enter2 h_enter2 leaving2 h_leaving2
        simp at h_get
        rewrite [← h_get]
        simp_all
  | trans h12 ih12 h23 ih23 =>
    rename_i t3 t4 t5
    simp_all

lemma pivoted_from_basis_ssubset {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotedFrom m n t1 t2 → t1.Visited_Bases ⊂ t2.Visited_Bases := by

  intro h_piv
  have h_subseteq := pivoted_from_basis_subset t1 t2 h_piv
  apply Finset.ssubset_def.mpr
  simp_all
  apply Finset.not_subset.mpr
  apply Exists.intro t2.B
  sorry

lemma N_different_after_pivot {m n : ℕ}
  (t : Tableau m n)
  (h_wf : WellFormed t)
  (args : pivot_arguments m n)
  (h_args : get_pivot_arguments t h_wf = some args) :
  t.N ≠ (pivot2 args).N := by
    sorry


lemma basis_determines_v {m n : ℕ} (t1 t2 : Tableau m n) :
    PivotedFrom m n t1 t2 → t1.B = t2.B → t1.v = t2.v := by
    intro h_piv h_Beq
    induction h_piv with
    | step args h_wf h_get h_eq =>
      rename_i t3 t4
      -- unfold get_pivot_arguments at h_get
      unfold pivot2 at h_eq
      simp at h_eq
      rewrite [h_eq]
      rewrite [h_eq] at h_Beq
      simp_all
      simp at h_eq
      simp_all

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

lemma x_not_in_N_implies_x_in_B {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t) (x : Fin n) :
  (¬∃ (y : Fin (n - m)), t.N y = x) → (∃p, t.B p = x) := by
  intro h
  unfold WellFormed at h_wf
  obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
  by_contra h_cont
  rewrite [Set.union_def] at B_N_universe
  simp at B_N_universe
  apply Set.eq_univ_iff_forall.mp at B_N_universe
  have contra := B_N_universe x
  simp [h_cont] at contra
  simp_all


lemma N_is_unique {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotedFrom m n t1 t2 → t1.N ≠ t2.N := by
  intro h_piv
  induction h_piv with
  | step args h_wf h_get h_eq =>
    rename_i t3 t4
    rewrite [h_eq]
    unfold pivot2
    simp_all
    rewrite [get_piv_arguments_unchanged_t t3 h_wf args h_get]
    rewrite [← ne_eq]
    symm
    apply Function.update_ne_self_iff.mpr
    rewrite [get_piv_arguments_unchanged_t t3 h_wf args h_get] at *
    have lem : args.t.N args.k = args.t.N args.k := by rfl
    exact x_in_N_implies_x_not_in_B args.t h_wf (args.t.N args.k) args.k lem args.leaving
  | trans h12 ih12 h23 ih23 =>
    rename_i t3 t4 t5
    simp_all




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

-- v := t.v + (t.c enter / t.A r enter) * t.b r
theorem basis_determines_v2 {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotedFrom m n t1 t2 → t1.v ≠ t2.v → t1.B ≠ t2.B := by
  intros h_piv h_v_neq
  have h_bases_subset := pivoted_from_basis_subset t1 t2 h_piv
  induction h_piv with
  | step args h_wf h_get h_eq =>
    rename_i t3 t4
    rewrite [h_eq]
    unfold get_pivot_arguments at h_get
    split at h_get
    · simp_all
    · split at h_get
      · simp_all
      · rename_i enter2 h_enter2 leaving2 h_leaving2
        simp at h_get
        rewrite [← h_get]
        unfold pivot2
        simp_all
        unfold find_leaving_variable at h_leaving2
        simp_all



lemma contrapose_injectivity {α β : Type} (f : α → β) :
  Function.Injective f → (∀ (a1 a2 : α), a1 ≠ a2 → f a1 ≠ f a2) := by
  intro h
  intros a1 a2
  contrapose
  unfold Function.Injective at h
  simp_all
  apply h

lemma pivoted_from_one_step {m n : ℕ} (t : Tableau m n)
    (h_wf : WellFormed t) (args : pivot_arguments m n)
    (h_args : get_pivot_arguments t h_wf = some args) :
    PivotedFrom m n t (pivot2 args) := by

    apply PivotedFrom.step args h_wf h_args
    simp


lemma pivoted_from_implies_pivot {m n : ℕ} (t1 t2 : Tableau m n) --(h_feasible : feasible t)
    (h_wf : WellFormed t1) (args : pivot_arguments m n)
    (h_args : get_pivot_arguments t1 h_wf = some args) :
    PivotedFrom m n t2 t1 → PivotedFrom m n t2 (pivot2 args) := by

    intro h
    have h0 := pivoted_from_one_step t1 h_wf args h_args
    apply PivotedFrom.trans h h0

def Visited_Bases_Invariant {m n : ℕ}
    (t1 : Tableau m n) : Prop :=
  ∀B, B ∈ t1.Visited_Bases → (B = t1.B ∨
  ∃t2, (PivotedFrom m n t2 t1 ∧ t2.B = B))

lemma contrapositive_vb {m n : ℕ} (t1 : Tableau m n)
  (h_vb : Visited_Bases_Invariant t1) :
  ∀B, (∃t2, (¬(PivotedFrom m n t1 t2 ∧ t2.B = B)
  ∧ ¬(B = t1.B)) → B ∉ t1.Visited_Bases) := by
  intro B
  unfold Visited_Bases_Invariant at h_vb
  contrapose h_vb
  simp at h_vb
  simp
  apply Exists.intro B
  constructor
  · specialize h_vb t1
    simp_all
  · constructor
    · specialize h_vb t1
      simp_all
    · intro t3 h
      specialize h_vb t3
      simp_all
      sorry

lemma pivot_accumulates_bases {m n : ℕ} (t : Tableau m n) --(h_feasible : feasible t)

  ∀B, B ∈ t.Visited_Bases → B ∈ (pivot2 args).Visited_Bases := by

  intro B h
  unfold pivot2
  simp
  right
  rewrite [← get_piv_arguments_unchanged_t t h_wf args h_args]
  exact h

lemma pivot_visited_bases {m n : ℕ} (t : Tableau m n) --(h_feasible : feasible t)
    (h_wf : WellFormed t) (args : pivot_arguments m n)
    (h_args : get_pivot_arguments t h_wf = some args) :
    ∀ B ∈ (pivot2 args).Visited_Bases, B = (pivot2 args).B ∨ B ∈ t.Visited_Bases := by

  intro B hB
  unfold pivot2 at *
  simp at *
  cases hB
  · simp_all
  · right
    have h1 := get_piv_arguments_unchanged_t t h_wf args h_args
    simp_all



-- lemma Visited_Bases_Invariant3 {m n : ℕ}
--     (t1 : Tableau m n) :
--   ∀B, B ∈ t1.Visited_Bases → (B = t1.B ∨
--   ∃t2, (PivotedFrom m n t1 t2 ∧ t2.B = B)) := by

--   intro B h


-- lemma Visited_Bases_Invariant2 {m n : ℕ}
--     (t1 : Tableau m n) (h_wf : WellFormed t1) (args : pivot_arguments m n)
--     (h_args : get_pivot_arguments t1 h_wf = some args):
--   ∀B, (∃t2, (¬(PivotedFrom m n t1 t2 ∧ t2.B = B)
--   ∧ ¬(B = t1.B)) → B ∉ t1.Visited_Bases) := by
--   intro B
--   have h1 := pivot_visited_bases t1 h_wf args h_args B
--   apply Exists.intro (pivot2 args)
--   intro h3
--   simp_all
--   by_contra h_contra
--   have h4 := pivot_accumulates_bases t1 h_wf args h_args B h_contra
--   have h5 := h1 h4
--   have h6 := pivoted_from_one_step t1 h_wf args h_args
--   cases h5
--   · rename_i h5

--   have h7 : ¬(pivot2 args).B = B := by



lemma pivot2_preserves_vb_invariant {m n : ℕ} (t : Tableau m n) --(h_feasible : feasible t)
    (h_wf : WellFormed t) (args : pivot_arguments m n)
    (h_args : get_pivot_arguments t h_wf = some args) :
    Visited_Bases_Invariant args.t → Visited_Bases_Invariant (pivot2 args) := by

    intro h
    unfold Visited_Bases_Invariant at *
    intro B
    have h_v := h B
    intro h2
    unfold pivot2 at h2
    simp_all
    -- Here we are splitting on the fact that
    -- B = pivot t B or B was already a visited base in t
    -- This fact comes from the fact that B ∈ pivoted visited bases
    cases h2
    · -- Case current B
      left
      unfold pivot2
      simp
      rename_i h2
      exact h2
    · -- Case old B
      specialize h B
      simp_all
      -- Now we are splitting on the fact that B either is
      -- t.B or a B from a previous pivot. This does not contradict
      -- the case we are in
      cases h
      · -- Case B = t.B
        rename_i h1 h2
        right
        apply Exists.intro args.t
        constructor
        · have h4 : (pivot2 args) = (pivot2 args) := by rfl
          have h5 := PivotedFrom.step args h_wf h_args h4
          rewrite [← get_piv_arguments_unchanged_t t h_wf args h_args]
          exact h5
        · simp_all
        -- left
        -- have h1 := pivot2_unchanged_og_lp t h_wf args h_args
        -- have h2 := get_piv_arguments_unchanged_t t h_wf args h_args
        -- rename_i h3 h4
        -- rewrite [h4]
        -- simp_all
      · -- Case B was from a previous pivot
        rename_i h3 h4
        obtain ⟨t2, h4, h5⟩ := h4
        right
        apply Exists.intro t2
        constructor
        · have h6 := pivoted_from_one_step t h_wf args h_args
          rewrite [← get_piv_arguments_unchanged_t t h_wf args h_args] at h4
          apply PivotedFrom.trans h4 h6
        · exact h5

lemma enter_N_to_B {m n : ℕ} (t : Tableau m n)
  (h_wf : WellFormed t)
  (args : pivot_arguments m n)
  (h_args : get_pivot_arguments t h_wf = some args) :
  ∀x, (∃i, t.N i = x ∧ ∃j, (pivot2 args).B j = x) →
  x = args.entering := by
  intros x h
  contrapose h
  simp_all
  intros i hi j
  rewrite [← hi]
  unfold pivot2
  simp
  unfold Function.update
  by_cases hj : j = args.leaving
  · simp_all
    rewrite [← ne_eq] at *
    symm
    exact h
  · simp_all
    have h2 := x_in_N_implies_x_not_in_B t h_wf x i hi j
    rewrite [← ne_eq]
    rewrite [← get_piv_arguments_unchanged_t t h_wf args h_args]
    exact h2

lemma leaving_B_to_N {m n : ℕ} (t : Tableau m n)
  (h_wf : WellFormed t)
  (args : pivot_arguments m n)
  (h_args : get_pivot_arguments t h_wf = some args) :
  ∀x, (∃i, t.B i = x ∧ ∃j, (pivot2 args).N j = x) →
  x = t.B args.leaving := by
  intros x h
  contrapose h
  simp_all
  intro i hi j
  rewrite [← hi]
  unfold pivot2
  simp
  unfold Function.update
  by_cases hj : j = args.k
  · simp_all
    rewrite [← ne_eq] at *
    symm
    rewrite [← get_piv_arguments_unchanged_t t h_wf args h_args] at *
    exact h
  · simp_all
    by_contra h_contra
    rewrite [← get_piv_arguments_unchanged_t t h_wf args h_args] at *
    have h2 := x_in_N_implies_x_not_in_B t h_wf x j h_contra i
    simp_all

lemma c_zero_implies_in_B {m n : ℕ} (t : Tableau m n)
  (h_wf : WellFormed t) : ∀x, t.c x = 0 → x ∈ Set.range t.B := by
  intros x h
  unfold WellFormed at h_wf
  obtain ⟨h_b_inj, h_n_inj, h_univ, h_disjoint, h_nm, h_rangeN⟩ := h_wf
  contrapose h
  by_contra h_contra
  specialize h_rangeN x
  obtain ⟨h1, h2⟩ := h_rangeN
  have h_x_in_N : x ∈ Set.range t.N := by
    by_contra h3
    have h4 := (Set.mem_union x (Set.range t.B) (Set.range t.N)).mp
    have h5 : x ∈ Set.univ := by simp
    rewrite [← h_univ] at h5
    apply h4 at h5
    simp_all
  apply h2 at h_x_in_N
  simp_all

theorem pivot2_preserves_well_formedness {m n : ℕ}
  (t : Tableau m n)
  (h_wf : WellFormed t)
  (args : pivot_arguments m n)
  (h_args : get_pivot_arguments t h_wf = some args) :
  WellFormed (pivot2 args) := by
  have h_t_eq := get_piv_arguments_unchanged_t t h_wf args h_args
  -- unfold WellFormed at *
  -- simp_all
  -- obtain ⟨h_b_inj, h_n_inj, h_univ, h_disjoint, h_nm, h_rangeN⟩ := h_wf
  constructor
  · -- WTS B' is Injective
    unfold pivot2
    simp_all
    unfold Function.Injective at *
    intros a1 a2 h5
    by_cases a1_r_eq : a1 = args.leaving
    · -- case a1 == args.leaving
      simp_all
      by_cases a2_r_eq : a2 = args.leaving
      · symm
        exact a2_r_eq
      · unfold Function.update at h5
        simp_all
        have h_enter_in_N := args.h_enter_in_N
        rewrite [← h_t_eq] at h_enter_in_N
        have disjointness_lemma :=
          x_in_N_implies_x_not_in_B t h_wf args.entering args.k h_enter_in_N a2
        simp_all
    · -- case a1 ≠ args.leaving
      by_cases a2_r_eq : a2 = args.leaving
      · simp_all
        unfold Function.update at h5
        simp_all
        have h_enter_in_N := args.h_enter_in_N
        rewrite [← h_t_eq] at h_enter_in_N
        have disjointness_lemma :=
          x_in_N_implies_x_not_in_B t h_wf args.entering args.k h_enter_in_N a1
        simp_all
      · unfold Function.update at h5
        simp_all
        obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
        unfold Function.Injective at B_inj
        rewrite [← h_t_eq] at h5
        apply B_inj at h5
        exact h5
  · constructor
    · -- WTS N' is injective
      unfold pivot2
      simp_all
      unfold Function.Injective at *
      intros a1 a2 h5
      by_cases a1_r_eq : a1 = args.k
      · -- case a1 == k
        simp_all
        by_cases a2_r_eq : a2 = args.k
        · symm
          exact a2_r_eq
        · unfold Function.update at h5
          simp_all
          have lem : t.N a2 = t.N a2 := by rfl
          have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf (t.N a2) a2 lem args.leaving
          rewrite [← h_t_eq] at h5
          simp_all
      · -- case a1 ≠ k
        by_cases a2_r_eq : a2 = args.k
        · simp_all
          unfold Function.update at h5
          simp_all
          have lem : t.N a1 = t.N a1 := by rfl
          have disjointness_lemma := x_in_N_implies_x_not_in_B t h_wf (t.N a1) a1 lem args.leaving
          simp_all
        · unfold Function.update at h5
          simp_all
          obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
          unfold Function.Injective at N_inj
          rewrite [← h_t_eq] at h5
          apply N_inj at h5
          exact h5
    · constructor
      · -- WTS N' ∪ B' = universe
        unfold pivot2
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
          by_cases p_is_r : p = args.leaving
          · -- case x == t.B r, need y = k
            right
            apply Exists.intro args.k
            simp_all
          · left
            apply Exists.intro p
            simp_all
        · -- case x ∈ N
          have x_in_N := x_not_in_B_implies_x_in_N t h_wf x x_in_B
          obtain ⟨p,x_in_N⟩ := x_in_N
          by_cases x_is_enter : x = args.entering
          · -- case x == enter
            left
            apply Exists.intro args.leaving
            simp_all
          · right
            -- need to find a y ≠ k
            apply Exists.intro p
            by_cases p_is_k : p = args.k
            · have h_entering_in_N := args.h_enter_in_N
              simp_all
            · simp_all
      · constructor
        · -- WTS N' ∩ B' = ∅
          unfold pivot2
          simp_all
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro x1
          simp_all
          intros x2 h1 x3
          unfold Function.update
          by_cases x3_is_k : x3 = args.k
          · simp_all
            unfold Function.update at h1
            by_cases x2_is_r : x2 = args.leaving
            · simp_all
              rewrite [← h1]
              have h4 := x_in_N_implies_x_not_in_B t h_wf args.entering args.k
              have h_enter_in_N := args.h_enter_in_N
              rewrite [h_t_eq] at *
              apply h4 at h_enter_in_N
              exact h_enter_in_N args.leaving
            · simp_all
              rewrite [← h1]
              unfold WellFormed at h_wf
              obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
              unfold Function.Injective at B_inj
              rewrite [h_t_eq] at *
              contrapose B_inj
              simp_all
              apply Exists.intro x2
              simp_all
              apply Exists.intro args.leaving
              simp_all
          · simp_all
            unfold Function.update at h1
            by_cases x2_is_r : x2 = args.leaving
            · simp_all
              rewrite [← h1]
              rewrite [← args.h_enter_in_N]
              obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
              have h_N_inj := contrapose_injectivity t.N N_inj x3 args.k
              simp_all
            · simp_all
              rewrite [← h1]
              have h3 := x_in_N_implies_x_not_in_B t h_wf (t.N x3) x3
              simp at h3
              have h4 := h3 x2
              rewrite [← ne_eq] at *
              symm
              rewrite [h_t_eq] at *
              exact h4
        · constructor
          · unfold WellFormed at h_wf
            simp_all
          · intro x
            constructor
            · -- Prove that  ∀ (x : Fin n), (pivot2 args).c x ≠ 0 → x ∈ Set.range (pivot2 args).N

              intro h
              contrapose h
              simp_all
              unfold pivot2
              simp
              unfold get_pivot_arguments at *
              simp_all
              split at h_args
              · simp_all
              · split at h_args
                · simp_all
                · rename_i enter2 h_enter2 leaving2 h_leaving2
                  simp_all
                  rewrite [← h_args] at *
                  simp_all
                  apply sub_eq_zero.mpr
                  unfold find_entering_variable at h_enter2
                  unfold find_leaving_variable at h_leaving2
                  unfold List.find_argmin at *
                  simp_all
                  simp at h_enter2
                  split at h_enter2
                  · simp_all
                  · simp_all
                    rename_i l head tail h_enter
                    have h_enter_c : 0 < args.t.c enter2 := sorry

                    split at h_leaving2
                    · simp_all
                    · simp_all
                      rename_i l2 head2 tail2 h_leaving




              -- have lem : (¬∃ y, (pivot2 args).N y = x) := by simp_all
              -- have h5 := x_not_in_N_implies_x_in_B () h_wf x lem


              intro h
              unfold pivot2
              simp_all
              unfold Function.update
              have h_wf2 := h_wf
              unfold WellFormed at h_wf2
              obtain ⟨h_b_inj, h_n_inj, h_univ, h_disjoint, h_nm, h_rangeN⟩ := h_wf2
              simp_all
              specialize h_rangeN x
              -- unfold pivot2 at h
              -- simp at h
              by_cases h_tc0 : t.c x = 0
              · -- t.c x = 0 so x ∈ B
                -- so x must be the leaving variable
                simp_all
                apply Exists.intro args.k
                simp_all

                by_cases x_is_leaving : x = t.B args.leaving
                · simp_all
                · -- there should be a contradiction here
                  simp_all
                  unfold pivot2 at *
                  unfold get_pivot_arguments at *
                  simp_all
                  split at h_args
                  · simp_all
                  · split at h_args
                    · simp_all
                    · rename_i enter2 h_enter2 leaving2 h_leaving2
                      simp_all
                      rewrite [← h_args] at *
                      simp_all
                      unfold find_leaving_variable at h_leaving2
                      simp_all
                      unfold List.find_argmin at h_leaving2
                      split at h_leaving2
                      · simp_all
                      · simp_all






                have h_x_in_B : ∃ i, args.t.B i = x := by
                  have lem : (¬∃ y, t.N y = x) := by simp_all
                  have h5 := x_not_in_N_implies_x_in_B t h_wf x lem
                  simp_all
                have h_piv_x_in_N : ∃ j, (pivot2 args).N j = x := by
                  unfold pivot2
                  simp
                  unfold Function.update

                have h4 : (∃ i, args.t.B i = x ∧ ∃ j, (pivot2 args).N j = x) := by
                  have lem : (¬∃ y, t.N y = x) := by simp_all
                  have h5 := x_not_in_N_implies_x_in_B t h_wf x lem
                  obtain ⟨i,hi⟩ := h5
                  apply Exists.intro i
                  simp_all
                  unfold pivot2
                  simp
                  unfold Function.update
                  apply Exists.intro args.k
                  simp

                  sorry

                have h_wf2 : WellFormed args.t := by
                  rewrite [h_t_eq] at h_wf
                  simp_all
                have h5 := leaving_B_to_N args.t h_wf2 args h_args x
                simp_all
              · -- case t.c ≠ 0
                -- x ∈ N
                -- (pivot2 args).c x ≠ 0
                -- so x ≠ enter
                obtain ⟨h_N1, h_N2⟩ := h_rangeN
                rewrite [h_t_eq] at *
                simp_all
                obtain ⟨y, hy⟩ := h_N1
                apply Exists.intro y
                simp_all
                intro h3
                have h4 := args.h_enter_in_N
                simp_all
                have h_wf2 : WellFormed args.t := by
                  rewrite [h_t_eq] at h_wf
                  simp_all
                -- unfold pivot2 at h
                -- simp_all
                have h5 : (∃ i, args.t.N i = x ∧ ∃ j, (pivot2 args).B j = x) := by
                  apply Exists.intro args.k
                  simp_all
                  -- have h6 := c_nonzero_implies_in_B t h_wf x
                  sorry

                have h5 := enter_N_to_B args.t h_wf2 args h_args x
                have h5 := leaving_B_to_N args.t h_wf2 args h_args x

                sorry
            · intro h_x_in_N
              unfold pivot2 at *
              simp_all
              obtain ⟨y, h_x_in_N⟩ := h_x_in_N
              unfold Function.update at h_x_in_N
              sorry









                -- have h_args2 := h_args
                -- unfold get_pivot_arguments at h_args
                -- simp at h_args
                -- split at h_args
                -- · simp_all
                -- · simp_all
                  -- split at h_args
                  -- · simp_all
                  -- · simp_all
                    -- rename_i enter2 h_enter2 leaving2 h_leaving2

                    -- rewrite [← h_args]
                    -- simp
                    -- -- rewrite [← h_t_eq] at *
                    -- rename_i h_wf2
                    -- have h4 : (∃ i, args.t.B i = x ∧ ∃ j, (pivot2 args).N j = x) := by

                    -- have h5 := leaving_B_to_N args.t h_wf2 args h_args2 x h4
                    -- rewrite [← h_args] at *
                    -- simp_all


theorem Bland_ensures_no_cycles {m n : ℕ} (t1 : Tableau m n) :
  -- ∀ t2, PivotedFrom m n t1 t2 → t1.B ≠ t2.B
  ∀ t2, PivotedFrom m n t1 t2 → Set.range t1.B ≠ Set.range t2.B := by

  -- For the sake of contradiction, suppose ∃t2 such that
  -- t1 pivots k times to reach t2 and
  -- t1 and t2 have the same basis
  by_contra h_contra
  simp_all
  obtain ⟨t2, h_piv, h_eq_Bases⟩ := h_contra




lemma pivot2_decreases_measure {m n : ℕ}
  (t : Tableau m n)
  (h_wf : WellFormed t)
  (args : pivot_arguments m n)
  (h_args : get_pivot_arguments t h_wf = some args)
  (h_newBase : Function.update args.t.B args.leaving args.entering ∉ t.Visited_Bases) :
    decreasing_measure (pivot2 args)
    < decreasing_measure t := by

  let B' := Function.update args.t.B args.leaving args.entering

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
    specialize h_contra (Function.update args.t.B args.leaving args.entering)
    simp_all

  -- from `C < A` we get `C + 1 ≤ A`
  have hsucc_le : t.Visited_Bases.card + 1 ≤ (all_bases m n).card := Nat.succ_le_of_lt hcard_lt

  unfold decreasing_measure
  unfold pivot2
  simp_all
  apply Nat.sub_lt_sub_left
  · exact hcard_lt
  · rewrite [get_piv_arguments_unchanged_t t h_wf args h_args] at *
    simp_all


-- TODO: starrt here!
noncomputable def pivot2_until_done {m n : ℕ}
  (t : Tableau m n)
  (h_feasible : feasible t)
  (h_wf : WellFormed t)
  (h_vb : Visited_Bases_Invariant t)
  : Tableau m n :=

  match h : get_pivot_arguments t h_wf with
  | none => t
  | some args =>
    have h_wf2 : WellFormed (pivot2 args) := pivot2_preserves_well_formedness t h_wf args h

    have h_newBase : Function.update args.t.B args.leaving args.entering ∉ t.Visited_Bases := by
      unfold Visited_Bases_Invariant at *
      by_contra h_contra
      specialize h_vb (Function.update args.t.B args.leaving args.entering)
      simp_all
      cases h_vb
      · -- here the contradiction is
        -- Function.update args.t.B args.leaving args.entering = t.B
        -- Because args.leaving ≠ args.entering
        rename_i h2
        rewrite [get_piv_arguments_unchanged_t t h_wf args h] at h2
        have h_leaving_eq_entering := Function.update_eq_self_iff.mp h2
        have h_enter_in_N := args.h_enter_in_N
        have h_enter_in_range_N : args.entering ∈ Set.range t.N := sorry
        have h_enter_in_range_B : args.entering ∈ Set.range t.B := sorry
        unfold WellFormed at h_wf
        obtain ⟨_,_,_,h_disjoint,_⟩ := h_wf
        have h_inter : args.entering ∈ Set.range t.B ∩ Set.range t.N := by
          apply (Set.mem_inter_iff args.entering (Set.range t.B) (Set.range t.N)).mpr
          simp_all
        rewrite [h_disjoint] at h_inter
        simp_all
      · -- case t pivoted from t2 where t2 had the same base.
        -- Pivot t has base B' and so does t2
        -- This is a contradiction bc there is no way we
        -- could have checked this base prior. Bland's rule.
        rename_i IH
        obtain ⟨t2, h_t21, h_t22⟩ := IH
        have h_B : (pivot2 args).B =
          Function.update args.t.B args.leaving args.entering := by
            rfl

        have h_piv_from : PivotedFrom m n t2 (pivot2 args) :=
          PivotedFrom.trans h_t21 (pivoted_from_one_step t h_wf args h)
        have h_pivot_list := pivot_list t2 (pivot2 args) h_piv_from
        obtain ⟨cycle_list, h_cycle⟩ := h_pivot_list
        rewrite [← h_B] at h_t22
        have h_fickle := cycle_implies_fickle t2 (pivot2 args) cycle_list h_t22 h_cycle


        -- TODO: 12/10


        have h_piv_improves_objective : t.v > t2.v := sorry
          -- pivoted_from_increases_v t t2 h_feasible
          --   (pivoted_from_preserves_feasibility t t2 h_feasible )
        induction h_t21 with
        | step args2 h_wf2 h_args2 h_piv_eq =>
            rename_i t3 t4
            simp_all
            -- t3 pivoted to t4
            rewrite [← h_piv_eq] at *
            -- t4 pivoted to t






    have h_vb2 : Visited_Bases_Invariant (pivot2 args) := by
      have h0 := get_piv_arguments_unchanged_t t h_wf args h
      rewrite [h0] at h_vb
      exact pivot2_preserves_vb_invariant t h_wf args h h_vb


    pivot2_until_done (pivot2 args) h_wf2 h_vb2
termination_by decreasing_measure t
decreasing_by
  apply pivot2_decreases_measure t h_wf args h h_newBase


noncomputable def Simplex_Algorithm {m n : ℕ}
  (lp : LP m n)
  (h_wflp : WellFormed_LP lp)
  (h_feas : Feasible_LP lp) : ℝ :=

  let t := make_tableau lp h_wflp
  let h_wf := wf_lp_to_tableau lp h_wflp
  let h_vb : Visited_Bases_Invariant (make_tableau lp h_wflp) := by
    unfold Visited_Bases_Invariant
    intro B
    intro h
    left
    unfold make_tableau at h
    simp at h
    unfold make_tableau at *
    simp_all
  let final_tableau := pivot2_until_done t h_wf
  final_tableau.v
