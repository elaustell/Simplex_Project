import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

/-- `CmpOp` Encodes the binary comparison operators ≤, =, ≥
    that an LP constraint can have -/
inductive CmpOp
  | leq
  | eq
  | geq

/-- A constraint in a linear program is of the form
      ∑ᵢ Aᵢxᵢ ⋈ b
    where ⋈ ∈ {≤,=,≥}
-/
structure constraint (n : ℕ) where
  (A : Fin n → ℝ)
  (b : ℝ)
  (ops : CmpOp)

/-- An LP's objective is either `min` or `max` some linear combination of constraints. -/
inductive objective
  | max
  | min

/-- A generic LP is of the form
    min/max c·x
    s.t. some constraints
-/
structure generic_LP (m n : ℕ) where
  (obj : objective)
  (c : Fin n → ℝ)
  (constraints : Fin m → constraint n)

/-- A standard LP is of the form
    max c·x
    s.t. Ax ≤ b
         xᵢ ≥ 0, ∀i
-/
structure standard_LP (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)

/-- An LP after we have added slack variables is of the form
    max c·x
    s.t. Ax = b
         xᵢ ≥ 0, ∀i
-/
structure LP (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)

/-- Returns the set of all inputs to the function `f` that return 0 -/
noncomputable def zeros {n : Type} [Fintype n] (f : n → ℝ) : Finset n :=
  Finset.univ.filter (fun x => f x = 0)

/-- Returns the set of all inputs to the function `f` that do not return 0 -/
noncomputable def nonzeros {n : Type} [Fintype n] (f : n → ℝ) : Finset n :=
  Finset.univ.filter (fun x => f x ≠ 0)

def WellFormed_LP {m n : ℕ} (lp : LP m n) : Prop :=
  (n > m) -- because we have a basic variable per constraint + nonbasic variables
  ∧ (zeros lp.c).toList.length = m -- num basic variables
  ∧ (nonzeros lp.c).toList.length = n-m -- num nonbasic variables

structure Tableau (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)
  (v : ℝ)
  (B : Fin m → Fin n) -- basic variables
  (N : Fin (n-m) → Fin n) -- non-basic variables
  (Visited_Bases : Finset (Fin m → Fin n))

/-- A Tableau is well-formed if B and N partition the variables,
    if there are strictly more variables than constraints, and
    if nonbasic variables have zero coefficients in the objective function
    (and basic variables have nonzero coefficients in the objective function)
-/
def WellFormed {m n : ℕ} (t : Tableau m n) : Prop :=
  Function.Injective t.B ∧
  Function.Injective t.N ∧
  Set.range t.B ∪ Set.range t.N = Set.univ ∧
  Set.range t.B ∩ Set.range t.N = ∅ ∧
  n > m ∧
  (∀x, t.c x ≠ 0 ↔ x ∈ Set.range t.N)


/-- The values in b correspond to the basic feasible solution.
    because every constraint has one basic variable with coefficient 1
    and all others are nonbasic variables set to 0.
-/
def Feasible {m n : ℕ} (t : Tableau m n) : Prop :=
  ∀ i, t.b i ≥ 0

/-- Given a well-formed LP with all equality constraints, identifies the basic variables
    according to which variables have coefficient zero in the objective function.
-/
noncomputable def make_B {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) : Fin m → Fin n :=
  have h : (zeros lp.c).toList.length = m := by
    unfold WellFormed_LP at h_wf
    simp_all
  have h2 : m = (zeros lp.c).toList.length := by
    simp_all
  fun j => (zeros lp.c).toList.get (Fin.cast h2 j)

/-- Given a well-formed LP with all equality constraints, identifies the nonbasic variables
    according to which variables are nonzero in the objective function.
-/
noncomputable def make_N {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) : Fin (n-m) → Fin n :=
  have h : (nonzeros lp.c).toList.length = (n-m) := by
    unfold WellFormed_LP at h_wf
    simp_all
  have h2 : n-m = (nonzeros lp.c).toList.length := by
    simp_all
  fun j => (nonzeros lp.c).toList.get (Fin.cast h2 j)

/-- Given a well-formed LP with all equality constraints, constructs the equivalent Tableau. -/
noncomputable def make_tableau {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) : Tableau m n :=
  ⟨lp.A, lp.b, lp.c, 0, make_B lp h_wf, make_N lp h_wf, {make_B lp h_wf}⟩

----------------------------------------------------------------------------------------
/- The following lemmas are used to help prove theorem `wf_lp_to_tableau`
  Many times the Lean standard Library will leave many arguments implicit.
  This causes Lean to sometimes have trouble synthesizing the arguments. Thus
  For several of these lemmas I write a version with explicit inputs in order to
  simplify the proof. -/

/-- A version of Lean's standard library lemma `List.Nodup.get_inj_iff` that makes arguments
    explicit rather than implicit. This helps Lean not to get stuck on the metavariables,
    which kept happening in the proofs.
-/
lemma List.Nodup.get_inj {α : Type} {l : List α} (h : l.Nodup) (i j : Fin l.length) :
    l.get i = l.get j ↔ i = j := by
    apply List.Nodup.get_inj_iff
    simp_all

/-- If `l` has no duplicates, then l[a1] = l[a2] implies a1 = a2. -/
lemma nodup_inj {α : Type} {n : ℕ} (l : List α)
  (h : n = l.length)
  (a1 a2 : Fin n)
  (nodup : l.Nodup)
  (eq : l[Fin.cast h a1] = l[Fin.cast h a2]) :
  a1 = a2 :=
by
  have h2 := (List.Nodup.get_inj nodup)
  have h3 := h2 (Fin.cast h a1) (Fin.cast h a2)
  obtain ⟨h4, h5⟩ := h3
  simp_all

/-- A version of Lean's standard library lemma `List.mem_iff_get` that makes arguments
    explicit rather than implicit. This helps Lean not to get stuck on the metavariables,
    which kept happening in the proofs.
-/
lemma list_mem_explicit {α : Type} (l : List α) (a : α) : a ∈ l ↔ ∃ n, l.get n = a := by
  apply List.mem_iff_get

----------------------------------------------------------------------------------------

/-- Given a well-formed LP with all equality constraints, the function `make_tableau`
    produces a Tableau that is well-formed.
-/
theorem wf_lp_to_tableau {m n : ℕ} (lp : LP m n) (h_wf : WellFormed_LP lp) :
  WellFormed (make_tableau lp h_wf) := by
  unfold WellFormed
  unfold WellFormed_LP at h_wf
  obtain ⟨h1, h2, h3⟩ := h_wf
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

/-- Iterates through `l` and compares each element with the `current_min`,
    keeping the smallest element.
-/
def List.helper_min {n : ℕ} (l : List (Fin n)) (current_min : (Fin n)) : Fin n :=
  match l with
  | [] => current_min
  | head :: tail =>
    if current_min < head
      then tail.helper_min current_min
      else tail.helper_min head

/-- Returns the minimum element of `l`, or `none` if `l` is empty. -/
def List.get_min {n : ℕ} (l : List (Fin n)) : Option (Fin n):=
  match l with
  | [] => none
  | head :: tail => some (tail.helper_min head)

--- The following lemmas will help us verify correctness of `find_entering_variable`---

/-- The function `l.get_min` returns `none` if and only if `l` is empty. -/
@[simp]
lemma List.min_none_iff {n : ℕ} (l : List (Fin n)) : l.get_min = none ↔ l = [] := by
  unfold List.get_min
  constructor
  · intro h
    split at h
    · simp_all
    · simp_all
  · intro h
    simp_all

/-- The function `l.helper_min` either returns the current minimum or a member of `l`. -/
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

/-- If the function `l.get_min` returns something, it must be a member of `l`. -/
@[simp]
lemma List.min_some_membership {n : ℕ} (l : List (Fin n)) (a : Fin n) :
  l.get_min = some a → a ∈ l := by
  intro h
  induction l with
  | nil =>
    unfold List.get_min at h
    simp_all
  | cons head tail IH =>
    simp_all
    unfold List.get_min at h
    simp at h
    have h_helper := List.helper_min_mem tail head
    simp_all
------------------------------------------------------------------------------


/-- We want to find a variable that is in N with a negative coefficient in c.
    Bland's Rule: choose the lowest-numbered nonbasic column with a positive cost
-/
noncomputable def find_entering_variable {m n : ℕ} (t : Tableau m n)
  : Option (Fin n) :=
  ((Finset.univ.image t.N).filter (fun x => t.c x > 0)).toList.get_min

/-- When finding a leaving variable, we only want to consider
    variables in B with a positive ratio. Since each constraint
    corresponds to a row in the tableau, which also corresponds
    to a basic variable (the variable with coefficient 1 that
    makes up the identity matrix), it follows that we simply need
    to compute the leaving variable in terms of the row of A.
-/
noncomputable def leavingCandidates {m n : ℕ} (t : Tableau m n) (enter : Fin n) :
    List (Fin m × ℝ) :=
  (Finset.univ.filter (fun i => t.b i / t.A i enter > 0)).toList.map (fun i =>
    (i, t.b i / t.A i enter))

/-- Recursively iterates through `l` and finds the pair with the minimum real value,
    breaking ties in favor of the smaller index. `cur` represents the current
    smallest pair in the current step of iteration.
-/
noncomputable def find_leaving_helper {m : ℕ} (cur : Fin m × ℝ) (l : List (Fin m × ℝ)) :=
  match l with
  | [] => cur.fst
  | (index,ratio) :: tail =>
      if ratio < cur.snd then find_leaving_helper (index,ratio) tail
      else if ratio = cur.snd ∧ index < cur.fst then find_leaving_helper (index,ratio) tail
      else find_leaving_helper cur tail

/-- Returns the index `i` of the smallest positive ratio t.b i / t.A i enter,
    breaking ties in favor of the smaller index, or `none` if no such ratio exists.
-/
noncomputable def find_leaving_variable {m n : ℕ} (t : Tableau m n) (enter : Fin n)
    : Option (Fin m) :=
  match leavingCandidates t enter with
  | [] => none
  | (i,r) :: rest =>
      some (find_leaving_helper (i,r) rest)

/-- A datatype for bundling together all arguments to the `pivot` function
-/
structure pivot_arguments (m n : ℕ) where
  t : Tableau m n
  entering : Fin n
  leaving : Fin m
  k : Fin (n - m)
  h_enter_in_N : t.N k = entering
  h_c_pos : t.c entering > 0
  new_basis : Function.update t.B leaving entering ∉ t.Visited_Bases

/-- Verifies that if `find_entering_variable` returns an entering variable,
    then that variable must have positive coefficient in the objective function
-/
lemma enter_var_pos_coefficient {m n : ℕ} (t : Tableau m n) (enter : Fin n) :
  (find_entering_variable t) = some enter → t.c enter > 0 := by
  intro h
  unfold find_entering_variable at h
  have h1 := List.min_some_membership {x ∈ Finset.image t.N Finset.univ | t.c x > 0}.toList enter h
  simp_all

/-- Verifies that if there is a variable with positive coefficient in the objective function,
  find_entering_variable will return that variable and ensure that it is in N.
-/
lemma entering_in_N {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t) :
  (∃x, t.c x > 0) → ∃k, t.N k = find_entering_variable t := by
  intro h
  unfold find_entering_variable
  simp_all
  unfold List.get_min
  obtain ⟨x,h⟩ := h
  unfold WellFormed at h_wf
  obtain ⟨_,_,_,_,_,h2⟩ := h_wf
  split
  · rename_i l h_contra
    have h1 : x ∈ {x ∈ Finset.image t.N Finset.univ | t.c x > 0} := by
      simp
      have h3 := (h2 x).mp
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
    have h3 := List.helper_min_mem tail head
    cases h3
    · rename_i h_case
      rewrite [h_case]
      simp_all
      have h4 : head ∈ {x ∈ Finset.image t.N Finset.univ | 0 < t.c x} := by
        apply Finset.mem_toList.mp
        simp_all
      have h5 : head ∈ Finset.image t.N Finset.univ := by simp_all
      simp at h5
      simp_all
    · rename_i h_case
      have h4 : tail.helper_min head ∈ {x ∈ Finset.image t.N Finset.univ | 0 < t.c x} := by
        apply Finset.mem_toList.mp
        simp_all
      have h5 : tail.helper_min head ∈ Finset.image t.N Finset.univ := by simp_all
      simp at h5
      simp_all

/-- Given a Tableau `t` and a proof `h_wf` that `t` is well-formed,
  returns all necessary arguments to `pivot` if entering / leaving variables
  exist and `none` otherwise.
-/
noncomputable def get_pivot_arguments {m n : ℕ} (t : Tableau m n)
              (h_wf : WellFormed t) : Option (pivot_arguments m n) :=
  match h : (find_entering_variable t) with
  | none => none
  | some enter =>
    match h2 : (find_leaving_variable t enter) with
    | none => none
    | some leaving =>
        have h_c_pos : ∃ x, t.c x > 0 := by
          apply Exists.intro enter
          simp_all
          apply (enter_var_pos_coefficient t enter h)
        have h_enter_in_N := entering_in_N t h_wf h_c_pos
        have N_k_is_enter : t.N (Classical.choose h_enter_in_N) = enter := by
          have h1 := Classical.choose_spec h_enter_in_N
          simp_all
        have t_c_positive : t.c enter > 0 := by
          have h2 := enter_var_pos_coefficient t enter
          simp_all
        have h_new_base : Function.update t.B leaving enter ∉ t.Visited_Bases := by
          sorry

        some {
          t := t
          entering := enter
          leaving := leaving
          k := (Classical.choose h_enter_in_N)
          h_enter_in_N := N_k_is_enter
          h_c_pos := t_c_positive
          new_basis := h_new_base
        }

/-- Brings `args.leaving` out of the basis and replaces it with `args.entering`. -/
noncomputable def pivot {m n : ℕ} (args : pivot_arguments m n)
  : Tableau m n :=

  let t := args.t
  let l := args.leaving
  let e := args.entering
  let k := args.k

  let piv := t.A l e
  let oldB := t.B l

  let A' := fun i j => if i = l then t.A l j / piv else t.A i j - (t.A i e / piv) * t.A l j
  let b' := fun i => if i = l then t.b i / piv else t.b i - (t.A i e / piv) * t.b l
  let c' := fun j => t.c j - (t.c e / piv) * t.A l j

  let v' := t.v + (t.c e / piv) * t.b l
  let B' := Function.update t.B l e
  let N' := Function.update t.N k oldB
  let Visited_Bases' := t.Visited_Bases.cons B' args.new_basis

  ⟨A', b', c', v', B', N', Visited_Bases'⟩

-------- The following lemmas will be used to prove the correctness of `pivot` -----------

/-- If `x` is a nonbasic variable, then it cannot be a basic variable. -/
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

/-- If `x` is not a basic variable, it must be a nonbasic variable. -/
lemma x_not_in_B_implies_x_in_N {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t) (x : Fin n) :
  (¬∃ (y : Fin m), t.B y = x) → (∃p, t.N p = x) := by
  intro h
  unfold WellFormed at h_wf
  obtain ⟨B_inj, N_inj, B_N_universe, B_N_disjoint⟩ := h_wf
  -- B_N_universe is the key here
  by_contra h_cont
  rewrite [Set.union_def] at B_N_universe
  simp at B_N_universe
  apply Set.eq_univ_iff_forall.mp at B_N_universe
  have contra := B_N_universe x
  simp [h_cont] at contra
  simp_all

/-- The function `find_leaving_helper` returns either the current element or something in `l`. -/
lemma find_leaving_helper_mem {m : ℕ} (l : List (Fin m × ℝ)) :
  ∀ (cur : Fin m × ℝ),
  find_leaving_helper cur l = cur.fst
  ∨ ∃v, ((find_leaving_helper cur l),v) ∈ l := by
  induction l with
  | nil =>
    unfold find_leaving_helper
    simp
  | cons head tail IH =>
    intro curr
    unfold find_leaving_helper
    simp_all
    by_cases h_cases : head.2<curr.2
    · simp_all
      specialize IH head.1 head.2
      cases IH
      · right
        apply Exists.intro head.2
        simp_all
      · rename_i IH
        obtain ⟨v, hv⟩ := IH
        right
        apply Exists.intro v
        simp_all
    · simp [h_cases]
      by_cases h_case2 : head.2 = curr.2
      · simp_all
        by_cases h_case3 : head.1 < curr.1
        · simp_all
          specialize IH head.1 curr.2
          cases IH
          · right
            apply Exists.intro head.2
            simp_all
            rewrite [← h_case2]
            simp
          · rename_i IH
            obtain ⟨v, hv⟩ := IH
            right
            apply Exists.intro v
            simp_all
        · simp [h_case3]
          specialize IH curr.1 curr.2
          cases IH
          · left
            simp_all
          · rename_i IH
            obtain ⟨v, hv⟩ := IH
            right
            apply Exists.intro v
            simp_all
      · -- head.s > curr.2
        simp_all
        specialize IH curr.1 curr.2
        cases IH
        · simp_all
        · simp_all
          rename_i IH
          obtain ⟨v, hv⟩ := IH
          right
          apply Exists.intro v
          simp_all

/-- If `get_pivot_args` returns `some`, then `t` must have an entering variable. -/
lemma pivot_args_some_implies_entering_some {m n : ℕ} (t : Tableau m n) (h_wf : WellFormed t) :
  (get_pivot_arguments t h_wf).isSome = true → (find_entering_variable t).isSome = true := by
  simp [get_pivot_arguments]
  split
  · simp
  · split
    · simp
    · simp_all

/-- If `get_pivot_args` returns `some`, then `t` must have a leaving variable. -/
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

/-- The tableau in the structure returned by `get_pivot_arguments` with input `t`
    is itself (`t`). This helps with rewrites where we have a hypothesis that refers to
    `args.t` but a goal that refers to `t`, or vice versa.
-/
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

/-- If a tableau `t` has a leaving variable, that variable will have a positive ratio
    between its right hand side and its coefficient in the entering variable's column.
-/
lemma piv_in_candidates {m n : ℕ} (t : Tableau m n) (enter : Fin n) (leaving : Fin m)
      (h_leaving : find_leaving_variable t enter = some leaving) :
  leaving ∈ (Finset.univ).filter (fun x : Fin m => (t.b x) / (t.A x enter) > 0) := by

  unfold find_leaving_variable at h_leaving
  unfold leavingCandidates at h_leaving
  split at h_leaving
  · simp_all
  · simp_all
    rename_i l index head tail h
    have h1 := find_leaving_helper_mem tail (index,head)
    cases h1
    · simp_all
      have h1 : (index, head) ∈ List.map (fun i ↦ (i, t.b i / t.A i enter))
                ({i | 0 < t.b i / t.A i enter} : Finset (Fin m)).toList := by
        simp_all
      have h2 : leaving ∈ ({i | 0 < t.b i / t.A i enter} : Finset (Fin m)).toList := by
        apply List.mem_map.mp at h1
        obtain ⟨a, ha,h1⟩ := h1
        rewrite [← h_leaving]
        simp_all
      simp_all
    · rename_i h2
      obtain ⟨v,h2⟩ := h2
      rewrite [h_leaving] at h2
      have h1 : (leaving,v) ∈ List.map (fun i ↦ (i, t.b i / t.A i enter))
                ({i | 0 < t.b i / t.A i enter} : Finset (Fin m)).toList := by
        simp_all
      have h2 : leaving ∈ ({i | 0 < t.b i / t.A i enter} : Finset (Fin m)).toList := by
        apply List.mem_map.mp at h1
        obtain ⟨a, ha,h1⟩ := h1
        rewrite [← h_leaving]
        simp_all
      simp_all

/-- The pivot element of a Tableau (the intersection of the entering and leaving variables
    in the Tableau) must be positive.
-/
lemma piv_positive {m n : ℕ} (t : Tableau m n)
    (h_feasible : Feasible t) (enter : Fin n) (leaving : Fin m)
    (h_leaving : find_leaving_variable t enter = some leaving) :
  0 < t.A leaving enter := by

  have h_mem := piv_in_candidates t enter leaving h_leaving
  simp_all
  unfold Feasible at h_feasible
  by_contra h_contra
  simp_all
  have h3 := h_feasible leaving
  have h4 := div_nonpos_of_nonneg_of_nonpos h3 h_contra
  have h5 : ¬(t.b leaving / t.A leaving enter > 0) := by
    apply not_lt_of_ge
    exact h4
  simp_all

/-- The ratio between the RHS of the leaving variable's constraint and the pivot element
    must be positive.
-/
lemma leaving_ratio_positive {m n : ℕ} (t : Tableau m n) (enter : Fin n) (leaving : Fin m)
      (h_leaving : find_leaving_variable t enter = some leaving) :
  t.b leaving / t.A leaving enter > 0 := by

  have h_mem := piv_in_candidates t enter leaving h_leaving
  simp_all
----------------------------------------------------------------------------------------

/-- If `t` is well-formed and can pivot, the resulting Tableau after pivoting is well-formed. -/
theorem pivot_preserves_well_formedness {m n : ℕ}
  (t : Tableau m n)
  (h_wf : WellFormed t)
  (args : pivot_arguments m n)
  (h_args : get_pivot_arguments t h_wf = some args) :
  WellFormed (pivot args) := by
  have h_t_eq := get_piv_arguments_unchanged_t t h_wf args h_args
  constructor
  · -- Goal: B' is Injective
    unfold pivot
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
    · -- Goal: N' is injective
      unfold pivot
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
      · -- Goal: N' ∪ B' = universe
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
        · -- Goal: N' ∩ B' = ∅
          unfold pivot
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
              have contrapose_injectivity : ∀ {α β : Type} (f : α → β),
                Function.Injective f → (∀ (a1 a2 : α), a1 ≠ a2 → f a1 ≠ f a2) := by
                intro α β f h
                intros a1 a2
                contrapose
                unfold Function.Injective at h
                simp_all
                apply h
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
            · -- Goal: ∀ (x : Fin n), (pivot2 args).c x ≠ 0 → x ∈ Set.range (pivot2 args).N
              intro h
              contrapose h
              simp_all
              unfold pivot
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
                  have h_enter_copy := h_enter2
                  unfold find_entering_variable at h_enter2
                  unfold find_leaving_variable at h_leaving2
                  unfold find_leaving_helper at *
                  simp_all
                  unfold List.get_min at h_enter2
                  simp at h_enter2
                  split at h_enter2
                  · simp_all
                  · simp_all
                    rename_i l head tail h_enter
                    have h_enter_c : 0 < args.t.c enter2 :=
                      enter_var_pos_coefficient args.t enter2 h_enter_copy
                    split at h_leaving2
                    · simp_all
                    · /- Proof sketch:
                      From h we know that x ∉ N, and thus by h_wf, it follows that x ∈ B
                      So t.c x = 0, because this is true for all basic variables
                      Additionally, the columns of A that correspond to variables in the basis
                      form the identity matrix, with the 1 in the row that corresponds to the same
                      basic variable. Thus if x is not the leaving variable (t.B leaving ≠ x), then
                      args.t.A leaving x = 0. Since both sides are equal to zero,
                      the inequality holds.
                      -/
                      sorry
            · intro h
              unfold pivot
              simp_all
              sorry

/-- Pivoting a tableau `t` strictly increases its objective value `v`. -/
theorem pivot_improves_objective {m n : ℕ} (t : Tableau m n) (h_feasible : Feasible t)
    (h_wf : WellFormed t) (args : pivot_arguments m n)
    (h_args : get_pivot_arguments t h_wf = some args) :
    (pivot args).v > args.t.v := by
  unfold pivot
  simp_all
  have h_enter_in_N := args.h_enter_in_N
  have h_c_pos := args.h_c_pos
  have h_unchanged_t := get_piv_arguments_unchanged_t t h_wf args h_args
  have args_feasible : Feasible args.t := by simp_all
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


---------- Recursion and Termination ------------

/-- All bases a Tableau could visit based on its dimensions. -/
def all_bases (m n : ℕ) : Finset (Fin m → Fin n) := Finset.univ

/-- The number of bases `t` has not yet visited.
-/
def decreasing_measure {m n : ℕ} (t : Tableau m n) : Nat :=
  (all_bases m n).card - t.Visited_Bases.card

/-- A call to `pivot` strictly decreases the number of bases not yet visited by the Tableau. -/
lemma pivot_decreases_measure {m n : ℕ}
  (t : Tableau m n)
  (h_wf : WellFormed t)
  (args : pivot_arguments m n)
  (h_args : get_pivot_arguments t h_wf = some args)
    : decreasing_measure (pivot args)
    < decreasing_measure t := by
  let B' := Function.update args.t.B args.leaving args.entering

  have hB' : B' ∈ all_bases m n := by
    unfold all_bases
    simp_all
  have h_newBase : Function.update args.t.B args.leaving args.entering ∉ t.Visited_Bases := by
    rewrite [get_piv_arguments_unchanged_t t h_wf args h_args]
    apply args.new_basis

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
  unfold pivot
  simp_all
  apply Nat.sub_lt_sub_left
  · exact hcard_lt
  · rewrite [get_piv_arguments_unchanged_t t h_wf args h_args] at *
    simp_all

/-- Given a well-formed tableau, performs the `pivot` operation
    until no more `entering` or `leaving` variables can be found.
-/
noncomputable def pivot_until_done {m n : ℕ}
  (t : Tableau m n) (h_wf : WellFormed t)
  : Tableau m n :=
  match h : get_pivot_arguments t h_wf with
  | none => t
  | some args =>
    have h_wf2 : WellFormed (pivot args) := pivot_preserves_well_formedness t h_wf args h
    pivot_until_done (pivot args) h_wf2

termination_by decreasing_measure t
decreasing_by
  apply pivot_decreases_measure t h_wf args h

/-- Given a Linear Program with all equality constraints and in the correct form,
    creates the Simplex Tableau, verifies its well-formedness, and then performs the
    pivot operation until termination. It then returns the objective value of the
    tableau after pivoting.
-/
noncomputable def Simplex_Algorithm {m n : ℕ} (lp : LP m n) (h_wflp : WellFormed_LP lp) : ℝ :=
  let t := make_tableau lp h_wflp
  let h_wf := wf_lp_to_tableau lp h_wflp
  let final_t := pivot_until_done t h_wf
  final_t.v

----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------
------------ Unfinished Proofs and infrastructure for future work ----------------------
----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------

/-- `t1` pivots to `t2` if either `t1` pivots directly to `t2` in one step
    or if there exists some tableau `ti` such that `t1` pivots to `ti` and
    `ti` pivots to `t2`.
-/
inductive PivotsTo (m n : ℕ) :
    Tableau m n → Tableau m n → Prop
| step :
    ∀ {t t'} (args : pivot_arguments m n)
      (h_wf : WellFormed t),
      get_pivot_arguments t h_wf = some args →
      t' = pivot args →
      PivotsTo m n t t'
| trans :
    ∀ {t₁ t₂ t₃},
      PivotsTo m n t₁ t₂ →
      PivotsTo m n t₂ t₃ →
      PivotsTo m n t₁ t₃

/-- If `t1` can pivot to `t2` in some number of steps, then
    `t1` must have been well-formed. This follows from the requirement
    that `t1` is well-formed when we call `pivot`.
-/
lemma pivots_to_preserves_well_formedness {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotsTo m n t1 t2 → WellFormed t1 := by
  intro h
  induction h with
  | step => simp_all
  | trans h12 ih12 h23 ih23 =>
      rename_i t3 t4 t5
      simp_all

/-- Helper lemma for `pivots_to_basis_ssubset`.
    If `t1` can pivot to `t2` in some number of steps, then every base visited by
    `t1` must have also been visited by `t2`.
-/
lemma pivots_to_basis_subset {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotsTo m n t1 t2 → t1.Visited_Bases ⊆ t2.Visited_Bases := by
  intro h_piv
  rewrite [Finset.subset_iff]
  intros B hB
  induction h_piv with
  | step args h_wf h_get h_eq =>
    rename_i t3 t4
    rewrite [h_eq]
    unfold pivot
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

/-- If `t1` can pivot to `t2` in some number of steps, then `t1` must have
    visited strictly fewer bases than `t2`. This should help prove a termination
    argument, since there are finitely many possible bases.
-/
lemma pivots_to_basis_ssubset {m n : ℕ} (t1 t2 : Tableau m n) :
  PivotsTo m n t1 t2 → t1.Visited_Bases ⊂ t2.Visited_Bases := by

  intro h_piv
  have h_subseteq := pivots_to_basis_subset t1 t2 h_piv
  apply Finset.ssubset_def.mpr
  simp_all
  apply Finset.not_subset.mpr
  apply Exists.intro t2.B
  induction h_piv with
  | step args h_wf h_get h_eq =>
    rename_i t3 t4
    constructor
    · unfold pivot at h_eq
      rewrite [h_eq]
      simp
    · unfold pivot at h_eq
      rewrite [h_eq]
      simp
      rewrite [get_piv_arguments_unchanged_t t3 h_wf args h_get]
      exact args.new_basis
  | trans h12 ih12 h23 ih23 =>
    rename_i t3 t4 t5
    have h1 := (pivots_to_basis_subset t3 t4 h12)
    have h2 := (pivots_to_basis_subset t4 t5 ih12)
    have h3 := (pivots_to_basis_subset t3 t5 (PivotsTo.trans h12 ih12))
    simp_all
    by_contra h_contra
    have h_contra2 : t5.B ∈ t4.Visited_Bases := by
      apply Finset.subset_iff.mp at h1
      simp_all
    simp_all

/-- A basic solution for a Tableau sets all variables not in the basis to zero
    and all variables in the basis to the RHS of their corresponding constraint.
-/
def basicSolution {m n : ℕ} (t : Tableau m n) : Fin n → ℝ :=
  fun j =>
    match (List.finRange m).find? (fun i => t.B i = j) with
    | some i => t.b i
    | none   => 0

/-- If `t` is feasible and can pivot, then the resulting tableau after pivoting
    will also be feasible. Note that this theorem is mostly finished, but has
    a few remaining calls to `sorry` and thus is not fully verified.
-/
theorem pivot_preserves_feasibility {m n : ℕ}
  (t : Tableau m n) (h_wf : WellFormed t)
  (h_feasible : Feasible t) (args : pivot_arguments m n)
  (h : get_pivot_arguments t h_wf = some args) :
    Feasible (pivot args) := by

  have h_enter_in_N := args.h_enter_in_N
  have h_leaving : find_leaving_variable t args.entering = some args.leaving := by
    unfold get_pivot_arguments at h
    split at h
    · simp_all
    · split at h
      · simp_all
      · rename_i enter2 h_enter2 leaving2 h_leaving2
        simp at h
        rewrite [← h]
        simp
        exact h_leaving2
  have h_pivot_pos := piv_positive t h_feasible args.entering args.leaving h_leaving
  have h_ratio : ∀ i : Fin m,
    t.A i args.entering > 0 →
    t.b args.leaving / t.A args.leaving args.entering ≤ t.b i / t.A i args.entering := sorry
  have h_c_pos : t.c args.entering > 0 := by
    rewrite [get_piv_arguments_unchanged_t t h_wf args h]
    apply args.h_c_pos
  have h_newBase : Function.update t.B args.leaving args.entering ∉ t.Visited_Bases := sorry

  rewrite [← get_piv_arguments_unchanged_t t h_wf args h] at *

  intro i
  let t' := pivot args
  by_cases hi : i = args.leaving
  · -- leaving row
    rw [hi]
    dsimp [pivot, basicSolution]
    have hr_nonneg : 0 ≤ t.b args.leaving := h_feasible args.leaving
    simp
    rewrite [get_piv_arguments_unchanged_t t h_wf args h] at *
    exact div_nonneg hr_nonneg (le_of_lt h_pivot_pos)
  · -- other rows
    dsimp [pivot, basicSolution]
    let A_i_enter := t.A i args.entering
    let b_i := t.b i
    let b_r := t.b args.leaving
    let piv := t.A args.leaving args.entering
    -- new value: b[i]' = b[i] - (A[i][enter]/piv)*b[r]
    by_cases hA_pos : t.A i args.entering > 0
    -- If A[i,enter] > 0 use ratio test: (b_r / piv) ≤ (b_i / A_i_enter)
    · have ratio := h_ratio i hA_pos
      -- multiply the ratio inequality by A_i_enter > 0:
      -- (A_i_enter / piv) * b_r = A_i_enter * (b_r / piv) ≤ A_i_enter * (b_i / A_i_enter) = b_i
      have h3 : (t.A i args.entering / t.A args.leaving args.entering)
                * t.b args.leaving ≤ t.b i := by
        -- rewrite (A_i_enter / piv) * b_r as A_i_enter * (b_r / piv)
        -- now multiply both sides of ratio by A_i_enter > 0
        have h_temp := mul_le_mul_of_nonneg_left ratio (le_of_lt hA_pos)
        have le_mul : ∀ (a b c : ℝ), 0 < c → a ≤ b → c*a ≤ c*b := by
          intros a b c h1 h2
          simp_all
        have some_linear_arith : ∀ (a b c d : ℝ),
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
        have h_temp3 :=
          (le_mul (t.b args.leaving / t.A args.leaving args.entering)
                  (t.b i / t.A i args.entering)
                  (t.A i args.entering)) hA_pos ratio
        have h_arith := some_linear_arith
          (t.A i args.entering)
          (t.b args.leaving)
          (t.A args.leaving args.entering)
          (t.b i) hA_pos h_temp3
        simp_all
      simp [hi]
      rewrite [get_piv_arguments_unchanged_t t h_wf args h] at *
      simp [h3]

    · -- If A[i,enter] ≤ 0 then (A_i_enter / piv) ≤ 0, so subtracting it
      -- b_i - (A_i_enter/piv)*b_r = b_i + (-(A_i_enter/piv))*b_r which is ≥ 0
      have hdiv_nonpos : A_i_enter / t.A args.leaving args.entering  ≤ 0 := by
        have h3 : A_i_enter ≤ 0 →
          A_i_enter / t.A args.leaving args.entering ≤ 0 / t.A args.leaving args.entering
          := (div_le_div_iff_of_pos_right h_pivot_pos).mpr
        have h4 := le_of_not_gt hA_pos
        apply h3 at h4
        simp_all

      have term_nonneg : 0 ≤ -(t.A i args.entering / t.A args.leaving args.entering)
                             * t.b args.leaving := by
        -- -(A_i_enter / piv) ≥ 0 and b_r ≥ 0, so product ≥ 0
        have : 0 ≤ -(A_i_enter / t.A args.leaving args.entering) := by
          let h1 := neg_le_neg hdiv_nonpos
          rewrite [neg_zero] at h1
          exact h1

        exact mul_nonneg this (h_feasible args.leaving)
      simp_all
      rewrite [get_piv_arguments_unchanged_t t h_wf args h] at *
      exact le_trans term_nonneg (h_feasible i)

/-- If `t1` is feasible and can pivot to `t2` in some number of steps,
    then `t2` must also be feasible. This follows from the proof
    that `pivot_preserves_feasibility`.
-/
lemma pivots_to_preserves_feasibility {m n : ℕ} (t1 t2 : Tableau m n) :
    Feasible t1 → PivotsTo m n t1 t2 → Feasible t2 := by
  intro h1 h2
  induction h2 with
  | step args h_wf h_args h_eq =>
    rename_i t3 t4
    have h3 := pivot_preserves_feasibility t3 h_wf h1 args h_args
    simp_all
  | trans h12 ih12 h23 ih23 =>
      rename_i t3 t4 t5
      simp_all

/-- If `t1` can pivot to `t2` in some number of steps, then the objective value for
    `t2` must be larger than the objective value from `t1`. This follows from the proof
    that `pivot_improves_objective`. This could be helpful in proving a termination
    argument because if `t1` pivots to `t2`, we cannot have that `t2` pivots to `t1`, since
    this would cause a contradiction by this theorem.
-/
theorem pivots_to_increases_v {m n : ℕ}
    (t1 t2 : Tableau m n) (h1_feasible : Feasible t1) (h2_feasible : Feasible t2) :
    PivotsTo m n t1 t2 → (t2.v > t1.v) := by
  intro h
  induction h with
  | step args h_wf h_get h_eq =>
    rename_i t3 t4
    have h_args_isSome : (get_pivot_arguments t3 h_wf).isSome = true := by simp_all
    have h_pivot_increases := pivot_improves_objective t3 h1_feasible h_wf args h_get
    simp_all
    have h_args_t := get_piv_arguments_unchanged_t t3 h_wf args h_get
    simp_all
  | trans h12 ih12 h23 ih23 =>
    rename_i t3 t4 t5
    simp_all
    have h_t3_wf := pivots_to_preserves_well_formedness t3 t4 h12
    have h_t4_feasible := pivots_to_preserves_feasibility t3 t4 h1_feasible h12
    simp_all
    exact lt_trans (h23) (ih23)

/-- Adds a slack variable to the jth constraint by putting a coefficient
    of 1 at the n+jth index and all other variables past n are 0
-/
def add_slack_to_constraint {m n : ℕ} (A_j : Fin n → ℝ) (j : Fin m) : Fin (n+m) → ℝ :=
  fun i => if h : i.val < n then A_j (Fin.castLT i h) else
    if i = (n + j) then 1 else 0

/-- Given an LP in standard form, adds a slack variable to each constraint
    to turn inequalities (≤) into equalities (=).
-/
def add_slack_variables {m n : ℕ} (lp : standard_LP m n) : LP m (n + m) :=
  let c := fun i : Fin (n + m) => if h : i.val < n then lp.c (Fin.castLT i h) else 0
  let b := lp.b
  let A := fun j : Fin m => add_slack_to_constraint (lp.A j) j
  ⟨A,b,c⟩

/-- A solution to a linear program with all equality constraints is feasible if
    the LHS of each constraint = the RHS of each constraint, and all variables are nonnegative.
-/
def solution_is_feasible_LP {m n : ℕ} (lp : LP m n) (x : Fin n → ℝ) : Prop :=
  (∀ (j : Fin m), ∑ i, (lp.A j i * x i) = lp.b j) ∧
  ∀ (i : Fin n), x i ≥ 0

/-- Given a linear program with all equality constraints,
    calculates the value of the objective function at the given solution.
-/
def get_objective_value_LP {m n : ℕ} (lp : LP m n) (solution : Fin n → ℝ) : ℝ :=
  ∑ i, ((lp.c i) * (solution i))

/-- Given a linear program in standard form, calculates the value of the objective function
    at the given solution.
-/
def get_objective_value_standard_LP {m n : ℕ} (lp : standard_LP m n) (solution : Fin n → ℝ) : ℝ :=
  ∑ i, ((lp.c i) * (solution i))

/-- Given a generic LP `lp`, returns an equivalent LP in standard form.

  This definition is not quite correct, because it does not add an extra
  inequality in the reverse direction for case `.eq`. We would like to encode
      ∑ᵢ Aⱼᵢxᵢ = bⱼ ≡ LHS ≤ bⱼ ∧ -LHS ≤ -bⱼ
  but this requires us to add more dimensions to A to encode the extra constraints,
  and it is unclear how to statically determine the dimensions for A depending on
  how many constraints have `op = .eq`.
-/
def make_standard {m n : ℕ} (lp : generic_LP m n) : standard_LP m n :=
  let c := match lp.obj with
    | .min => (fun i => -1 * lp.c i)
    | .max => lp.c
  let b := fun i => (lp.constraints i).b
  let A := fun i : Fin m => fun j => match (lp.constraints i).ops with
    | .leq => (lp.constraints i).A j
    | .eq => (lp.constraints i).A j
    | .geq =>  -1 * ((lp.constraints i).A j)
  ⟨A,b,c⟩

/-- A solution to a linear program in standard form is feasible if the LHS of each constraint
    is ≤ the RHS of each constraint, and all variables are nonnegative.
-/
def solution_is_feasible_standard_LP {m n : ℕ} (lp : standard_LP m n) (x : Fin n → ℝ) : Prop :=
  (∀ (j : Fin m), ∑ i, (lp.A j i * x i) ≤ lp.b j) ∧
  ∀ (i : Fin n), x i ≥ 0

/-- `v` is a feasible objective value for an LP iff `v` is a feasible objective value
    for the LP after adding slack variables.
-/
theorem adding_slack_equivalent_LP {m n : ℕ} : ∀ (lp : standard_LP m n) (v : ℝ),
  (∃x, solution_is_feasible_standard_LP lp x
    ∧ get_objective_value_standard_LP lp x = v)
  ↔
  (∃y, solution_is_feasible_LP (add_slack_variables lp) y
    ∧ get_objective_value_LP (add_slack_variables lp) y = v) := sorry
