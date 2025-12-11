import Mathlib
open List Finset

/-
  Minimal tableau structure for the primal simplex (standard sign conventions):
  - A : m × n matrix (rows = constraints, cols = variables)
  - b : right-hand side
  - c : reduced cost for each variable (objective row)
  - v : current objective value (unused in the proofs below)
  - B : basic variables (indexing rows → column index in 0..n-1)
  - N : nonbasic variables as an injection Fin (n-m) → Fin n
        (but we just treat them as a Finset via image)
-/
structure Tableau (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  v : ℝ
  B : Fin m → Fin n       -- index of basic var in each row
  N : Fin (n - m) → Fin n -- nonbasic variables enumeration

variable {m n : ℕ} (t : Tableau m n)

-- helpers: minimal element of a nonempty list
noncomputable def helper_find_argmin {n : ℕ}
    (l : List (Fin n)) (f : (Fin n) → ℝ) (current : Fin n) : Fin n :=
  match l with
  | [] => current
  | hd :: tl =>
    if f current < f hd then helper_find_argmin tl f current
    else if f hd < f current then helper_find_argmin tl f hd
    else -- equal values: tie-break by index
      if current < hd then helper_find_argmin tl f current else helper_find_argmin tl f hd

noncomputable def List.find_argmin_fin {k : ℕ} (l : List (Fin k)) (f : Fin k → ℝ) :
    Option (Fin k) :=
  match l with
  | [] => none
  | hd :: tl => some (helper_find_argmin tl f hd)

lemma leaving_break_ties {k : ℕ}
  (l : List (Fin k))
  (f : Fin k → ℝ)
  (leaving : Fin k)
  (h : l.find_argmin_fin f = some leaving) :
  ∀j, j ∈ l → f leaving = f j → leaving ≤ j := by

  intros j hj heq
  unfold List.find_argmin_fin at h
  split at h
  · simp_all
  · rename_i l head tail

-- f a = f b → f ≤ b
-- ((t.b leaving / t.A leaving enter) = (t.b j / t.A j enter) → leaving ≤ j)


lemma helper_find_argmin_returns_min {n : ℕ}
    (l : List (Fin n)) (f : (Fin n) → ℝ) (current : Fin n) :
    ∀k ∈ l, f (helper_find_argmin l f current) ≤ f k := by
    intros k hk
    unfold helper_find_argmin
    induction l with
    | nil => simp_all
    | cons head tail IH =>
      simp_all
      cases hk
      · rename_i k_is_head
        simp_all
        sorry
      · simp_all
        sorry

lemma helper_find_argmin_returns_min_current {n : ℕ}
    (l : List (Fin n)) (f : (Fin n) → ℝ) (current : Fin n) :
    f (helper_find_argmin l f current) ≤ f current := by
    sorry

lemma List.find_argmin_fin_returns_min {k : ℕ}
  (l : List (Fin k))
  (f : Fin k → ℝ)
  (a : Fin k)
  (min : Fin k)
  (h : l.find_argmin_fin f = some min) :
  f min ≤ f a := sorry


lemma helper_leaving_break_ties {k : ℕ}
  (l : List (Fin k))
  (f : Fin k → ℝ)
  (current : Fin k)
  (j : Fin k)
  (hj : j ∈ l)
  (heq : f (helper_find_argmin l f current) = f j) :
  (helper_find_argmin l f current) ≤ j := by
  induction l with
  | nil => simp_all
  | cons head tail IH =>
    simp_all
    cases hj
    · -- Case j = head
      simp_all
      unfold helper_find_argmin at *
      by_cases h_curr_head : f current < f head
      · -- Case f current < f head
        -- impossible because f head is minimum
        simp_all
        rewrite [← heq] at h_curr_head
        have h_min := helper_find_argmin_returns_min_current tail f current
        simp_all
        apply lt_iff_not_ge.mp at h_curr_head
        simp_all
      · sorry -- I think in general the trick is f (argmin) ≤ f a ≤ fb
        -- or whatever. So need some sort of transitivity of leq
        -- TODO

        -- Case f head ≤ f current
        -- this is the true case
        -- by_cases h_head_curr : f head = f current
        -- · -- Case f head = f current
        --   simp_all
        --   by_cases h_cases : current < head
        --   · simp_all
        --     unfold helper_find_argmin

          -- simp [h_head_curr]
          -- simp [h_curr_head]
          -- simp_all
          -- unfold helper_find_argmin at heq
          -- have h_min := helper_find_argmin_returns_min_current tail f head
    · simp_all
      unfold helper_find_argmin
      sorry

  -- TODO : CURRENT



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

lemma List.helper_min_le_tail {n : ℕ} (l : List (Fin n)) (current_min : (Fin n)) :
    ∀a, a ∈ l → l.helper_min current_min ≤ a := by
  intro a ha
  sorry

lemma List.helper_min_le_head {n : ℕ} (l : List (Fin n)) (current_min : (Fin n)) :
    ∀a, a = current_min → l.helper_min current_min ≤ a := by
  intro a ha
  sorry

lemma List.min_le {n : ℕ} (l : List (Fin n)) : ∀a, a ∈ l → l.min ≤ a := by
  intro a ha
  unfold List.min
  induction l with
  | nil => simp_all
  | cons head tail IH =>
    simp_all
    have h_helper1 := List.helper_min_le_tail tail head a
    have h_helper2 := List.helper_min_le_head tail head a
    cases ha
    · simp_all
    · simp_all


/-
  Utility: convert the enumeration of nonbasic vars (t.N) into a List of Fin n,
  ordered by the `Fin`'s usual order (we rely on `Finset.toList` / `List` order arbitrarily,
  but since we tie-break by index in the helper, it's fine).
-/
noncomputable def nonbasicList : List (Fin n) :=
  (Finset.univ.image (t.N)).toList

/-- Bland entering variable: choose smallest-index nonbasic `j` with `t.c j > 0` (if any). -/
noncomputable def find_entering : Option (Fin n) :=
  ((Finset.univ.image (t.N)).filter (fun j => t.c j > 0)).toList.min


/-
  For leaving we need rows i with pivot A i enter > 0, ratio b i / A i enter defined.
  We compute: list of (i : Fin m) with A i enter > 0, then argmin by ratio, tie-breaking by index.
-/
noncomputable def leaving_list (enter : Fin n) : List (Fin m) :=
  (Finset.univ.filter (fun i => t.A i enter > 0)).toList

noncomputable def find_leaving (enter : Fin n) : Option (Fin m) :=
  (Finset.univ.filter (fun i => t.A i enter > 0)).toList.find_argmin_fin
    (fun i => t.b i / t.A i enter)
  -- match (leaving_list t enter) with
  -- | [] => none
  -- | hd :: tl => some (helper_find_argmin tl (fun i => t.b i / t.A i enter) hd)

-- ==== Specifications ====

/-- If `find_entering t = some j`, then `j` is nonbasic, \
    `t.c j > 0`, and is the smallest such index. -/
theorem find_entering_spec
  (entering : Fin n)
  (h : (find_entering t) = some entering) :
  entering ∈ (Finset.univ.image (t.N)) ∧ t.c entering > 0 ∧
  ∀ k, k ∈ (Finset.univ.image (t.N)) → t.c k > 0 → entering ≤ k := by

  constructor
  · -- prove enter ∈ N
    -- should be by construction
    simp_all
    sorry
  · constructor
    · -- prove t.c enter > 0
      -- should be by construction
      sorry
    · intros k hk1 hk2
      have hk3 : k ∈ {j ∈ image t.N univ | 0 < t.c j}.toList := by
            simp
            simp_all
      unfold find_entering at *
      have h_min := List.min_le {j ∈ image t.N univ | t.c j > 0}.toList k hk3
      rewrite [h] at h_min
      simp_all


/-- If `find_leaving t enter = some i`, then A i enter > 0 and i achieves the minimum ratio;
    among equal ratios, `i` is the smallest index (tie-break). -/
theorem find_leaving_spec
  (enter : Fin n) (leaving : Fin m) (h : (find_leaving t enter) = some leaving) :
  t.A leaving enter > 0 ∧
  ∀ j, t.A j enter > 0 → (t.b leaving / t.A leaving enter) ≤ (t.b j / t.A j enter) ∧
    ((t.b leaving / t.A leaving enter) = (t.b j / t.A j enter) → leaving ≤ j) := by
  -- proof sketch / implementable:
  -- By construction `leaving_list` are exactly those rows with positive pivot.
  -- `helper_find_argmin` picks minimal ratio, tie-breaking by `Fin` order.
  -- A full formal proof follows by proving basic lemmas about `helper_find_argmin`.
  constructor
  · -- t.A leaving enter > 0
    -- by construction
    sorry
  · intros j hpos
    constructor
    · unfold find_leaving at h
      have h_helper := List.find_argmin_fin_returns_min
        ({i | t.A i enter > 0} : Finset (Fin m)).toList
        (fun i ↦ t.b i / t.A i enter) j leaving h
      simp_all
    · intro h2
      unfold find_leaving at h
      have hj : j ∈ ({i | t.A i enter > 0} : Finset (Fin m)).toList := by simp_all
      have h_leave_enter : (fun i ↦ t.b i / t.A i enter) leaving
                            = (fun i ↦ t.b i / t.A i enter) j := by
        simp_all
      exact leaving_break_ties ({i | t.A i enter > 0} : Finset (Fin m)).toList
        (fun i ↦ t.b i / t.A i enter) leaving h j hj h_leave_enter



-- ==== Termination statement (no cycling) ====

/-
  Classic Bland termination statement:

  If at each iteration you choose entering/ leaving variable according to Bland's rule,
  then the simplex algorithm cannot cycle: you cannot revisit the same basis twice.
  Equivalently: every pivot strictly decreases the lexicographically-ordered vector of basic indices.

  To formalize:
  - Represent a basis as the vector `B : Fin m → Fin n`. Sort those indices ascending to obtain `bVec`.
  - Define the lexicographic order `lex` on `Vector` or `Fin m → Fin n`.
  - Show that under Bland pivot (entering = smallest nonbasic with negative reduced cost; leaving = among min ratios break ties by smallest index),
    the new basis `B'` is strictly smaller than `B` in `lex` order.
  - `lex` on a finite product of `Fin n` is well-founded, hence no infinite descending chain → no cycles.

  I state the theorem and outline the finishing steps below.
-/

-- assume Mathlib imported and your Tableau and pivot defined as in your message
noncomputable def pivot {m n : ℕ}
  (t : Tableau m n) (enter : Fin n) (r : Fin m) (k : Fin (n - m))
  (_ : t.N k = enter) (_ : t.c enter > 0)
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

variable {m n : ℕ}
variable (t : Tableau m n) (enter : Fin n) (r : Fin m) (k : Fin (n - m))
variable (hN : t.N k = enter) (hce : t.c enter > 0)

-- let t' := pivot t enter r k hN hce
-- let oldB := t.B r
-- let piv := t.A r enter

/-- canonical simplex invariants you must assume for `t` -/
structure simplex_invariants (t : Tableau m n) : Prop where
  (basic_is_id : ∀ i j : Fin m, t.A i (t.B j) = if i = j then 1 else 0)
  (c_basic : ∀ j : Fin m, t.c (t.B j) = 0)
  (B_N_partition : Function.Injective t.B ∧
    Function.Injective t.N ∧
    Set.range t.B ∪ Set.range t.N = Set.univ ∧
    Set.range t.B ∩ Set.range t.N = ∅)

-- immediate fact: the pivot changes basis by updating at row r
theorem pivot_updates_B : (pivot t enter r k hN hce).B = Function.update t.B r enter := by
  rfl -- by definition of your pivot

-- algebraic identity: reduced cost of old basic var after pivot
theorem c_prime_oldB_eq_neg_c_enter (h_inv : simplex_invariants t) :
  (pivot t enter r k hN hce).c (t.B r) = - t.c enter := by
  -- compute c' oldB = t.c oldB - (t.c enter / piv) * t.A r oldB
  -- use h_inv.c_basic to get t.c oldB = 0
  -- use h_inv.basic_is_id to get t.A r oldB = piv

  unfold pivot
  simp
  sorry
  -- calc
  --   (pivot t enter r k hN hce).c (t.B r)
  --     = t.c (t.B r) - (t.c enter / t.A r enter) * t.A r (t.B r) := by rfl -- unfold c' from pivot def
  --   _ = 0 - (t.c enter / t.A r enter) * t.A r enter := by
  --     congr
  --     · exact (h_inv.c_basic r)
  --     · have : t.A r (t.B r) = t.A r enter := by
  --         -- dsimp [(t.B r), t.A r enter];
  --         rw [h_inv.basic_is_id r r];
  --         simp
  --       exact this.symm
  --   _ = - t.c enter := by
  --     -- (t.c enter / piv) * piv = t.c enter
  --     field_simp [piv.ne_zero?] -- you will need a lemma that piv ≠ 0 (pivot must be nonzero)
  --     -- after cancel: 0 - t.c enter = - t.c enter
  --     rfl

-- from that, because t.c enter > 0, we get c' oldB < 0
theorem c_prime_oldB_negative (h_inv : simplex_invariants t) (hpiv : t.A r enter ≠ 0) :
  (pivot t enter r k hN hce).c (t.B r) < 0 := by
  have eq := c_prime_oldB_eq_neg_c_enter t enter r k hN hce h_inv
  rw [eq]
  -- apply pos_of_neg_neg
  -- exact neg_pos.2 hce -- since t.c enter > 0
  sorry

-- lex decrease reduces to enter < oldB
theorem lex_decrease_if_enter_lt_oldB
  (h_update : (pivot t enter r k hN hce).B = Function.update t.B r enter) :
  (enter < t.B r) → lex_lt (pivot t enter r k hN hce).B t.B := by
  intro hlt
  use r
  constructor
  · -- for all i < r, B' i = B i because only row r changed
    intro i hi
    dsimp [t']
    have : (Function.update t.B r enter) i = t.B i := by
      apply Function.update_noteq; intro eq; have := (congrArg (fun (x : Fin m) => (x : Nat)) eq);
      -- finish: i ≠ r because (i : Nat) < (r : Nat)
      sorry
    simpa [h_update] using this
  · -- at r, B' r = enter < oldB = B r
    dsimp [t']
    have : (Function.update t.B r enter) r = enter := by simp [Function.update]
    simp [h_update] at this
    calc
      (pivot t enter r k hN hce).B r = enter := by simp [h_update]; rfl
      _ < oldB := hlt

-- now it remains to prove enter < oldB under Bland selection hypotheses + invariants + pivot nonzero
theorem enter_lt_oldB (h_inv : simplex_invariants t)
  (h_enter_spec : (* find_entering_spec for `enter`: enter minimal nonbasic with t.c > 0 *))
  (h_leave_spec : (* find_leaving_spec for `r` *))
  (hpiv : piv ≠ 0) : enter < oldB := by
  -- sketch: assume ¬(enter < oldB) and derive contradiction using `c' oldB = - t.c enter` and
  -- the minimality from h_enter_spec and the tie-breaking from h_leave_spec.
  sorry


-- Represent a basis (row → basic variable)
def Basis := Fin m → Fin n

/-- Sketch of termination theorem: no repeated basis when pivoting by Bland. -/
theorem bland_no_cycle (start : Tableau m n) :
  -- any sequence of Bland pivots produces only finitely many distinct bases; equivalently cannot cycle.
  True := by
  -- proof sketch:
  -- 1) define a lex ordering on `Basis` by comparing vectors of basic indices in descending order (or ascending).
  -- 2) Show that one Bland pivot strictly decreases that lex order (uses `find_entering_spec` & `find_leaving_spec`).
  -- 3) Since lex on a finite product is well-founded, no infinite descending chain exists.
  -- 4) Thus you cannot revisit a previous basis (would give infinite descent).
  trivial
