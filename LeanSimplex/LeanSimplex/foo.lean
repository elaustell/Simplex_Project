import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

structure Tableau (m n : ℕ) where
  (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ)
  (c : Fin n → ℝ)
  (v : ℝ)
  (B : Fin m → Fin n) -- basic variables
  (N : Fin (n-m) → Fin n) -- non-basic variables
  (Visited_Bases : Finset (Fin m → Fin n))

structure pivot_arguments (m n : ℕ) where
  t : Tableau m n
  entering : Fin n
  leaving : Fin m
  k : Fin (n - m)
  h_enter_in_N : t.N k = entering
  h_c_pos : t.c entering > 0

noncomputable def find_entering_variable {m n : ℕ} (t : Tableau m n)
  : Option (Fin n) := sorry

noncomputable def find_leaving_variable {m n : ℕ} (t : Tableau m n) (enter : Fin n)
      : Option (Fin m) := sorry

noncomputable def get_pivot_arguments {m n : ℕ} (t : Tableau m n) : Option (pivot_arguments m n) :=
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
          sorry
        have h_enter_in_N : ∃ k, some (t.N k) = find_entering_variable t := sorry
        have N_k_is_enter : t.N (Classical.choose h_enter_in_N) = enter := sorry
        have t_c_positive : t.c enter > 0 := sorry
        some {
          t := t
          entering := enter
          leaving := leaving
          k := (Classical.choose h_enter_in_N)
          h_enter_in_N := N_k_is_enter
          h_c_pos := t_c_positive
        }

lemma pivot_args_some_implies_entering_some {m n : ℕ} (t : Tableau m n) :
  (get_pivot_arguments t).isSome = true → (find_entering_variable t).isSome = true := by

  --- CANT GET IT TO WORK
