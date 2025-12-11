import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic

/- The following lemmas are used to help prove theorem `wf_lp_to_tableau`
  Many times the Lean standard Library will leave many arguments implicit.
  This causes Lean to sometimes have trouble synthesizing the arguments. Thus
  For several of these lemmas I write a version with explicit inputs in order to
  simplify the proof.
-/
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
  have h2 := (List.Nodup.get_inj nodup)
  have h3 := h2 (Fin.cast h a1) (Fin.cast h a2)
  obtain ⟨h4, h5⟩ := h3
  simp_all

lemma list_mem_explicit {α : Type} (l : List α) (a : α) : a ∈ l ↔ ∃ n, l.get n = a := by
  apply List.mem_iff_get
