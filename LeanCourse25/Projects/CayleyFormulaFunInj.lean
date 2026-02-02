import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Equiv.Fin.Basic
import LeanCourse25.Projects.CayleyFormulaTypes
import LeanCourse25.Projects.CayleyFormulaFun

open Classical SimpleGraph

set_option maxHeartbeats 40000

lemma f_injective (Lt : LabeledType) (k : ℕ) (hn : Lt.n ≥ 1) (hk : k ≥ 1) (hnk : k ≤ Lt.n + 1) :
  Function.Injective (f Lt k hn hk hnk) := by
  let n : ℕ := Lt.n
  intro w1 w2 he
  by_contra hc
  rcases w1 with ⟨s1, hw1⟩
  rcases w2 with ⟨s2, hw2⟩
  unfold forest_set is_forest_with_roots_in_set at hw1 hw2
  simp at hw1 hw2
  simp at hc
  simp only [f, card_neighborFinset_eq_degree, ne_eq, Sigma.mk.injEq, Fin.mk.injEq] at he
  rcases he with ⟨h_degree, h⟩

  let roots : Finset Lt.V := upper_vertices Lt k
  let v : Lt.V := Lt.labeling.symm (⟨n, by omega⟩ : Fin (n + 1))
  let neighbor_set1 : Finset Lt.V := s1.neighborFinset v
  let neighbor_set2 : Finset Lt.V := s2.neighborFinset v

  have : v = Lt.labeling.symm (⟨n, by omega⟩ : Fin (n + 1)) := by rfl

  --rw [← this] at h

  have h_target_eq :
    upper_vertices (LabeledTypeWithoutLast Lt hn) (k - 1 + s1.degree v) =
    upper_vertices (LabeledTypeWithoutLast Lt hn) (k - 1 + s2.degree v) := by
    rw [h_degree]
  --rw [h_target_eq] at h
  --simp [h_target_eq] at h
-- Now your hypothesis becomes more readable
  --h_degree : s1.degree v = s2.degree v
  simp [this, h_degree, is_forest_with_roots_in_set, upper_vertices, forest_set, label_switch, label_switch_extended] at h
  --rw [h_target_eq] at h


  -- have hv : v = Lt.labeling.symm (⟨n, by omega⟩) := rfl
  -- rw [← hv] at h_degree
  -- let deg := s1.degree v
  -- let deg' := s2.degree v
  -- have h_deg : deg = deg' := h_degree
  -- let v : Lt.V := Lt.labeling.symm ⟨Lt.n, by omega⟩
  -- let deg1 := s1.degree v
  -- let deg2 := s2.degree v
  -- have h_deg : deg1 = deg2 := h_degree
  -- let neighbor_set1 := s1.neighborFinset v
  -- let neighbor_set2 := s2.neighborFinset v
  -- subst deg1 deg2
  -- rw [h_deg] at h



  set v := Lt.labeling.symm (⟨Lt.n, by omega⟩ : Fin (n + 1)) at *

  simp [h_degree] at h
