import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
--import Mathlib/Order/LocallyFinite
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic

structure LabeledType where
  n : ℕ
  V : Type
  labeling : V ≃ Fin (n + 1)

instance (Lt : LabeledType) : Fintype Lt.V :=
  Fintype.ofEquiv (Fin (Lt.n + 1)) Lt.labeling.symm

def LabeledTypeWithoutLastType (Lt : LabeledType) : Type :=
  {v : Lt.V // Lt.labeling v ≠ Fin.last Lt.n}

def subtype_equiv_fin_subtype (Lt : LabeledType) :
  LabeledTypeWithoutLastType Lt ≃ Fin Lt.n :=
  (Lt.labeling.subtypeEquiv (fun _ => by rfl)).trans
  (finSuccAboveEquiv (Fin.last Lt.n)).symm

def LabeledTypeWithoutLast (Lt : LabeledType) (hn : Lt.n ≥ 1) :
  LabeledType := by
  refine {
    n := Lt.n - 1
    V := LabeledTypeWithoutLastType Lt
    labeling := ?_
  }
  simpa [Nat.sub_add_cancel hn] using subtype_equiv_fin_subtype Lt






def upper_vertices (Lt : LabeledType) (k : ℕ) : Finset Lt.V :=
  Finset.filter (λ v => Lt.n - k + 1 ≤ (Lt.labeling v)) Finset.univ

def is_forest_with_roots_in_set (Lt : LabeledType) (G : SimpleGraph Lt.V) (k : ℕ) : Prop :=
  G.IsAcyclic ∧ SimpleGraph.ConnectedComponent.Represents
    (upper_vertices Lt k) (Set.univ : Set G.ConnectedComponent)

def ForestType (Lt : LabeledType) (k : ℕ) : Type :=
   {G : SimpleGraph Lt.V // is_forest_with_roots_in_set Lt G k}

noncomputable instance (Lt : LabeledType) (k : ℕ) : Fintype (ForestType Lt k) := by
  classical
  exact Subtype.fintype (λ G : SimpleGraph Lt.V => is_forest_with_roots_in_set Lt G k)

noncomputable instance (Lt : LabeledType) (G : SimpleGraph Lt.V) : DecidableRel G.Adj :=
  Classical.decRel _








noncomputable def number_of_forests (Lt : LabeledType) (k : ℕ) : ℕ :=
  Fintype.card (ForestType Lt k)

theorem general_cayley :
  ∀ (Lt : LabeledType), ∀ k : ℕ, k ≤ Lt.n + 1 →
    number_of_forests Lt k = k * (Lt.n + 1) ^ ((Lt.n + 1) - 1 - k) := by sorry





def equiv (Lt : LabeledType) (k : ℕ) (hn : Lt.n ≥ 1) (hk : k ≥ 1) :
  ForestType Lt k ≃
  Σ i : Fin (Lt.n - k + 2), Σ N : {s : Finset (Fin (Lt.n - k + 1)) // s.card = i},
  ForestType (LabeledTypeWithoutLast Lt hn) (k - 1 + i) where
  toFun :=
    λ ⟨W, hW⟩ =>
    let n : ℕ := Lt.n
    let v : Lt.V := Lt.labeling.symm (⟨n, by linarith⟩ : Fin (n + 1))
    have hv : v ∈ upper_vertices Lt k := by
        simp [upper_vertices, v, n]
        rw [Nat.add_one_le_iff]
        exact Nat.sub_lt hn hk
    have hvl : Lt.labeling v = n := by simp [v]
    let neighbor_set : Finset Lt.V := W.neighborFinset v

    have hW2 : SimpleGraph.ConnectedComponent.Represents
      (upper_vertices Lt k) (Set.univ : Set W.ConnectedComponent) := hW.2

    have upper_not_reachable : ∀ q : Lt.V, n - k + 1 ≤ Lt.labeling q ∧ Lt.labeling q < n
      → ¬W.Reachable q v := by
      intro q hq
      have hp : q ∈ upper_vertices Lt k := by simp [upper_vertices]; exact hq.1
      rw [Nat.lt_iff_le_and_ne] at hq
      have hn : ¬q = v := by
        apply ne_of_apply_ne Lt.labeling
        simp [v]
        obtain ⟨_, _, hqq⟩ := hq
        exact Fin.ne_of_val_ne hqq
      simp [SimpleGraph.ConnectedComponent.Represents, Set.BijOn] at hW2
      obtain ⟨_, h2, _⟩ := hW2
      simp [Set.InjOn] at h2
      specialize h2 hp hv
      rw [← not_imp_not] at h2
      exact h2 hn

    have ht : ∀ t ∈ neighbor_set, Lt.labeling t ≤ n - k := by
      intro t ht
      have htv : v ≠ t := by
        apply W.ne_of_adj
        exact (SimpleGraph.mem_neighborFinset W v t).mp ht
      subst neighbor_set
      have h : W.Reachable v t := by
        apply SimpleGraph.Adj.reachable
        simp at ht
        exact ht
      specialize upper_not_reachable t
      rw [imp_not_comm] at upper_not_reachable
      rw [SimpleGraph.reachable_comm] at h
      have : ¬(n - k + 1 ≤ ↑(Lt.labeling t) ∧ ↑(Lt.labeling t) < n) := upper_not_reachable h
      simp at this
      rw [le_imp_le_iff_lt_imp_lt] at this
      rw [Nat.lt_add_one_iff] at this
      apply this
      refine Nat.lt_of_le_of_ne ?_ ?_
      · exact Fin.is_le (Lt.labeling t)
      · rw [← hvl]
        by_contra h
        have hc : v = t := by
          apply Lt.labeling.injective
          exact Eq.symm (Fin.eq_of_val_eq h)
        exact htv hc

    let neighbor_set_labels : Finset (Fin (Lt.n - k + 1)) :=
      neighbor_set.attach.image (fun ⟨t, ht_mem⟩ =>
      ⟨Lt.labeling t, Nat.lt_succ_of_le (ht t ht_mem)⟩)

    let i : Fin (Lt.n - k + 2) := ⟨neighbor_set_labels.card, by
      rw [Nat.lt_succ_iff]
      exact card_finset_fin_le neighbor_set_labels⟩

    let new_type : LabeledType := LabeledTypeWithoutLast Lt hn

    let S' : SimpleGraph new_type.V :=
      W.induce {v | Lt.labeling v ≠ Fin.last n}

    --have h : ∀ (c : S'.ConnectedComponent),
    -- SimpleGraph.ConnectedComponent.Represents
    -- (upperVertices (n - 1) k) (Set.univ : Set S'.ConnectedComponent) := by
    -- intro c
    ⟨i, ⟨neighbor_set_labels, rfl⟩, sorry⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

open scoped BigOperators

--instance (n : ℕ) (k : ℕ) (i : ℕ) : Fintype (ForestType (n - 1) (k - 1 + i)) := by sorry
-- instance (n k : ℕ) : Fintype (ForestType n k) := by
--   apply instFintypeSimpleGraphOfDecidableEq

-- lemma helper (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
--   Fintype.card
--     (Σ i : Fin (n - k),
--       Σ N : {s : Finset (Fin (n - k)) // s.card = i},
--         ForestType (n - 1) (k - 1 + i)) =
--   ∑ i : Fin (n - k),
--     Nat.choose (n - k) i * Fintype.card (ForestType (n - 1) (k - 1 + i)) := by sorry
