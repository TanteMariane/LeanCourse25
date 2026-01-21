import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Equiv.Fin.Basic

open Classical SimpleGraph

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
  Finset.filter (λ v => Lt.n + 1 - k ≤ (Lt.labeling v)) Finset.univ

def upper_vertices_card (Lt : LabeledType) (k : ℕ) (hk : k ≤ Lt.n + 1) :
  Finset.card (upper_vertices Lt k) = k := by
    rw [← Fintype.card_coe (upper_vertices Lt k)]
    simp [upper_vertices]
    have he : {v // Lt.n + 1 ≤ (Lt.labeling v).val + k} ≃
      {i : Fin (Lt.n + 1) // Lt.n + 1 - k ≤ i.val} :=
        Lt.labeling.subtypeEquiv (by intro a; simp)
    rw [Fintype.card_congr he]
    let equiv (Lt : LabeledType) (hk : k ≤ Lt.n + 1) :
      {i : Fin (Lt.n + 1) // Lt.n + 1 - k ≤ (i : Nat)} ≃ Fin k := {
        toFun := λ ⟨x, hx⟩ => ⟨x - (Lt.n + 1 - k), by omega⟩
        invFun := λ ⟨x, hx⟩ => ⟨⟨Lt.n + 1 - k + x, by omega⟩, by simp⟩
        left_inv := by intro ⟨x, hx⟩; ext; simp; omega
        right_inv := by intro x; ext; simp }
    rw [Fintype.card_congr (equiv Lt hk)]
    exact Fintype.card_fin k

def is_forest_with_roots_in_set (Lt : LabeledType) (G : SimpleGraph Lt.V) (k : ℕ) : Prop :=
  G.IsAcyclic ∧ ConnectedComponent.Represents
    (upper_vertices Lt k) (Set.univ : Set G.ConnectedComponent)

noncomputable def forest_set (Lt : LabeledType) (k : ℕ) : Finset (SimpleGraph Lt.V) :=
   {G | is_forest_with_roots_in_set Lt G k}

noncomputable def number_of_forests (Lt : LabeledType) (k : ℕ) : ℕ :=
  Finset.card (forest_set Lt k)

noncomputable def sort_by_label (Lt : LabeledType) (s : Finset Lt.V) : List Lt.V :=
  ((s.image Lt.labeling).toList.mergeSort (· ≤ ·)).map Lt.labeling.symm


-- explicit construction
-- noncomputable def label_switch (Lt : LabeledType) (k : ℕ) (hk : k ≥ 1)
--   (neighbor_set : Finset Lt.V) (i : Fin (Lt.n + 3 - k)) :
--   Lt.V ≃ Lt.V :=
--   let sorted_neighbors : List Lt.V := sort_by_label Lt neighbor_set
--   let target_vertices : List Lt.V :=
--     List.ofFn (λ (j : Fin i) => Lt.labeling.symm ⟨Lt.n + 2 + j - i - k, by omega⟩)
--   let perm : Equiv.Perm Lt.V :=
--     List.foldl (λ perm (pair : Lt.V × Lt.V) =>
--       perm * Equiv.swap pair.1 pair.2) 1
--       (List.zip sorted_neighbors target_vertices)
--   perm

-- we dont need explicit as Finset.equivOfCardEq is deterministic
noncomputable def label_switch (Lt : LabeledType)
  (new_roots new_upper: Finset Lt.V) (h : new_roots.card = new_upper.card) :
    new_roots ≃ new_upper := Finset.equivOfCardEq h

noncomputable def label_switch_extended (Lt : LabeledType)
  (new_roots new_upper: Finset Lt.V) (h : new_roots.card = new_upper.card)
    (bij : new_roots ≃ new_upper) : Lt.V ≃ Lt.V :=
    let equiv : Lt.V ≃ Lt.V :=
      calc
      Lt.V ≃ {x // x ∈ new_roots} ⊕ {x // x ∉ new_roots} :=
        Equiv.sumCompl (p := fun x => x ∈ new_roots).symm
      _ ≃ {x // x ∈ new_upper} ⊕ {x // x ∉ new_upper} :=
        bij.sumCongr (Fintype.equivOfCardEq (by simp; rw [h]))
      _ ≃ Lt.V := Equiv.sumCompl (p := fun x => x ∈ new_upper)
    equiv


theorem general_cayley :
  ∀ (Lt : LabeledType), ∀ k : ℕ, k ≤ Lt.n + 1 →
    number_of_forests Lt k = k * (Lt.n + 1) ^ ((Lt.n + 1) - 1 - k) := by sorry

  -- lemma helper (n : ℕ) (k : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) :
  -- Fintype.card (ForestType n k) =
  --   ∑ i : Fin (n - k + 1),
  --   Nat.choose (n - k) i * Fintype.card (ForestType (n - 1) (k - 1 + i)) := by
  -- rw [Fintype.card_congr (equiv n k hk hn)]
  -- simp [Fintype.card_sigma]
