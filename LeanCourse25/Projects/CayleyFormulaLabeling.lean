import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
--import Mathlib/Order/LocallyFinite
import Mathlib.Tactic.Linarith

structure LabeledGraph (n : ℕ) where
  V : Type
  [fintype : Fintype V]
  [decidable : DecidableEq V]
  labeling : V ≃ Fin n
  graph : SimpleGraph V

attribute [instance] LabeledGraph.fintype LabeledGraph.decidable

def labelOfVertex (n : ℕ) (G : LabeledGraph n) (v : G.V) : Fin n := G.labeling v

def upperVertices (n : ℕ) (G : LabeledGraph n) (k : ℕ) : Finset G.V :=
  Finset.filter (λ v => n - k ≤ (labelOfVertex n G v)) Finset.univ

def IsForestWithRootsInSet (n : ℕ) (k : ℕ) (G : LabeledGraph n) : Prop :=
  G.graph.IsAcyclic ∧ SimpleGraph.ConnectedComponent.Represents
    (upperVertices n G k) (Set.univ : Set G.graph.ConnectedComponent)

def ForestType (n : ℕ) (k : ℕ) : Type 1 :=
  {G : LabeledGraph n // IsForestWithRootsInSet n k G}


noncomputable def numberOfForests (n : ℕ) (k : ℕ) : ℕ :=
  Nat.card (ForestType n k)

def equiv (n : ℕ) (k : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) :
  ForestType n k ≃
  Σ i : Fin (n - k), Σ N : {s : Finset (Fin (n - k)) // s.card = i},
  ForestType (n - 1) (k - 1 + i) where
  toFun :=
    λ ⟨W, hW⟩ =>
    let v : Fin n := ⟨n - 1, (by simp; exact hn)⟩
    let neighborSet : Finset (Fin n) := W.neighborFinset v
    let i : ℕ := W.degree v

    let S' : SimpleGraph {x : Fin n // x < n - 1} :=
    W.induce ({x | x < n - 1} : Finset (Fin n))

    let newRoots : Finset {x : Fin n // x < n - 1} := upperVertices (n - 1) (k - 1)

    have h : ∀ (c : S'.ConnectedComponent),
    -- SimpleGraph.ConnectedComponent.Represents
    -- (upperVertices (n - 1) k) (Set.univ : Set S'.ConnectedComponent) := by
    -- intro c
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

open scoped BigOperators

--instance (n : ℕ) (k : ℕ) (i : ℕ) : Fintype (ForestType (n - 1) (k - 1 + i)) := by sorry
-- instance (n k : ℕ) : Fintype (ForestType n k) := by
--   apply instFintypeSimpleGraphOfDecidableEq

lemma helper (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
  Fintype.card
    (Σ i : Fin (n - k),
      Σ N : {s : Finset (Fin (n - k)) // s.card = i},
        ForestType (n - 1) (k - 1 + i)) =
  ∑ i : Fin (n - k),
    Nat.choose (n - k) i * Fintype.card (ForestType (n - 1) (k - 1 + i)) := by sorry
