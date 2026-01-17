import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
--import Mathlib/Order/LocallyFinite
import Mathlib.Tactic.Linarith

--open BigOperators

--old
-- def IsForestWithRootsInSet (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
--   G.IsAcyclic ∧ ∀ (c : G.ConnectedComponent), ∃! r ∈ A, c = G.connectedComponentMk r
def upperVertices (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (λ (x : Fin n) => n - k ≤ x.val)

--old
-- def IsForestWithRootsInSet (n : ℕ) (k : ℕ) (hk : k ≤ n) (G : SimpleGraph (Fin n)) : Prop :=
--   G.IsAcyclic ∧ ∀ (c : G.ConnectedComponent),
--     SimpleGraph.ConnectedComponent.Represents
--     (upperVertices) G.ConnectedComponent
def IsForestWithRootsInSet (n : ℕ) (k : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  G.IsAcyclic ∧ SimpleGraph.ConnectedComponent.Represents
    (upperVertices n k) (Set.univ : Set G.ConnectedComponent)

def ForestType (n : ℕ) (k : ℕ) : Type :=
   {G : SimpleGraph (Fin n) // IsForestWithRootsInSet n k G}

noncomputable def numberOfForests (n : ℕ) (k : ℕ) : ℕ := Nat.card (ForestType n k)

instance (n : ℕ) : Fintype (SimpleGraph (Fin n)) := by infer_instance
noncomputable instance (n : ℕ) (k : ℕ) : Fintype (ForestType n k) := by
  classical
  exact Subtype.fintype (λ G : SimpleGraph (Fin n) => IsForestWithRootsInSet n k G)

noncomputable instance (n : ℕ) (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

--old
-- def ForestType (n : ℕ) (A : Finset (Fin n)) : Type :=
--   {G : SimpleGraph (Fin n) // IsForestWithRootsInSet n G A}

--old
--noncomputable def numberOfForests (n : ℕ) (A : Finset (Fin n)) : ℕ := Nat.card (ForestType n A)

--old
-- def equiv (n : ℕ) (k : ℕ) (hk : k ≥ 2) (A : Finset (Fin n)) (h: A = Finset.Icc (n - k + 1) n) :
--   ForestType n A ≃
--   Σ i : Fin (n - A.card + 1),
--   Σ N : {s : Finset (Fin n - A.card + 1) // s.card = i},
--   ForestType (n - 1) ((removeMin n A (by sorry)) ∪ N) where

--   toFun := equivTreeToFun
--   invFun := equivTreeInvFun
--   left_inv := equivTree_left_inv
--   right_inv := equivTree_right_inv

def equiv (n : ℕ) (k : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) :
  ForestType n k ≃
  Σ i : Fin (n - k + 1), Σ N : {s : Finset (Fin (n - k)) // s.card = i},
  ForestType (n - 1) (k - 1 + i) where
  toFun :=
  λ ⟨W, hW⟩ =>
    let v : Fin n := ⟨n - 1, (by simp; exact hn)⟩
    let neighborSet : Finset (Fin n) := W.neighborFinset v
    let i : ℕ := W.degree v

  --alternative
  -- let S : SimpleGraph (Fin (n - 1)) :=
  -- { Adj := λ i j =>
  --     let i' : Fin n := ⟨i.val, by omega⟩
  --     let j' : Fin n := ⟨j.val, by omega⟩
  --     W.Adj i' j'
  --   symm := λ i j h => W.symm h
  --   loopless := λ i h => W.loopless _ h }
  --let vertex_set : Set (Fin n) := {x | x.val ≤ n - 2}

  let S' : SimpleGraph {x : Fin n // x < n - 1} :=
    W.induce ({x | x < n - 1} : Finset (Fin n))

  let newRoots : Finset {x : Fin n // x < n - 1} := sorry

  have h : ∀ (c : S'.ConnectedComponent),
    SimpleGraph.ConnectedComponent.Represents
    newRoots (Set.univ : Set S'.ConnectedComponent) := by
    intro c


  -- let S : SimpleGraph (Fin (n - 1)) := S'.overFin (by
  --   refine Fintype.card_fin_lt_of_le ?_
  --   exact Nat.sub_le n 1)



  invFun := sorry
  left_inv := sorry
  right_inv := sorry

lemma helper (n : ℕ) (k : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) :
  Fintype.card (ForestType n k) =
    ∑ i : Fin (n - k + 1),
    Nat.choose (n - k) i * Fintype.card (ForestType (n - 1) (k - 1 + i)) := by
  rw [Fintype.card_congr (equiv n k hk hn)]
  simp [Fintype.card_sigma]


--Plan
-- zeige Bijektion, die Bijektion ist es, das kleinste Element α aus A zu löschen,
-- man erhält einen Wald auf n-1 Knoten verwurzelt in k-1+i Knoten
-- Injektivität in die Hinrichtung sollte wie folgt folgen:
-- nehmen wir zwei Wälder, hat α verschiedene
--

-- wegen Bijektion wissen wit
