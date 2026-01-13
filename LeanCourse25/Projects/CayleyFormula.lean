import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib/Order/LocallyFinite

open BigOperators


def IsForestWithRootsInSet (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  G.IsAcyclic ∧ ∀ (c : G.ConnectedComponent), ∃! r ∈ A, c = G.connectedComponentMk r

def ForestType (n : ℕ) (A : Finset (Fin n)) : Type :=
  {G : SimpleGraph (Fin n) // IsForestWithRootsInSet n G A}

noncomputable def numberOfForests (n : ℕ) (A : Finset (Fin n)) : ℕ := Nat.card (ForestType n A)

def removeMin (n : ℕ) (A : Finset (Fin n)) (h : A.Nonempty) : Finset (Fin n) :=
  A.erase (A.min' h)

def equiv (n : ℕ) (A : Finset (Fin n)) (h: A.card ≥ 2) :
(ForestType n (Finset.Icc (n - A.card + 1) n)) ≃
  Σ i : Fin (n - A.card + 1),
  Σ N : {s : Finset (Fin n - A.card + 1) // s.card = i},
  ForestType (n - 1) ((removeMin n A (by sorry)) ∪ N) where

  toFun := equivTreeToFun
  invFun := equivTreeInvFun
  left_inv := equivTree_left_inv
  right_inv := equivTree_right_inv

--Plan:
-- zeige Bijektion, die Bijektion ist es, das kleinste Element α aus A zu löschen,
-- man erhält einen Wald auf n-1 Knoten verwurzelt in k-1+i Knoten
-- Injektivität in die Hinrichtung sollte wie folgt folgen:
-- nehmen wir zwei Wälder, hat α verschiedene
--

-- wegen Bijektion wissen wit
