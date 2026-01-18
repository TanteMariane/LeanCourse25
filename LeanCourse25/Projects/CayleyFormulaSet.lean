import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
--import Mathlib/Order/LocallyFinite
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic

open Classical

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
  G.IsAcyclic ∧ SimpleGraph.ConnectedComponent.Represents
    (upper_vertices Lt k) (Set.univ : Set G.ConnectedComponent)

noncomputable def forest_set (Lt : LabeledType) (k : ℕ) : Finset (SimpleGraph Lt.V) :=
   {G | is_forest_with_roots_in_set Lt G k}

-- noncomputable instance (Lt : LabeledType) (k : ℕ) : Fintype (ForestType Lt k) := by
--   exact Subtype.fintype (λ G : SimpleGraph Lt.V => is_forest_with_roots_in_set Lt G k)

-- noncomputable instance (Lt : LabeledType) (G : SimpleGraph Lt.V) : DecidableRel G.Adj :=
--   Classical.decRel _








noncomputable def number_of_forests (Lt : LabeledType) (k : ℕ) : ℕ :=
  Finset.card (forest_set Lt k)

theorem general_cayley :
  ∀ (Lt : LabeledType), ∀ k : ℕ, k ≤ Lt.n + 1 →
    number_of_forests Lt k = k * (Lt.n + 1) ^ ((Lt.n + 1) - 1 - k) := by sorry





def equiv (Lt : LabeledType) (k : ℕ) (hn : Lt.n ≥ 1) (hk : k ≥ 1) (hnk : k ≤ Lt.n + 1) :
  forest_set Lt k ≃
  Σ i : Fin (Lt.n + 2 - k), Σ N : {s : Finset (Fin (Lt.n + 1 - k)) // s.card = i},
  forest_set (LabeledTypeWithoutLast Lt hn) (k - 1 + i) where
  toFun :=
    λ ⟨W, hW⟩ =>
    let n : ℕ := Lt.n
    let roots : Finset Lt.V := upper_vertices Lt k
    let v : Lt.V := Lt.labeling.symm (⟨n, by linarith⟩ : Fin (n + 1))
    have hv : v ∈ roots := by
        simp [roots, v, n, upper_vertices]
        rw [Nat.add_one_le_iff]
        exact hk
    have hvl : Lt.labeling v = n := by simp [v]
    let neighbor_set : Finset Lt.V := W.neighborFinset v

    have hW2 : SimpleGraph.ConnectedComponent.Represents
      roots (Set.univ : Set W.ConnectedComponent) := by
        simp [forest_set, is_forest_with_roots_in_set] at hW
        exact hW.2

    have upper_not_reachable : ∀ q : Lt.V, n + 1 - k ≤ Lt.labeling q ∧ Lt.labeling q < n
      → ¬W.Reachable q v := by
      intro q hq
      have hp : q ∈ roots := by
        unfold roots
        unfold upper_vertices
        rw [@Finset.mem_filter_univ]
        exact hq.1
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

    have ht : ∀ t ∈ neighbor_set, Lt.labeling t < n + 1 - k := by
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
      have : ¬(n + 1 - k ≤ ↑(Lt.labeling t) ∧ ↑(Lt.labeling t) < n) :=
        upper_not_reachable h
      rw [not_and, imp_not_comm, not_le] at this
      apply this
      refine Nat.lt_of_le_of_ne ?_ ?_
      · exact Fin.is_le (Lt.labeling t)
      · rw [← hvl]
        by_contra h
        have hc : v = t := by
          apply Lt.labeling.injective
          exact Eq.symm (Fin.eq_of_val_eq h)
        exact htv hc

    let neighbor_set_labels : Finset (Fin (n + 1 - k)) :=
      neighbor_set.attach.image (fun ⟨t, ht_mem⟩ =>
      ⟨Lt.labeling t, ht t ht_mem⟩)

    have hnn : neighbor_set.card = neighbor_set_labels.card := by
      rw [← neighbor_set.card_attach]
      dsimp [neighbor_set_labels]
      rw [Finset.card_image_of_injective]
      intro ⟨x, hx⟩ ⟨y, hy⟩ h
      ext
      simp at h
      exact Lt.labeling.injective (Fin.eq_of_val_eq h)

    let i : Fin (n + 2 - k) := ⟨neighbor_set.card, by
      rw [hnn]
      have : neighbor_set_labels.card ≤ n + 1 - k := card_finset_fin_le neighbor_set_labels
      omega ⟩

    let Nt : LabeledType := LabeledTypeWithoutLast Lt hn

    let S' : SimpleGraph Nt.V := W.induce {v | Lt.labeling v ≠ Fin.last n}

    have hn_nt : ∀ x ∈ neighbor_set, Lt.labeling x ≠ Fin.last n := by
      intro x hx
      have hr : Lt.labeling x < n + 1 - k := ht x hx
      by_contra h
      have : (Lt.labeling x : ℕ) = n := by simp [h]
      omega

    let old_new_roots : Finset Lt.V := roots \ {v}

    have hr_nt : ∀ x ∈ old_new_roots, Lt.labeling x ≠ Fin.last n := by
      intro x hx
      simp [old_new_roots] at hx
      by_contra h
      have hr : x = v := (Equiv.apply_eq_iff_eq_symm_apply Lt.labeling).mp h
      exact hx.2 hr

    let neighbor_set_Nt : Finset Nt.V :=
      (neighbor_set.attach.map ⟨(fun x => ⟨x.val, hn_nt x.val x.property⟩), by
        intro x y h; cases x; cases y; cases h; rfl⟩)

    let old_roots_Nt : Finset Nt.V :=
      (old_new_roots.attach.map ⟨(fun x => ⟨x.val, hr_nt x.val x.property⟩), by
        intro x y h; cases x; cases y; cases h; rfl⟩)

    let new_roots_Nt : Finset Nt.V := neighbor_set_Nt ∪ old_roots_Nt
    let new_upper_Nt : Finset Nt.V := upper_vertices Nt (k - 1 + i)

    have h_disj : Disjoint neighbor_set_Nt old_roots_Nt := by
      rw [@Finset.disjoint_iff_ne]
      intro a ha b hb
      simp [neighbor_set_Nt] at ha
      simp [old_roots_Nt] at hb
      obtain ⟨a', ha', haa⟩ := ha
      obtain ⟨b', hb', hbb⟩ := hb
      unfold old_new_roots roots upper_vertices at hb'
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_singleton] at hb'
      have hc : Lt.labeling a' < n + 1 - k := ht a' ha'
      rw [← haa, ← hbb]
      by_contra h_eq
      have hab : a' = b' := congr_arg Subtype.val h_eq
      rw [hab] at hc
      omega

    have h_card : new_roots_Nt.card = new_upper_Nt.card := by
      rw [upper_vertices_card Nt (k - 1 + i)
        (by simp [Nt, LabeledTypeWithoutLast]; omega)]
      unfold new_roots_Nt
      have hn : neighbor_set_Nt.card = i := by simp [neighbor_set_Nt]; rfl
      have hs : old_roots_Nt.card = k - 1 := by
        simp [old_roots_Nt, old_new_roots]
        rw [Finset.sdiff_singleton_eq_erase v roots]
        rw [Finset.card_erase_of_mem hv]
        unfold roots
        rw [tsub_left_inj]
        repeat' simp [upper_vertices_card Lt k hnk]
        all_goals exact hk
      rw [Finset.card_union_of_disjoint h_disj]
      rw [hn, hs]
      omega

    let bij : new_roots_Nt ≃ new_upper_Nt := Finset.equivOfCardEq h_card
    --let bijc : Finset.univ \ new_roots_Nt ≃ new_upper_Nt.fintypeCoeSort := by sorry
    let new_roots_Nt_c : Finset Nt.V := Finset.univ \ new_roots_Nt
    let new_upper_Nt_c : Finset Nt.V := Finset.univ \ new_upper_Nt
    have helpp : new_roots_Nt_c.card = new_upper_Nt_c.card := by sorry
      --exact?

    let bijc : new_roots_Nt_c ≃ new_upper_Nt_c := by sorry--exact?

    let extendEquiv : Nt.V ≃ Nt.V :=
      (Equiv.sumCompl s).trans
        ((Equiv.sumCongr f complEquiv).trans
          (Equiv.sumCompl t).symm)

    --have h : ∀ (c : S'.ConnectedComponent),
    -- SimpleGraph.ConnectedComponent.Represents
    -- (upperVertices (n - 1) k) (Set.univ : Set S'.ConnectedComponent) := by
    -- intro c

    ⟨i, ⟨neighbor_set_labels, by rw[← hnn]⟩, sorry⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

open scoped BigOperators
