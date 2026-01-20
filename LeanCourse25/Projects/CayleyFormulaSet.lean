import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic

open Classical SimpleGraph

set_option maxHeartbeats 400000

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

theorem general_cayley :
  ∀ (Lt : LabeledType), ∀ k : ℕ, k ≤ Lt.n + 1 →
    number_of_forests Lt k = k * (Lt.n + 1) ^ ((Lt.n + 1) - 1 - k) := by sorry

noncomputable def equivalence (Lt : LabeledType) (k : ℕ) (hn : Lt.n ≥ 1) (hk : k ≥ 1) (hnk : k ≤ Lt.n + 1) :
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
    have hvl : ∀ i, Lt.labeling i = Fin.last Lt.n ↔ i = v := by
      intro i
      constructor
      · intro hi; exact (Equiv.apply_eq_iff_eq_symm_apply Lt.labeling).mp hi
      · intro hi; rw [hi]; simp [v, Fin.last]; rfl

    let neighbor_set : Finset Lt.V := W.neighborFinset v

    have hW' : W.IsAcyclic ∧ ConnectedComponent.Represents
      roots (Set.univ : Set W.ConnectedComponent) := by
      simp [forest_set, is_forest_with_roots_in_set] at hW
      exact hW

    have h_roots : ∀ ⦃x y : Lt.V⦄, x ∈ roots → y ∈ roots → x ≠ y → ¬W.Reachable x y := by
      intro x y hx hy hne
      by_contra h
      simp [ConnectedComponent.Represents, Set.BijOn, Set.InjOn] at hW'
      exact hne (hW'.2.2.1 hx hy h)

    have hvr : ∀ t ∈ neighbor_set, W.Reachable v t := by
      intro t ht
      apply Adj.reachable
      subst neighbor_set
      simp at ht
      exact ht

    have ht : ∀ t ∈ neighbor_set, Lt.labeling t < n + 1 - k := by
      intro t ht
      have htv : v ≠ t := by
        apply W.ne_of_adj
        exact (mem_neighborFinset W v t).mp ht
      subst neighbor_set
      by_contra hc
      rw [Nat.not_lt] at hc
      have htr : t ∈ roots := by
        unfold roots upper_vertices
        simp
        exact Nat.le_add_of_sub_le hc
      exact h_roots hv htr htv (hvr t ht)

    let neighbor_set_labels : Finset (Fin (n + 1 - k)) :=
      neighbor_set.attach.image (fun ⟨t, ht_mem⟩ => ⟨Lt.labeling t, ht t ht_mem⟩)

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

    let S'_hom_W : S' →g W := {
      toFun := fun v => v.val
      map_rel' := by intro v w h; simpa [S'] using h }

    have S'_hom_W_inj : Function.Injective S'_hom_W := by
      intro v w h
      exact Subtype.ext h

    have rS'_rW (u v : Nt.V) (h : S'.Reachable u v) : W.Reachable u.val v.val := by
      rcases h with ⟨p⟩
      exact ⟨p.map S'_hom_W⟩

    have rW_rS' (e : Lt.V) (d : Lt.V) (p : W.Walk e d)
      (he : Lt.labeling e ≠ Fin.last n) (hd : Lt.labeling d ≠ Fin.last n)
      (hs : ∀ v ∈ p.support, Lt.labeling v ≠ Fin.last n) :
      S'.Reachable ⟨e, he⟩ ⟨d, hd⟩ :=
      ⟨by induction p with
      | nil => exact Walk.nil
      | @cons a b w h p' ih =>
        have ha : Lt.labeling a ≠ Fin.last n := hs a (by simp)
        have hb : Lt.labeling b ≠ Fin.last n := hs b (by simp [Walk.support_cons])
        have h_edge : S'.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by simp [S', SimpleGraph.induce, h]
        have hs' : ∀ x ∈ p'.support, Lt.labeling x ≠ Fin.last n := by
          intro x hx
          apply hs x
          simp [Walk.support_cons, hx]
        exact Walk.cons h_edge (ih hb hd hs')⟩

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
        rw [Finset.sdiff_singleton_eq_erase v roots, Finset.card_erase_of_mem hv]
        unfold roots
        rw [tsub_left_inj]
        repeat' simp [upper_vertices_card Lt k hnk]
        all_goals exact hk
      rw [Finset.card_union_of_disjoint h_disj, hn, hs]
      omega

    have h_cc : ∀ d, ∃ e ∈ new_roots_Nt, S'.Reachable e d := by
      intro d
      let c : W.ConnectedComponent := W.connectedComponentMk d.1
      have hc_univ : c ∈ Set.univ := trivial
      rcases hW'.2.surjOn hc_univ with ⟨e', he', hce'⟩
      have hr : W.Reachable d.1 e' := by simp [c] at hce'; exact Reachable.symm hce'
      by_cases bc : e' ≠ v
      · have he'l : Lt.labeling e' ≠ Fin.last n := by by_contra hc; exact bc ((hvl e').mp hc)
        have he'nor : e' ∈ old_new_roots := by simp [old_new_roots]; exact ⟨he', bc⟩
        let e : Nt.V := ⟨e', he'l⟩
        have he : e ∈ new_roots_Nt :=
          by simp [new_roots_Nt, old_roots_Nt]; right; exact ⟨e', he'nor, rfl⟩
        use e
        constructor
        · exact he
        · rcases Reachable.exists_isPath hr with ⟨p, hp⟩
          have hrs : ∀ i ∈ p.support, Lt.labeling i ≠ Fin.last n := by
            intro i hi
            by_contra hc
            have : i = v := (hvl i).mp hc
            have hrc : W.Reachable e' v := by
              rw [← this]
              exact ⟨SimpleGraph.Walk.takeUntil p.reverse i (by simpa using hi)⟩
            exact (h_roots he' hv bc) hrc
          exact rW_rS' e' d.1 p.reverse he'l d.2 (by simpa using hrs)
      · rw [not_ne_iff] at bc
        subst bc
        have dnv : d.1 ≠ v := by by_contra hc; exact d.2 ((hvl d.1).mpr hc)
        rcases Reachable.exists_isPath hr with ⟨p, hp⟩
        have pn : ¬p.Nil := Walk.not_nil_of_ne dnv
        rcases adj_of_mem_walk_support p pn (Walk.end_mem_support p) with ⟨nv, hnvs, hnv⟩
        have hnv' : nv ∈ neighbor_set := by simpa [neighbor_set] using hnv
        have hnvl : Lt.labeling nv ≠ Fin.last n :=
          by by_contra hc; exact W.ne_of_adj (adj_symm W hnv) ((hvl nv).mp hc)
        have hnvnor : ⟨nv, hnvl⟩ ∈ new_roots_Nt := by
          simp [new_roots_Nt, neighbor_set_Nt]
          left
          exact ⟨nv, hnv', rfl⟩
        let e : Nt.V := ⟨nv, hnvl⟩
        use e
        constructor
        · exact hnvnor
        · let p' : W.Path d.1 nv := ⟨Walk.takeUntil p nv hnvs, Walk.IsPath.takeUntil hp hnvs⟩
          have vp' : v ∉ p'.1.support :=
            Walk.endpoint_notMem_support_takeUntil hp hnvs (ne_of_adj W hnv)
          have hrs : ∀ i ∈ p'.1.support, Lt.labeling i ≠ Fin.last n := by
            intro i hi
            by_contra hc
            have : i = v := (hvl i).mp hc
            rw [this] at hi
            exact vp' hi
          exact reachable_comm.mp (rW_rS' (d.1) nv (↑p') d.property hnvl hrs)

    have h_new_roots : ∀ ⦃x y : Nt.V⦄, x ∈ new_roots_Nt → y ∈ new_roots_Nt →
      x ≠ y → ¬ S'.Reachable x y := by
      intro x y hx hy hu
      simp [new_roots_Nt, old_roots_Nt, neighbor_set_Nt] at hx hy
      rcases hx with ⟨x', x'_mem, x'_eq⟩ | ⟨x', x'_mem, x'_eq⟩ <;>
      rcases hy with ⟨y', y'_mem, y'_eq⟩ | ⟨y', y'_mem, y'_eq⟩
      all_goals
        have x_x' : x' = x.val := by simpa using congrArg Subtype.val x'_eq
        have y_y' : y' = y.val := by simpa using congrArg Subtype.val y'_eq
        have x'_neq_y' : x' ≠ y' := by intro h; subst x; subst y; subst h; exact hu rfl
      · by_contra h
        rcases SimpleGraph.Reachable.exists_isPath h with ⟨p, hp⟩
        let p' : W.Path x.val y.val :=
          ⟨p.map S'_hom_W, Walk.map_isPath_of_injective S'_hom_W_inj hp⟩
        have v_walk : v ∉ p'.1.support := by
          simp [p', S'_hom_W]
          intro k hk
          by_contra hc
          have hcon : Lt.labeling v ≠ Fin.last Lt.n := by rw [← hc]; exact k.property
          exact hcon ((hvl v).mpr rfl)
        have hx'v : W.Adj x' v := by simp [neighbor_set] at x'_mem; exact (adj_symm W x'_mem)
        have hvy' : W.Adj v y' := by simp [neighbor_set] at y'_mem; exact y'_mem
        let walk_x'vy' : W.Walk x' y' := Walk.cons hx'v (Walk.cons hvy' Walk.nil)
        have v_in_walk_x'vy' : v ∈ walk_x'vy'.support := by simp [walk_x'vy']
        have path_x'vy' : walk_x'vy'.IsPath := by
          simp [walk_x'vy']
          refine ⟨?_, ?_, ?_⟩
          · simp [neighbor_set] at y'_mem; apply W.ne_of_adj; exact y'_mem
          · simp [neighbor_set] at x'_mem; apply W.ne_of_adj; exact hx'v
          · exact x'_neq_y'
        subst x_x' y_y'
        have hc : p' = ⟨walk_x'vy', path_x'vy'⟩ := by apply IsAcyclic.path_unique hW'.1
        have hc' : p' ≠ ⟨walk_x'vy', path_x'vy'⟩ := by
          by_contra h_eq
          have h_support_eq : p'.1.support = walk_x'vy'.support := by simp [h_eq]
          have h_support_eq' : walk_x'vy'.support ≠ p'.1.support := by
            apply Membership.mem.ne_of_notMem' v_in_walk_x'vy' v_walk
          exact h_support_eq' (Eq.symm h_support_eq)
        exact hc' hc
      · by_contra h
        have hc1 : W.Reachable x' y' := by rw [x_x', y_y']; exact rS'_rW x y h
        have hc2: ¬W.Reachable x' y' := by
          by_contra hc
          simp [old_new_roots] at y'_mem
          rw [← ne_eq y' v, ne_comm] at y'_mem
          exact (h_roots hv y'_mem.1 y'_mem.2) (Reachable.trans (hvr x' x'_mem) hc)
        exact hc2 hc1
      · by_contra h
        have hc1 : W.Reachable y' x' := by rw [y_y', x_x']; exact rS'_rW y x (Reachable.symm h)
        have hc2: ¬W.Reachable y' x' := by
          by_contra hc
          simp [old_new_roots] at x'_mem
          rw [← ne_eq x' v, ne_comm] at x'_mem
          exact (h_roots hv x'_mem.1 x'_mem.2) (Reachable.trans (hvr y' y'_mem) hc)
        exact hc2 hc1
      · by_contra h
        have hc1 : W.Reachable x' y' := by rw [x_x', y_y']; exact rS'_rW x y h
        have hc2: ¬W.Reachable x' y' := by
          simp [old_new_roots] at x'_mem y'_mem
          exact h_roots x'_mem.1 y'_mem.1 x'_neq_y'
        exact hc2 hc1

    let bij : new_roots_Nt ≃ new_upper_Nt := Finset.equivOfCardEq h_card
    let equiv : Nt.V ≃ Nt.V :=
      calc
      Nt.V ≃ {x // x ∈ new_roots_Nt} ⊕ {x // x ∉ new_roots_Nt} :=
        Equiv.sumCompl (p := fun x => x ∈ new_roots_Nt).symm
      _ ≃ {x // x ∈ new_upper_Nt} ⊕ {x // x ∉ new_upper_Nt} :=
        bij.sumCongr (Fintype.equivOfCardEq (by simp; rw [h_card]))
      _ ≃ Nt.V := Equiv.sumCompl (p := fun x => x ∈ new_upper_Nt)

    have equiv_symm : ∀ (y : Nt.V) (hy : y ∈ new_upper_Nt),
        equiv.symm y = (bij.symm ⟨y, hy⟩).val := by
      intro y hy
      simp [equiv, Equiv.symm_trans_apply, Equiv.sumCompl, Equiv.sumCongr, bij, hy]

    have equiv_forward : ∀ (y : Nt.V) (hy : y ∈ new_roots_Nt),
        equiv y = (bij ⟨y, hy⟩).val := by
      intro y hy
      simp [equiv, Equiv.trans_apply, Equiv.sumCompl, Equiv.sumCongr, bij, hy]

    have equiv_symm_image : equiv.symm '' new_upper_Nt ⊆ new_roots_Nt := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      rw [equiv_symm y hy]
      exact Subtype.coe_prop (bij.symm ⟨y, hy⟩)

    have h_equiv : equiv.symm '' new_upper_Nt = new_roots_Nt := by
      apply Set.Subset.antisymm_iff.mpr
      constructor
      · exact equiv_symm_image
      · intro x hx; simp; rw [equiv_forward x hx]; exact Finset.coe_mem (bij ⟨x, hx⟩)

    let S : SimpleGraph Nt.V := S'.map equiv.toEmbedding
    let graph_iso : S' ≃g S := Iso.map equiv S'
    let c_iso : S'.ConnectedComponent ≃ S.ConnectedComponent :=
      SimpleGraph.Iso.connectedComponentEquiv graph_iso

    have s_acyclic : S.IsAcyclic := by
      rw [← Iso.isAcyclic_iff graph_iso]
      apply IsAcyclic.induce
      exact hW'.1

    have h_reduce_surj : Set.SurjOn S'.connectedComponentMk new_roots_Nt Set.univ →
      Set.SurjOn S.connectedComponentMk (new_upper_Nt : Set Nt.V) Set.univ := by
      intro h c hc_univ
      rw [← h_equiv] at h
      let c' := c_iso.symm c
      rcases h trivial with ⟨y, ⟨x, hx, rfl⟩, hy_c'⟩
      refine ⟨x, hx, ?_⟩
      calc
        S.connectedComponentMk x = c_iso (c_iso.symm (S.connectedComponentMk x)) := by simp
        _ = c_iso (S'.connectedComponentMk (graph_iso.symm x)) := rfl
        _ = c_iso (c_iso.symm c) := congrArg c_iso hy_c'
        _ = c := by simp

    have s_represents :
      ConnectedComponent.Represents
        new_upper_Nt (Set.univ : Set S.ConnectedComponent) := by
      simp [ConnectedComponent.Represents, Set.BijOn]
      refine ⟨?_, ?_, ?_⟩
      · simp [Set.MapsTo]
      · simp [Set.InjOn]
        intro x hx y hy h
        by_contra hc
        let x' : Nt.V := graph_iso.symm x
        let y' : Nt.V := graph_iso.symm y
        have hx' : x' ∈ new_roots_Nt := equiv_symm_image (by dsimp [x']; exact ⟨x, hx, rfl⟩)
        have hy' : y' ∈ new_roots_Nt := equiv_symm_image (by dsimp [y']; exact ⟨y, hy, rfl⟩)
        have hne : x' ≠ y' := by intro h; exact hc (graph_iso.symm.injective h)
        exact (h_new_roots hx' hy' hne) (Iso.reachable_iff.mpr h)
      · apply h_reduce_surj
        simp [Set.SurjOn, Set.ext_iff, Set.mem_image, Set.mem_univ]
        intro c
        rcases ConnectedComponent.nonempty_supp c with ⟨d, hd⟩
        rw [ConnectedComponent.mem_supp_iff] at hd
        rw [← hd]
        simp only [ConnectedComponent.eq]
        exact h_cc d

    have hs : S ∈ forest_set (LabeledTypeWithoutLast Lt hn) (k - 1 + ↑i) := by
      unfold forest_set
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold is_forest_with_roots_in_set
      constructor
      · exact s_acyclic
      · exact s_represents

    ⟨i, ⟨neighbor_set_labels, by rw[← hnn]⟩, ⟨S, hs⟩⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry


  -- lemma helper (n : ℕ) (k : ℕ) (hk : k ≥ 2) (hn : n ≥ 1) :
  -- Fintype.card (ForestType n k) =
  --   ∑ i : Fin (n - k + 1),
  --   Nat.choose (n - k) i * Fintype.card (ForestType (n - 1) (k - 1 + i)) := by
  -- rw [Fintype.card_congr (equiv n k hk hn)]
  -- simp [Fintype.card_sigma]
