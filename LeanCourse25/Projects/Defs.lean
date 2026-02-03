import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Represents
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Equiv.Fin.Basic

open Classical SimpleGraph

--there is exactly one element from roots in each connected component of G
variable {α : Type} [Fintype α] {w : α} {roots : Finset α} {hw : w ∈ roots}

def is_forest_with_roots_in_set {α : Type} [Fintype α] (G : SimpleGraph α)
  (roots : Finset α) : Prop :=
  G.IsAcyclic ∧ ConnectedComponent.Represents
    roots (Set.univ : Set G.ConnectedComponent)

def forest_set {α : Type} [Fintype α]
  (roots : Finset α) := {G | is_forest_with_roots_in_set G roots}

class IsForestWithRoots (G : SimpleGraph α) (roots : Finset α) : Prop where
  (hG : G ∈ forest_set roots)

def induce_hom (S : SimpleGraph α) : S.induce {v | v ≠ w} →g S := {
  toFun := fun v => v.val
  map_rel' := by intro v w h; exact h}

omit [Fintype α] in
lemma induce_hom_inj (S : SimpleGraph α) : Function.Injective (induce_hom (w:= w) S)  := by
  intro v w h
  exact Subtype.ext h

def f (G : SimpleGraph α) : SimpleGraph {v | v ≠ w} :=
  G.induce {v | v ≠ w}

omit [Fintype α] in
lemma f_inj (G G' : SimpleGraph α) :
  (f (w := w) G = f G' ∧ ∀ u : α, (G.Adj u w ↔ G'.Adj u w)) → G = G' := by
  intro h
  rcases h with ⟨hf, ha⟩
  ext x y
  by_cases bcx : x = w <;>
  by_cases bcy : y = w
  · subst bcx bcy
    simp only [SimpleGraph.irrefl]
  · subst bcx
    rw [adj_comm G x y, adj_comm G' x y]
    exact ha y
  · subst bcy
    exact ha x
  · simp [f] at hf
    rw [SimpleGraph.ext_iff, funext_iff] at hf
    specialize hf ⟨x, bcx⟩
    rw [funext_iff] at hf
    specialize hf ⟨y, bcy⟩
    simp at hf
    exact hf







noncomputable def new_roots (roots : Finset α) (G : SimpleGraph α) :
  Finset {v | v ≠ w} := (roots ∪ G.neighborFinset w).subtype (fun v => v ≠ w)

noncomputable def coer (set : Finset α) :
  Finset {v | v ≠ w} := set.subtype (fun v => v ≠ w)



--some helper lemmas
lemma inj_comp (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
  ∀ x, x ∈ roots → ∀ y, y ∈ roots → G.Reachable x y → x = y := by
  simp [forest_set, is_forest_with_roots_in_set, ConnectedComponent.Represents,
    Set.BijOn, Set.InjOn] at hG
  exact hG.2.2.1

-- lemma surj_comp [IsForestWithRoots G roots] :
--     ∀ x, ∃ r ∈ roots, G.connectedComponentMk r = x := by
--   have hG := IsForestWithRoots.hG (G := G) (roots := roots)
--   simp [forest_set, is_forest_with_roots_in_set, ConnectedComponent.Represents,
--     Set.BijOn, Set.SurjOn, Set.ext_iff, Set.mem_image, Set.mem_univ] at hG
--   exact hG.2.2.2

lemma roots_not_reachable (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
  ∀ u w, u ∈ roots → w ∈ roots → u ≠ w → ¬G.Reachable u w := by
  intro u w hu hw he
  by_contra hc
  exact he (inj_comp G hG u hu w hw hc)

lemma roots_neighbors_not_reachable {hw : w ∈ roots}
  (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
  ∀ u v, u ∈ roots → v ∈ G.neighborFinset w → u ≠ w → ¬G.Reachable u v := by
  intro u v hu hv he
  by_contra hc
  simp only [mem_neighborFinset] at hv
  exact roots_not_reachable G hG w u hw hu (Ne.symm he)
    (Reachable.trans (Adj.reachable hv) (Reachable.symm hc))

--otherwise there would be one path with w and one without w
lemma neighbors_neighbors_not_reachable (G : SimpleGraph α) (ha : G.IsAcyclic)
  (x y : α) (hx : x ≠ w) (hy : y ≠ w) : x ≠ y → x ∈ G.neighborFinset w → y ∈ G.neighborFinset w →
    ¬(G.induce {v | v ≠ w}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  intro hc hx' hy'
  by_contra hr
  rcases Reachable.exists_isPath hr with ⟨p, hp⟩
  have hxw : G.Adj x w := by simp at hx'; exact adj_symm G hx'
  have hyw : G.Adj w y := by simp at hy'; exact hy'
  let xwy : G.Walk x y := Walk.cons hxw (Walk.cons hyw Walk.nil)
  have pxwy : xwy.IsPath := by simp [xwy]; exact ⟨Ne.symm hy, hx, hc⟩
  have wp : w ∈ xwy.support := by simp [xwy]
  let xy : G.Path x y :=
    ⟨p.map (induce_hom G), Walk.map_isPath_of_injective (induce_hom_inj G) hp⟩
  have wp' : w ∉ xy.1.support := by simp [xy, induce_hom]
  have hc : xy = ⟨xwy, pxwy⟩ := by apply IsAcyclic.path_unique ha
  have hc' : xy ≠ ⟨xwy, pxwy⟩ := by
    by_contra hc
    have heq : xy.1.support = xwy.support := by simp only [hc]
    exact (Membership.mem.ne_of_notMem' wp wp') (Eq.symm heq)
  exact hc' hc

--if there is a walk W from x to y with w ∉ W.support,
--there is a walk from x to y in G.induce {v | v ≠ w}
omit [Fintype α] in
lemma reachability_subgraph (G : SimpleGraph α) (x y : α) (p : G.Walk x y) (hx : x ≠ w) (hy : y ≠ w)
  (hs : ∀ v ∈ p.support, v ≠ w) : (G.induce {v | v ≠ w}).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
    ⟨by induction p with
      | nil => exact Walk.nil
      | @cons a b i h p' ih =>
        have ha : a ≠ w := hx
        have hb : b ≠ w := by exact hs b (by simp [Walk.support_cons])
        have h_edge : (G.induce {v | v ≠ w}).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by simp [SimpleGraph.induce, h]
        have hs' : ∀ x ∈ p'.support, x ≠ w := by
          intro x hx
          apply hs x
          simp [Walk.support_cons, hx]
        exact Walk.cons h_edge (ih hb hy hs')⟩

--prove that there is a path from every node x in G.induce {v | v ≠ w} to
--a node in (roots \ {w} ∪ G.neighborFinset w)
lemma new_roots_surj {hw : w ∈ roots} (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
  ∀ x, ∃ y ∈ (new_roots roots G), (G.induce {v | v ≠ w}).Reachable x y := by
  intro x
  let xcc : G.ConnectedComponent := G.connectedComponentMk x
  have xc : xcc ∈ Set.univ := trivial
  rcases hG.2.surjOn xc with ⟨r, hr, hrc⟩
  have hrr : G.Reachable x r := by simp [xcc] at hrc; exact Reachable.symm hrc
  by_cases bc : r ≠ w
  · --case where x is not in connected component of w
    use ⟨r, bc⟩
    constructor
    · simp [new_roots]
      left
      exact hr
    · rcases Reachable.exists_isPath hrr with ⟨p, hp⟩
      have hps : ∀ i ∈ p.support, i ≠ w := by
        intro i hi
        by_contra hc
        have hrw : G.Reachable r w := by
          rw [← hc]
          exact ⟨Walk.takeUntil p.reverse i (by simpa using hi)⟩
        exact (roots_not_reachable G hG r w hr hw bc) hrw
      exact reachability_subgraph G x.1 r p x.2 bc hps
  · --case where x is in connected component of w
    rcases Reachable.exists_isPath hrr with ⟨p, hp⟩
    rw [not_ne_iff] at bc
    subst bc
    rcases adj_of_mem_walk_support p (Walk.not_nil_of_ne x.2)
      (Walk.end_mem_support p) with ⟨n, hn, hnr⟩
    have hne : n ≠ r := G.ne_of_adj (adj_symm G hnr)
    use ⟨n, hne⟩
    constructor
    · simp [new_roots]; right; exact hnr
    · let p' : G.Path x n := ⟨Walk.takeUntil p n hn, Walk.IsPath.takeUntil hp hn⟩
      have vp' : r ∉ p'.1.support :=
        Walk.endpoint_notMem_support_takeUntil hp hn (ne_of_adj G hnr)
      have hrs : ∀ i ∈ p'.1.support, i ≠ r := by
        intro i hi
        exact ne_of_mem_of_not_mem hi vp'
      exact reachability_subgraph G x.1 n p'.1 x.2 hne hrs


--if we delete a root w, then we get a forest rooted in (roots \ {w} ∪ G.neighborFinset w)
theorem f_maps_to {hw : w ∈ roots} (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
  f G ∈ forest_set (new_roots (w := w) roots G) := by
  simp [f, forest_set, is_forest_with_roots_in_set] at hG ⊢
  constructor
  · apply IsAcyclic.induce hG.1
  · simp [ConnectedComponent.Represents, Set.BijOn]
    refine ⟨?_, ?_, ?_⟩
    · simp [Set.MapsTo]
    · simp [Set.InjOn]
      intro x hx hx' y hy hy' hr
      by_contra hc
      simp only [new_roots, ne_eq, Finset.mem_subtype, Finset.mem_union] at hx' hy'
      rcases hx' with hx' | hx' <;>
      rcases hy' with hy' | hy'
      · exact (roots_not_reachable G hG x y hx' hy' hc)
          (Reachable.map (induce_hom G) hr)
      · exact roots_neighbors_not_reachable (hw := hw) G hG x y hx' hy' hx
          (Reachable.map (induce_hom G) hr)
      · exact roots_neighbors_not_reachable (hw := hw) G hG y x hy' hx' hy
          (Reachable.symm (Reachable.map (induce_hom G) hr))
      · have hh : ¬(induce {v | v ≠ w} G).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
          exact (neighbors_neighbors_not_reachable G hG.1 x y hx hy hc hx' hy')
        exact hh hr
    · simp [Set.SurjOn, Set.ext_iff, Set.mem_image, Set.mem_univ]
      intro cc
      rcases ConnectedComponent.nonempty_supp cc with ⟨d, hd⟩
      rw [ConnectedComponent.mem_supp_iff] at hd
      rw [← hd]
      simp only [ConnectedComponent.eq]
      obtain ⟨a, ha, ha'⟩ := new_roots_surj G hG (w := w) (hw := hw) d
      exact ⟨a.1, a.2, ha, Reachable.symm ha'⟩

-- lemma disj {hw : w ∈ roots} (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
--   Disjoint (G.neighborFinset w) roots := by
--   rw [Finset.disjoint_iff_ne]
--   intro a ha b hb
--   by_contra hc
--   simp only [mem_neighborFinset] at ha
--   subst hc
--   exact roots_not_reachable G hG a w hb hw (Adj.ne' ha) (Adj.reachable (adj_symm G ha))

-- lemma card {hw : w ∈ roots} (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
--   (G.neighborFinset w).card < Fintype.card α - roots.card + 1 := by
--   rw [Order.lt_add_one_iff]
--   have h : (G.neighborFinset w).card + roots.card ≤ Fintype.card α := by
--     rw [← Finset.card_union_eq_card_add_card.mpr (disj G hG)]
--     · exact Finset.card_le_univ (G.neighborFinset w ∪ roots)
--     · exact hw
--   exact Nat.le_sub_of_add_le h


def valid_neighbor_sets_i (i : ℕ) (w : α) (roots : Finset α) : Type :=
  {N : Finset α // w ∉ N ∧ Disjoint N roots ∧ N.card = i}

--further plan:
--fix an i and a valid_neighbor_set_i N
--f induces a bijection between the forests rooted in roots, where w has i neighbors
--in valid_neighbor_set_i N, and the forests rooted in (roots \ {w} ∪ N)
--we already proved injectivity

--after that we need to prove that the union over all valid_neighbor_sets_i
--covers each forest exactly one time

def forest_fiber (N : Finset α) : Type _ :=
  {G : SimpleGraph α // G ∈ forest_set roots ∧ (G.neighborFinset w) = N}

def f_on_fiber (i : Fin (Fintype.card α - Finset.card roots + 1))
  (N : valid_neighbor_sets_i i w roots) (G : forest_set roots) () : := ⟨ ⟩



-- lemma disj_coe {hw : w ∈ roots} (F : SimpleGraph α) (hF : F ∈ forest_set roots) :
--   Disjoint (α := Finset {v : α // v ≠ w}) (coer (F.neighborFinset w)) (coer roots) := by
--   simp[coer]
--   rw [Finset.disjoint_iff_ne]
--   intro a ha b hb
--   simp at ha hb
--   by_contra hc
--   subst hc
--   exact roots_not_reachable F hF a w hb hw (Adj.ne' ha) (Adj.reachable (adj_symm F ha))

-- lemma card_coe {hw : w ∈ roots} (G : SimpleGraph α) (hG : G ∈ forest_set roots) :
--   (G.neighborFinset w).card < Fintype.card α - roots.card + 1 := by
--   rw [Order.lt_add_one_iff]
--   have h : (G.neighborFinset w).card + roots.card ≤ Fintype.card α := by
--     rw [← Finset.card_union_eq_card_add_card.mpr (disj G hG)]
--     · exact Finset.card_le_univ (G.neighborFinset w ∪ roots)
--     · exact hw
--   exact Nat.le_sub_of_add_le h


-- noncomputable def f_ext (F : SimpleGraph α) (hF : F ∈ forest_set roots) :
--   Finset {v | v ≠ w} × (forest_set (α := {v | v ≠ w}) (new_roots roots F)) :=
--   ⟨coer (F.neighborFinset w), ⟨f F, f_maps_to (hw := hw) F hF⟩⟩

-- theorem f_ext_injective {F1 F2 : SimpleGraph α} (hF1 : F1 ∈ forest_set roots) (hF2 : F2 ∈ forest_set roots) :
--     f_ext F1 hF1 = f_ext F2 hF2 → F1 = F2 := by sorry

-- def valid_neighbor_sets_i (i : ℕ) (w : α) (roots : Finset α) : Type :=
--   {N : Finset {v | v ≠ w} // Disjoint N (coer roots) ∧ N.card = i}

-- --((N.1 ∪ roots) \ {w})
-- noncomputable def f_ext {hw : w ∈ roots} (F : SimpleGraph α) (hF : F ∈ forest_set roots) :
--   Σ i : Fin (Fintype.card α - Finset.card roots + 1),
--     Σ N : valid_neighbor_sets_i i w roots, forest_set (N.1 ∪ (coer roots)) :=

--   ⟨⟨(F.neighborFinset w).card, card (hw := hw) F hF⟩,
--   ⟨coer (F.neighborFinset w), ⟨disj_coe (hw := hw) F hF, by
--     simp only [ne_eq, coer, Finset.card_subtype]
--     refine Finset.card_filter_eq_iff.mpr ?_
--     intro x hx
--     rw [F.mem_neighborFinset] at hx
--     exact Adj.ne' hx
--     ⟩⟩,
--   ⟨f F, by
--     simp[coer]
--     have hh : f F ∈ forest_set (new_roots roots F) := f_maps_to (hw := hw) F hF
--     simp [new_roots] at hh
--     have hlper : (Finset.subtype (fun v ↦ ¬v = w) (F.neighborFinset w) ∪
--       Finset.subtype (fun v ↦ ¬v = w) roots) =
--       (Finset.subtype (fun v ↦ ¬v = w) (roots ∪ F.neighborFinset w)) := by
--       ext x
--       simp
--       rw [or_comm]
--     rw[hlper]
--     exact hh
--     ⟩⟩

-- lemma f_ext_injective {hw : w ∈ roots} :
--   Function.Injective (fun Fh :
--       { F : SimpleGraph α // F ∈ forest_set roots } =>
--       f_ext (hw := hw) Fh.1 Fh.2) := by
--   intro f1 f2 he
--   simp [f_ext, coer] at he
--   rcases he with ⟨a,b⟩
--   --apply Subtype.ext

--   have h_neighbor_set_eq :
--     Finset.subtype (fun v ↦ ¬v = w) ((f1.1).neighborFinset w) =
--     Finset.subtype (fun v ↦ ¬v = w) ((f2.1).neighborFinset w) :=
--     congr_arg Sigma.fst (congr_arg Sigma.fst (eq_of_heq b))


-- structure ExtendedForest where
--   i : Fin (Fintype.card α - Finset.card roots + 1)
--   N : valid_neighbor_sets_i i w roots
--   forest : forest_set (N.1 ∪ (coer roots))

-- noncomputable def f_ext {hw : w ∈ roots} (F : SimpleGraph α) (hF : F ∈ forest_set roots) :
--   ExtendedForest (α:=α) (roots:=roots) (w:=w) :=
--   ⟨⟨(F.neighborFinset w).card, card (hw := hw) F hF⟩,
--   ⟨coer (F.neighborFinset w), ⟨disj_coe (hw := hw) F hF, by
--     simp only [ne_eq, coer, Finset.card_subtype]
--     refine Finset.card_filter_eq_iff.mpr ?_
--     intro x hx
--     rw [F.mem_neighborFinset] at hx
--     exact Adj.ne' hx
--     ⟩⟩,
--   ⟨f F, by
--     simp[coer]
--     have hh : f F ∈ forest_set (new_roots roots F) := f_maps_to (hw := hw) F hF
--     simp [new_roots] at hh
--     have hlper : (Finset.subtype (fun v ↦ ¬v = w) (F.neighborFinset w) ∪
--       Finset.subtype (fun v ↦ ¬v = w) roots) =
--       (Finset.subtype (fun v ↦ ¬v = w) (roots ∪ F.neighborFinset w)) := by
--       ext x
--       simp
--       rw [or_comm]
--     rw[hlper]
--     exact hh
--     ⟩⟩

-- lemma f_ext_injective {hw : w ∈ roots} :
--   Function.Injective (fun Fh :
--       { F : SimpleGraph α // F ∈ forest_set roots } =>
--       f_ext (hw := hw) Fh.1 Fh.2) := by
--   intro f1 f2 he
--   simp [f_ext, coer] at he
--   rcases he with ⟨a,b,c⟩





noncomputable def number_of_forests {α : Type} [Fintype α]
  (roots : Finset α) : ℕ := (Finset.univ.filter
    (fun G => is_forest_with_roots_in_set G roots)).card

theorem general_cayley {α : Type} [Fintype α] (roots : Finset α) :
    number_of_forests roots =
      Finset.card roots * Fintype.card α ^ (Fintype.card α - Finset.card roots - 1) := by
      --bijection proof
      sorry
