import PEqualNP.Defs.BicliqueBlockCost
import PEqualNP.Defs.CoverPromise
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The exact cost of the block covers in L-meta-612. When a graph has no four-cycle,
each nonempty complete bipartite block is a star. Its block cost pays for its
edges. One center per block covers the whole graph, so the number of blocks
also pays for a minimum vertex cover. Assigning edges to centers of a minimum
cover attains the bound, including the empty case with natural subtraction.

This result uses the project's block-family cost. Applying it to every
monotone circuit would additionally require a bound on that cost in terms
of circuit size, including any gates shared between blocks.
-/

namespace PEqualNP.Research.BlockBound612

open PEqualNP.BicliqueBlockCost
open PEqualNP.MetaComplexity.CoverPromise

variable {n : ℕ} {G : SimpleGraph (Fin n)}

def NoFourCycle (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

private theorem star {p : Block n} (hg : NoFourCycle G) (hp : IsBlock G p) :
    p.1.card = 1 ∨ p.2.card = 1 := by
  obtain ⟨hd, hA, hB, adj⟩ := hp
  by_contra! hn
  have haPos := Finset.card_pos.mpr hA
  have hbPos := Finset.card_pos.mpr hB
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp (show 1 < p.1.card by omega)
  obtain ⟨b, hb, d, hd', hbd⟩ := Finset.one_lt_card.mp (show 1 < p.2.card by omega)
  have apart : ∀ i ∈ p.1, ∀ j ∈ p.2, i ≠ j := by
    intro i hi j hj eq
    exact Finset.disjoint_left.mp hd hi (eq ▸ hj)
  exact hg a b c d (apart _ ha _ hb) hac (apart _ ha _ hd') (apart _ hc _ hb).symm
    hbd (apart _ hc _ hd') (adj _ ha _ hb) (adj _ hc _ hb).symm
    (adj _ hc _ hd') (adj _ ha _ hd').symm

private def centerSide (p : Block n) : Finset (Fin n) :=
  if p.1.card = 1 then p.1 else p.2

private def edgesOf (p : Block n) : Finset (Sym2 (Fin n)) :=
  (p.1 ×ˢ p.2).image (fun e => s(e.1, e.2))

private theorem edgeCount {p : Block n} (hp : IsBlock G p) (hg : NoFourCycle G) :
    (edgesOf p).card ≤ blockCost p := by
  calc
    _ ≤ (p.1 ×ˢ p.2).card := Finset.card_image_le
    _ = p.1.card * p.2.card := Finset.card_product _ _
    _ = blockCost p := by
      rcases star hg hp with ha | hb <;> simp [blockCost, *]

theorem family_lower (hg : NoFourCycle G) (F : Finset (Block n))
    (hF : IsBlockCover G F) (t : ℕ)
    (ht : ∀ S : Finset (Fin n), IsVertexCover G S → t ≤ S.card) :
    G.edgeSet.ncard + t ≤ familyCost F + 1 := by
  classical
  let centers := F.biUnion centerSide
  have cover : IsVertexCover G centers := by
    intro u v huv
    obtain ⟨p, hp, huv'⟩ := hF.2 u v huv
    by_cases h : p.1.card = 1
    · rcases huv' with h1 | h2
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, by simpa [centerSide, h] using h1.1⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, by simpa [centerSide, h] using h2.1⟩)
    · rcases huv' with h1 | h2
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, by simpa [centerSide, h] using h1.2⟩)
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨p, hp, by simpa [centerSide, h] using h2.2⟩)
  have tc : t ≤ F.card := calc
    t ≤ centers.card := ht centers cover
    _ ≤ ∑ p ∈ F, (centerSide p).card := Finset.card_biUnion_le
    _ = F.card := by
      calc
        _ = ∑ _p ∈ F, 1 := by
          apply Finset.sum_congr rfl
          intro p hp
          rcases star hg (hF.1 p hp) with ha | hb
          · simp [centerSide, ha]
          · by_cases ha : p.1.card = 1 <;> simp [centerSide, ha, hb]
        _ = _ := by simp
  have subset : G.edgeFinset ⊆ F.biUnion edgesOf := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      obtain ⟨p, hp, huv'⟩ := hF.2 u v huv
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hp, ?_⟩
      rcases huv' with h | h
      · exact Finset.mem_image.mpr ⟨(u,v), Finset.mem_product.mpr h, rfl⟩
      · exact Finset.mem_image.mpr ⟨(v,u), Finset.mem_product.mpr h, Sym2.eq_swap⟩
  have ec : G.edgeSet.ncard ≤ ∑ p ∈ F, blockCost p := calc
    _ = G.edgeFinset.card := by rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
    _ ≤ (F.biUnion edgesOf).card := Finset.card_le_card subset
    _ ≤ ∑ p ∈ F, (edgesOf p).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun p hp => edgeCount (hF.1 p hp) hg
  unfold familyCost
  omega

theorem cost_lower (hg : NoFourCycle G) (t c : ℕ)
    (ht : ∀ S : Finset (Fin n), IsVertexCover G S → t ≤ S.card)
    (hc : HasBlockCost G c) : G.edgeSet.ncard + t ≤ c + 1 := by
  obtain ⟨F, hF, hcost⟩ := hc
  have := family_lower hg F hF t ht
  omega

-- Assign an edge to its endpoint in the cover. If both endpoints belong to
-- the cover, assign it to the smaller one. Each edge is then paid for once.
private noncomputable def leaves (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (c : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => G.Adj c v ∧ (v ∉ T ∨ c < v)

private theorem owner (T : Finset (Fin n)) (hT : IsVertexCover G T) {u v : Fin n}
    (h : G.Adj u v) :
    (u ∈ T ∧ v ∈ leaves G T u) ∨ (v ∈ T ∧ u ∈ leaves G T v) := by
  classical
  simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hu : u ∈ T
  · by_cases hv : v ∈ T
    · rcases lt_or_gt_of_ne h.ne with hlt | hgt
      · exact Or.inl ⟨hu, h, Or.inr hlt⟩
      · exact Or.inr ⟨hv, h.symm, Or.inr hgt⟩
    · exact Or.inl ⟨hu, h, Or.inl hv⟩
  · exact Or.inr ⟨(hT _ _ h).resolve_left hu, h.symm, Or.inl hu⟩

theorem cost_upper (T : Finset (Fin n)) (hT : IsVertexCover G T) :
    HasBlockCost G (G.edgeSet.ncard + T.card - 1) := by
  classical
  let L := leaves G T
  let U := T.filter fun c => (L c).Nonempty
  let block : Fin n → Block n := fun c => ({c}, L c)
  let F := U.image block
  let E : Fin n → Finset (Sym2 (Fin n)) := fun c => (L c).image (fun v => s(c,v))
  have hBlock : IsBlockCover G F := by
    constructor
    · intro p hp
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
      refine ⟨Finset.disjoint_singleton_left.mpr ?_, Finset.singleton_nonempty _, (Finset.mem_filter.mp hc).2, ?_⟩
      · intro h
        have hcc : G.Adj c c := (Finset.mem_filter.mp h).2.1
        exact hcc.ne rfl
      · intro a ha b hb
        have : a = c := Finset.mem_singleton.mp ha
        subst a
        exact (Finset.mem_filter.mp hb).2.1
    · intro u v huv
      rcases owner T hT huv with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact ⟨block u, Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, ⟨v,hv⟩⟩, rfl⟩,
          Or.inl ⟨Finset.mem_singleton_self _, hv⟩⟩
      · exact ⟨block v, Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, ⟨u,hu⟩⟩, rfl⟩,
          Or.inr ⟨Finset.mem_singleton_self _, hu⟩⟩
  have disjointEdges : (U : Set (Fin n)).PairwiseDisjoint E := by
    intro c hc d hd hne
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨y, hy, eq⟩ := Finset.mem_image.mp he'
    rcases Sym2.eq_iff.mp eq with h | ⟨hdx, hyc⟩
    · exact hne h.1.symm
    · subst x
      subst y
      have inC : c ∈ T := (Finset.mem_filter.mp hc).1
      have inD : d ∈ T := (Finset.mem_filter.mp hd).1
      have hcd : c < d := (Finset.mem_filter.mp hx).2.2.resolve_left (fun h => h inD)
      have hdc : d < c := (Finset.mem_filter.mp hy).2.2.resolve_left (fun h => h inC)
      exact (lt_asymm hcd hdc)
  have subset : U.biUnion E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hc
    exact SimpleGraph.mem_edgeFinset.mpr (Finset.mem_filter.mp hv).2.1
  have injBlock : Function.Injective block := by
    intro a b h
    exact Finset.singleton_injective (congrArg Prod.fst h)
  have sizes : (∑ p ∈ F, blockCost p) ≤ G.edgeSet.ncard := calc
    _ = ∑ c ∈ U, blockCost (block c) := Finset.sum_image (fun _ _ _ _ h => injBlock h)
    _ = ∑ c ∈ U, (E c).card := by
      apply Finset.sum_congr rfl
      intro c _
      have inj : Function.Injective (fun v : Fin n => s(c,v)) := fun _ _ h => Sym2.congr_right.mp h
      simp [E, block, blockCost, Finset.card_image_of_injective _ inj]
    _ = (U.biUnion E).card := (Finset.card_biUnion disjointEdges).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card subset
    _ = _ := by rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  have num : F.card ≤ T.card :=
    Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _))
  refine ⟨F, hBlock, ?_⟩
  by_cases empty : F = ∅
  · simp [empty, familyCost]
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    unfold familyCost
    omega

theorem exact_cost (hg : NoFourCycle G) (T : Finset (Fin n)) (hT : IsVertexCover G T)
    (hmin : ∀ S : Finset (Fin n), IsVertexCover G S → T.card ≤ S.card) :
    bc G = G.edgeSet.ncard + T.card - 1 := by
  have hi := cost_upper T hT
  have inhabited : {c : ℕ | HasBlockCost G c}.Nonempty := ⟨_, hi⟩
  have lo := cost_lower hg T.card (bc G) hmin (Nat.sInf_mem inhabited)
  have up : bc G ≤ G.edgeSet.ncard + T.card - 1 := Nat.sInf_le hi
  omega

end PEqualNP.Research.BlockBound612
