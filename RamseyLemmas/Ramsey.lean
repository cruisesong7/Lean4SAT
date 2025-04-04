import Mathlib.Data.Rat.Init
import Lean.Parser.Tactic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice

import FormalRamsey.Ramsey2Color

namespace SimpleGraph

section FintypeVGraph
variable {V : Type*} (G : SimpleGraph V) (x y : ℕ)

-- Define the Independence number for a SimpleGraph G
noncomputable abbrev indNum : ℕ := Gᶜ.cliqueNum

-- an (x,y)-graph on n vertices iff does not have clique of size x or independet set of size y
def isXYGraph : Prop := G.cliqueNum < x ∧ G.indNum < y

noncomputable def RamseyOld : ℕ  :=  sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)) (_ : DecidableRel G.Adj), G.isXYGraph x y}

theorem Lemma₁ : G.isXYGraph x y ↔ Gᶜ.isXYGraph y x := by
  simp [isXYGraph, indNum]
  tauto

variable [Fintype V]

lemma exists_IsNClique_of_le_cliqueNum  {n : ℕ} (h : n ≤ G.cliqueNum) : ∃ S : Finset V, G.IsNClique n S := by
  rcases G.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

lemma exists_IsNIndset_of_le_indNum  {n : ℕ} (h : n ≤ G.indNum) : ∃ S : Finset V, Gᶜ.IsNClique n S := by
  rcases Gᶜ.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

lemma cliqueNum2CliqueFree: G.cliqueNum < x ↔ G.CliqueFree x := by
  simp [CliqueFree, isNClique_iff]
  apply Iff.intro
  · intros H_cliqueNum S SIsClique
    linarith [SIsClique.card_le_cliqueNum]
  · intro NotXClique
    obtain ⟨S, SMaxClique⟩ := G.maximumClique_exists
    have SCardEqCN := maximumClique_card_eq_cliqueNum S SMaxClique
    simp [isMaximumClique_iff] at SMaxClique
    have SCardNEx := NotXClique S SMaxClique.left
    rw [SCardEqCN] at SCardNEx
    rcases Nat.lt_or_gt_of_ne (Ne.symm SCardNEx) with h | h
    · obtain ⟨T, TClique⟩ := exists_IsNClique_of_le_cliqueNum G (Nat.le_of_lt h)
      simp [G.isNClique_iff] at TClique
      have contra := NotXClique T TClique.left
      simp_all
    · assumption

theorem noXYGraphIffRamseyGraphProp (N: ℕ) : (∀ (G : SimpleGraph (Fin N)), ¬ G.isXYGraph x y) ↔ RamseyGraphProp N x y := by
  simp [isXYGraph, RamseyGraphProp, indNum]
  apply Iff.intro <;> intros H G
  · have cliqueNumProp := H G
    by_contra RamseyProp
    by_cases H : G.cliqueNum < x
    · have H₁ := not_lt_of_le (cliqueNumProp H)
      simp [cliqueNum2CliqueFree] at H H₁
      simp_all [CliqueFree]
    · simp [cliqueNum2CliqueFree] at H
      simp_all [CliqueFree]
  · intro cliqueNumProp
    obtain ⟨S,SClique⟩ | ⟨T, TClique⟩ := H G
    · rw [cliqueNum2CliqueFree] at cliqueNumProp
      simp_all [CliqueFree]
    · by_contra H
      simp [cliqueNum2CliqueFree] at H
      simp_all [CliqueFree]

lemma isXYGraph_bddAbove : BddAbove {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x y} := by
  simp [BddAbove, upperBounds, Set.Nonempty]
  rcases (Ramsey₂Finite x y) with ⟨N, NRamsey⟩
  simp at NRamsey
  use N
  intros M G Gxy
  cases Nat.le_or_ge M N with
  | inl _ => assumption
  | inr MgeN =>
    have MRamsey : RamseyGraphProp M x y := by
      suffices Ramsey₂Prop M x y by rwa [← Ramsey₂GraphProp]
      exact Ramsey.RamseyMonotone NRamsey MgeN
    rw [← noXYGraphIffRamseyGraphProp] at MRamsey
    cases MRamsey G Gxy

-- NOTE: This can be strengthened to <, using more or less the same proof
lemma cardLERamseyOld [DecidableEq V] : G.isXYGraph x y → Fintype.card V ≤ RamseyOld x y := by
  cases (Nat.eq_zero_or_pos (Fintype.card V)) with
  | inl Vempty => simp [Vempty]
  | inr Vnonempty =>
    intro Gxy
    simp [RamseyOld]
    apply le_csSup
    · exact isXYGraph_bddAbove x y
    · simp [SimpleGraph.isXYGraph] at Gxy ⊢
      have mapping : Fintype.card V = Fintype.card (Fin (Fintype.card V)) := by simp
      rw [Fintype.card_eq] at mapping
      rcases mapping with ⟨f, g, fginv, gfinv⟩
      have fInj : f.Injective := Function.LeftInverse.injective fginv
      use G.map ⟨f, fInj⟩
      apply And.intro <;> apply Nat.lt_of_not_ge <;> intro clique
      · simp at clique
        rcases exists_IsNClique_of_le_cliqueNum _ clique with ⟨s, sclique⟩
        rw [SimpleGraph.isNClique_map_iff] at sclique
        · rcases sclique with ⟨t, tclique, _⟩
          have xle := tclique.isClique.card_le_cliqueNum
          rw [tclique.card_eq] at xle
          cases (Nat.not_lt_of_le xle) Gxy.left
        · cases Nat.eq_zero_or_pos G.cliqueNum with
          | inl cnzero =>
            simp [Fintype.card_pos_iff] at Vnonempty
            rcases Vnonempty with ⟨v⟩
            have cliqueNum1 : 1 ≤ G.cliqueNum := by
              suffices Finset.card {v} ≤ G.cliqueNum by simpa
              apply SimpleGraph.IsClique.card_le_cliqueNum
              simp [SimpleGraph.IsNClique]
            simp [cnzero] at cliqueNum1
          | inr cnpos =>
            simp at cnpos
            exact Nat.lt_of_le_of_lt cnpos Gxy.left
      · simp at clique
        rcases exists_IsNClique_of_le_cliqueNum _ clique with ⟨s, sclique⟩
        replace Vnonempty := Fintype.card_pos_iff.mp Vnonempty
        have moveComplInside : (SimpleGraph.map { toFun := f, inj' := fInj} G)ᶜ = SimpleGraph.map { toFun := f, inj' := fInj} Gᶜ := by
          simp [SimpleGraph.map]
          ext v w
          apply Iff.intro
          simp [Relation.Map]
          intros vneqw this
          use (g v), (g w)
          specialize this (g v) (g w)
          refine ⟨⟨ ?_, ?_,⟩, ⟨?_, ?_⟩⟩
          · apply Function.Injective.ne
            apply Function.RightInverse.injective gfinv
            exact vneqw
          · intro contra
            specialize this contra
            tauto
          · tauto
          · tauto
          simp [Relation.Map]
          intros x y xneqy xyAdj fx fy
          apply And.intro
          · by_contra!
            rw [this, ← fy] at fx
            replace fx := (Function.Injective.eq_iff fInj).mp fx
            exact xneqy fx
          · intros x₁ y₁ xyNAdj fx₁ fy₁
            subst_vars
            replace fx₁ := (Function.Injective.eq_iff fInj).mp fx₁
            replace fy₁ := (Function.Injective.eq_iff fInj).mp fy₁
            subst_vars
            tauto
        rw [moveComplInside, SimpleGraph.isNClique_map_iff] at sclique
        · rcases sclique with ⟨t, tclique, _⟩
          have xle := tclique.isClique.card_le_cliqueNum
          rw [tclique.card_eq] at xle
          cases (Nat.not_lt_of_le xle) Gxy.right
        · cases Nat.eq_zero_or_pos G.indNum with
          | inl cnzero =>
            rcases Vnonempty with ⟨v⟩
            have indNum1 : 1 ≤ G.indNum := by
              suffices Finset.card {v} ≤ G.indNum by simpa
              apply SimpleGraph.IsClique.card_le_cliqueNum
              simp [SimpleGraph.IsNClique]
            simp [cnzero] at indNum1
          | inr cnpos =>
            simp at cnpos
            exact Nat.lt_of_le_of_lt cnpos Gxy.right
------------------------------------------------ RamseyOld <-> GraphRamsey
variable {G}

lemma fintype_cliqueNum_bddAbove : BddAbove {n | ∃ s, G.IsNClique n s} := by
  use Fintype.card V
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

--TODO: prove mono_RamseyOld
-- theorem GraphRamsey2RamseyOld : GraphRamsey x y = RamseyOld x y + 1 := by
--   simp [GraphRamsey]
--   rw [Nat.sInf_upward_closed_eq_succ_iff]
--   . simp_all
--     apply And.intro
--     · simp [← noXYGraphIffRamseyGraphProp]
--       intro G _
--       by_contra H
--       sorry
--     · sorry
--   · simp
--     intro M N MleqN MRamsey
--     exact RamseyGraphMonotone MRamsey MleqN

variable (i : ℕ) (G) [DecidableRel G.Adj]
noncomputable abbrev v_i : ℤ := RamseyOld x y.succ - i

noncomputable abbrev s_i : ℕ := (Finset.univ).filter (λ v ↦ G.degree v = v_i x y i) |>.card
noncomputable abbrev t_i (p : V): ℕ := (G.neighborFinset p).filter (λ v ↦ G.degree v = v_i x y i) |>.card

variable {G x y}
noncomputable def σ_G (_ : G.isXYGraph x.succ y.succ) : ℕ := RamseyOld x y.succ - G.minDegree

lemma sum_degree_eq_sum_over_degrees :
  ∑ v : V, G.degree v =
    ∑ d in Finset.image (λ v ↦ G.degree v) Finset.univ, d * ((Finset.univ).filter (λ v ↦ G.degree v = d)).card := by

    have h_sigma : (∑ v: V, G.degree v) =
    ∑ p in Finset.sigma (Finset.image (λ v ↦ G.degree v) Finset.univ) (λ d ↦ Finset.univ.filter (λ v ↦ G.degree v = d)), G.degree p.2 := by
      apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
      intros p _ _ h
      use p.2
      rw [h]

    rw [h_sigma]

    have h_inner_sum : ∀ d ∈ (Finset.image (λ v ↦ G.degree v) Finset.univ),
    (∑ v in (Finset.univ.filter (λ v ↦ G.degree v = d)), G.degree v) =
    d * ((Finset.univ).filter (λ v ↦ G.degree v = d)).card := by
      intros d hd
      have h : ∀ v ∈ (Finset.univ.filter (λ v ↦ G.degree v = d)), G.degree v = d := by
        intros v hv
        rw [Finset.mem_filter] at hv
        rcases hv with ⟨hv1, hv2⟩
        rw [hv2]
      rw [Finset.sum_const_nat h]
      apply mul_comm

    suffices:
      (∑ p in Finset.sigma  (Finset.image (λ v ↦ G.degree v) Finset.univ) (λ d ↦ Finset.univ.filter (λ v ↦ G.degree v = d)), G.degree p.2) =
      (∑ d in (Finset.image (λ v ↦ G.degree v) Finset.univ), ∑ v in Finset.univ.filter (λ v ↦  G.degree v = d), G.degree v)
    rw[this]
    apply Finset.sum_congr rfl h_inner_sum
    simp [Finset.sum_sigma']

lemma num_of_vertices_eq_sum_over_degrees : Fintype.card V =
  ∑ d in Finset.image (λ v ↦ G.degree v) Finset.univ, ((Finset.univ).filter (λ v ↦ G.degree v = d)).card := by
  transitivity (∑ v: V, 1)
  simp
  have h_sigma : (∑ v: V, 1) =
    ∑ p in Finset.sigma (Finset.image (λ v ↦ G.degree v) Finset.univ) (λ d ↦ Finset.univ.filter (λ v ↦  G.degree v = d)), 1 := by
      apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
      intros p _ _ h
      use p.2
      rw [h]
  rw [h_sigma]
  suffices:
      (∑ p in Finset.sigma  (Finset.image (λ v ↦ G.degree v) Finset.univ) (λ d ↦ Finset.univ.filter (λ v ↦ G.degree v = d)), 1) =
      (∑ d in (Finset.image (λ v ↦ G.degree v) Finset.univ), ∑ v in Finset.univ.filter (λ v ↦  G.degree v = d), 1)
  rw[this]
  apply Finset.sum_congr rfl (by simp)
  simp [Finset.sum_sigma']
end FintypeVGraph
----------------------------------

section FinNGraph
variable (G : SimpleGraph (Fin N))[DecidableRel G.Adj] (p : Fin N)

def H₁ : SimpleGraph ↑(G.neighborSet p) := G.induce (G.neighborSet p)
instance H₁AdjDecidableRel : DecidableRel (H₁ G p).Adj := by apply instDecidableComapAdj

def H₂ : SimpleGraph ↑(Gᶜ.neighborSet p) := G.induce (Gᶜ.neighborSet p)
instance H₂AdjDecidableRel : DecidableRel (H₂ G p).Adj := by apply instDecidableComapAdj

abbrev e₁ : ℕ := (H₁ G p).edgeFinset.card
abbrev e₂ : ℕ := (H₂ G p).edgeFinset.card

end FinNGraph

section NonEmptyGraph

variable {x y N : ℕ} (G : SimpleGraph (Fin N.succ))(p : Fin N.succ)
-- set_option pp.explicit true
lemma oneLeCN: 1 ≤ G.cliqueNum := by
  apply le_csSup fintype_cliqueNum_bddAbove
  simp
  tauto

lemma indNumMono : (H₁ G p).indNum ≤ G.indNum := by
  simp [indNum, cliqueNum]
  apply csSup_le_csSup'
  · exact fintype_cliqueNum_bddAbove
  · rintro n ⟨S, SProp⟩
    simp
    use S.map (Function.Embedding.subtype _)
    simp [isNClique_iff,IsClique] at SProp ⊢
    apply And.intro
    · intros a ha b hb hab
      simp_all
      rcases ha with ⟨ha, ha_mem⟩
      rcases hb with ⟨hb, hb_mem⟩
      simp[Set.Pairwise] at SProp
      have _ := SProp.left a ha ha_mem b hb hb_mem hab
      tauto
    · exact SProp.right

variable [DecidableRel G.Adj]
lemma cliqueNumMono : (H₁ G p).cliqueNum ≤ G.cliqueNum - 1 := by
    simp [cliqueNum]
    rw [csSup_le_iff' fintype_cliqueNum_bddAbove]
    by_contra! H
    obtain ⟨n, ⟨ S, SClique⟩, SProp⟩ := H
    suffices : ∃ s, G.IsNClique n.succ s
    have tmp : n.succ ∈ {n | ∃ s, G.IsNClique n s} := by simp[this]
    have contra := le_csSup fintype_cliqueNum_bddAbove (tmp)
    rw [← @Nat.sub_le_sub_iff_right 1 (sSup {n | ∃ s, G.IsNClique n s}) n.succ] at contra
    simp_all; linarith
    exact oneLeCN G
    use insert p (S.map (Function.Embedding.subtype _))
    apply IsNClique.insert

    --TODO: refactor this?
    simp [isNClique_iff, IsClique] at SClique ⊢
    apply And.intro
    · intros a ha b hb hab
      simp_all
      rcases ha with ⟨ha, ha_mem⟩
      rcases hb with ⟨hb, hb_mem⟩
      simp[Set.Pairwise] at SClique
      have _ := SClique.left a ha ha_mem b hb hb_mem hab
      tauto
    · exact SClique.right

    simp_all

theorem Lemma₂ : G.isXYGraph x.succ y.succ →  G.degree p ≤ RamseyOld x y.succ ∧ G.degree p + RamseyOld x.succ y ≥ N := by
  intros xyGraphProp
  -- apply And.intro
  apply And.intro
  · have H₁isXYGraph: (H₁ G p).isXYGraph x y.succ := by
      have indNum_mono := indNumMono G p
      have cliqueNum_mono := cliqueNumMono G p
      simp [isXYGraph] at xyGraphProp ⊢
      simp[← Nat.sub_lt_sub_iff_right (oneLeCN G)] at xyGraphProp
      simp [lt_of_le_of_lt indNum_mono xyGraphProp.right]
      linarith

    have tmp := (cardLERamseyOld (H₁ G p) x y.succ H₁isXYGraph)
    rw [card_neighborSet_eq_degree] at tmp
    exact tmp

  · have H₁isXYGraph_C : (H₁ Gᶜ p)ᶜ.isXYGraph x.succ y := by
      have indNum_mono := indNumMono Gᶜ p
      have cliqueNum_mono := cliqueNumMono Gᶜ p
      rw [Lemma₁] at xyGraphProp ⊢
      simp [isXYGraph] at xyGraphProp ⊢
      simp[← Nat.sub_lt_sub_iff_right (oneLeCN Gᶜ)] at xyGraphProp
      simp [lt_of_le_of_lt cliqueNum_mono xyGraphProp.left]
      linarith

    simp [isXYGraph] at H₁isXYGraph_C
    have tmp := (cardLERamseyOld (H₁ Gᶜ p)ᶜ x.succ y H₁isXYGraph_C)
    rw [card_neighborSet_eq_degree] at tmp
    have _ := G.degree_compl
    simp_all
    linarith

lemma G_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v : Fin N.succ, G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.s_i x y j * v_i x y j := by
  rw [sum_degree_eq_sum_over_degrees]
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.s_i x y j > 0) , G.s_i x y j * v_i x y j)
  push_cast
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, v_i]
    use a
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ a₂ h
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, v_i] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [v_i]
    intros a
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[tmp, mul_comm]
    by_cases aeq0 : G.degree a = 0
    right
    exact aeq0
    left
    simp[s_i, v_i]
    suffices : (Finset.univ.filter (fun v ↦ G.degree v = G.degree a)) = Finset.univ.filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw[tmp]
    norm_cast
    tauto
  · rw [Finset.sum_filter (λ j ↦ G.s_i x y j > 0) (λ j ↦ ↑(G.s_i x y j) * v_i x y j)]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    left
    assumption

lemma G_vertCount_eq (hxy : G.isXYGraph x.succ y.succ) : N.succ = (∑ i ∈ Finset.range (σ_G hxy + 1), G.s_i x y i ) := by
  transitivity Fintype.card (Fin N.succ)
  simp
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.s_i x y j > 0) , G.s_i x y j)
  rw [@num_of_vertices_eq_sum_over_degrees (Fin N.succ) G]
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, v_i]
    use a
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ a₂ h
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, v_i] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [v_i]
    intros a
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[s_i, v_i]
    suffices : Finset.univ.filter (fun v ↦ G.degree v = G.degree a) = Finset.univ.filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw [tmp]
    norm_cast
    tauto
  · rw [Finset.sum_filter (λ j ↦ G.s_i x y j > 0) (λ j ↦ (G.s_i x y j))]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    simp[s_i]
    replace h := Finset.card_eq_zero.mpr h
    exact h.symm

lemma H1_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v : ↑(G.neighborSet p), G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.t_i x y j p * v_i x y j := by
  suffices : ∑ v : ↑(G.neighborSet p), G.degree v = ∑ d in Finset.image (λ v ↦ G.degree v) (G.neighborFinset p), d * ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)).card
  rw[this]
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.t_i x y j p > 0) , G.t_i x y j p * v_i x y j)
  push_cast
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intros a ha
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, v_i]
    use a
    refine ⟨ha, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ _ a₂ _
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, v_i] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    refine ⟨ha.left, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [v_i]
    intros a ha
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[tmp, mul_comm]
    by_cases aeq0 : G.degree a = 0
    right
    exact aeq0
    left
    simp[t_i, v_i]
    suffices : ((G.neighborFinset p).filter (fun v ↦ G.degree v = G.degree a)) = (G.neighborFinset p).filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw[tmp]
    norm_cast
    tauto
  · rw [Finset.sum_filter (λ j ↦ G.t_i x y j p > 0) (λ j ↦ ↑(G.t_i x y j p) * v_i x y j)]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    left
    assumption

  have h_sigma : (∑ v: (G.neighborSet p), G.degree v) =
  ∑ p in Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦  G.degree v = d)), G.degree p.2 := by
    apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
    intros a ha
    refine ⟨?_, ha⟩
    use a
    intros p _ _ _ _ _
    use p.2
    simp_all

  rw [h_sigma]

  have h_inner_sum : ∀ d ∈ ((G.neighborFinset p).image (λ v ↦ G.degree v)),
  (∑ v in ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree v) =
  d * ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)).card := by
    intros d hd
    have h : ∀ v ∈ ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree v = d := by
      intros v hv
      rw [Finset.mem_filter] at hv
      rcases hv with ⟨hv1, hv2⟩
      rw [hv2]
    rw [Finset.sum_const_nat h]
    apply mul_comm

  suffices:
    (∑ p in Finset.sigma  ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree p.2) =
    (∑ d in ((G.neighborFinset p).image (λ v ↦ G.degree v)), ∑ v in (G.neighborFinset p).filter (λ v ↦  G.degree v = d), G.degree v)
  rw[this]
  apply Finset.sum_congr rfl h_inner_sum
  simp [Finset.sum_sigma']

lemma H1_vertCount_eq (hxy : G.isXYGraph x.succ y.succ) : ↑(Fintype.card ↑(G.neighborSet p)) = (∑ i ∈ Finset.range (σ_G hxy + 1), G.t_i x y i p) := by
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.t_i x y j p > 0) , G.t_i x y j p)
  transitivity (∑ d ∈ (G.neighborFinset p).image (fun v ↦ G.degree v), ((G.neighborFinset p).filter (fun v ↦ G.degree v = d)).card)
  · transitivity (∑ v : (G.neighborSet p), 1)
    simp
    have h_sigma : (∑ v: (G.neighborSet p), 1) =
      ∑ p in Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦  G.degree v = d)), 1 := by
        apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
        intros a ha
        refine ⟨?_, ha⟩
        use a
        intros p _ _ _ _ _
        use p.2
        simp_all
    rw [h_sigma]
    suffices:
        (∑ p in Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = d)), 1) =
        (∑ d in ((G.neighborFinset p).image (λ v ↦ G.degree v)), ∑ v in (G.neighborFinset p).filter (λ v ↦  G.degree v = d), 1)
    rw[this]
    apply Finset.sum_congr rfl (by simp)
    simp [Finset.sum_sigma']
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a ha
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, v_i]
    use a
    refine ⟨ha, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ _ a₂ _
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, v_i] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    refine ⟨ha.left, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [v_i]
    intros a ha
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[t_i, v_i]
    suffices : ((G.neighborFinset p).filter (fun v ↦ G.degree v = G.degree a)) = (G.neighborFinset p).filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw[tmp]
    norm_cast
    tauto
  · rw [Finset.sum_filter (λ j ↦ G.t_i x y j p > 0) (λ j ↦ G.t_i x y j p)]
    simp[t_i, v_i]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    simp[h]


variable {G}

theorem Prop₁ (hxy : G.isXYGraph x.succ y.succ):
N.succ ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 - (σ_G hxy) ∧ (σ_G hxy) ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 -  N.succ := by
  obtain ⟨p, hp⟩ := G.exists_minimal_degree_vertex
  have ⟨ha, hb⟩ := (Lemma₂ G p hxy)
  simp[σ_G]
  apply And.intro
  rw[Nat.le_sub_iff_add_le (by simp; linarith)]
  have vLERamseyOld : G.minDegree ≤ RamseyOld x y.succ := by rw [← hp] at ha; exact ha
  rw [← Nat.add_sub_assoc vLERamseyOld]
  simp_all
  linarith

  suffices :  0 ≤ (RamseyOld x.succ y + G.minDegree - N)
  have temp : N ≤ RamseyOld x.succ y + G.minDegree := by
    simp [← hp, Nat.sub_le_iff_le_add] at hb
    linarith
  have temp1 : RamseyOld x y.succ ≤ RamseyOld x y.succ := by simp
  have temp2 := Nat.add_le_add temp1 this
  rw [← Nat.add_sub_assoc temp (RamseyOld x y.succ)] at temp2
  rw [← Nat.add_assoc (RamseyOld x y.succ) (RamseyOld x.succ y) G.minDegree] at temp2
  have temp3: N ≤ RamseyOld x y.succ + RamseyOld x.succ y := by linarith
  rw [← Nat.sub_add_comm temp3]
  assumption
  rw [← hp] at hb; simp [hb]

variable (x y i)

-- theorem Prop₂ (hxy : G.isXYGraph x.succ y.succ) (hp: G.degree p = v_i x y i) : 2 * ((↑(e₂ G p)  - ↑(e₁ G p))) =
-- RamseyOld x y.succ * (↑N.succ - 2 * ↑(RamseyOld x y.succ) + 2 * ↑i) + ∑ j in Finset.range (σ_G hxy).succ, (↑j : ℤ) * (2 * ↑(t_i G x y j p) - ↑(s_i G x y j)) := by
--   let e := G.edgeFinset.card
--   let lhs := ∑ j in Finset.range (σ_G hxy).succ, (t_i G x y j p) * (v_i x y j)
--   let rhs := ∑ j in Finset.range (σ_G hxy).succ, (s_i G x y j) * (v_i x y j)

--   have count₁ : 2 * e = 2 * (lhs - e₁ G p + e₂ G p) := by
--     unfold lhs
--     rw[← H1_degreeCount_eq]
--     sorry

--   have count₂ : 2 * e = rhs := by
--     norm_cast
--     simp only[e, ← sum_degrees_eq_twice_card_edges]
--     apply G_degreeCount_eq

--   rw [count₁] at count₂

--   have count₂ : 2 * (G.e₂ p - G.e₁ p) = ↑rhs - 2 * (↑lhs : ℤ) := by
--     have tmp : G.e₁ p ≤ lhs := by sorry
--     omega
--   conv at count₂ ↦
--     rhs
--     unfold lhs rhs
--     simp[v_i]

--   --hard to work with under conv, easier to show bijective
--   have part₁ : ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y x_1) * (↑(RamseyOld x (y + 1)) - ↑x_1 : ℤ)
--   =  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (↑(G.s_i x y x_1) * (↑(RamseyOld x (y + 1)): ℤ) - ↑(G.s_i x y x_1) * x_1) := by
--     apply Finset.sum_bij (λ a ha ↦ a) <;> simp
--     intros a ha
--     linarith

--   rw[Finset.sum_sub_distrib] at part₁
--   rw [← Finset.sum_mul] at part₁
--   have tmp₁ : N.succ = (∑ i ∈ Finset.range (σ_G hxy + 1), G.s_i x y i ) := G_vertCount_eq G hxy
--   zify at tmp₁
--   rw [tmp₁.symm] at part₁

--   have part₂ : 2 * ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.t_i x y x_1 p) * (↑(RamseyOld x (y + 1)) - ↑x_1 : ℤ)
--   =  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (2 * ↑(G.t_i x y x_1 p) * (↑(RamseyOld x (y + 1)): ℤ) - 2 * ↑(G.t_i x y x_1 p) * x_1) := by
--     rw[Finset.mul_sum]
--     apply Finset.sum_bij (λ a ha ↦ a) <;> simp
--     intros a ha
--     linarith

--   rw [Finset.sum_sub_distrib] at part₂
--   rw [← Finset.sum_mul] at part₂
--   have tmp₂ : (∑ i ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.t_i x y i p): ℤ) = 2 * v_i x y i := by
--     rw[← hp, ← SimpleGraph.card_neighborSet_eq_degree]
--     rw [H1_vertCount_eq G p hxy]
--     simp [Finset.mul_sum]
--   rw [tmp₂] at part₂

--   rw [part₁, part₂] at count₂
--   rw [count₂]
--   rw [sub_sub_sub_comm]
--   rw [sub_sub_eq_add_sub, add_sub_assoc]
--   rw [← Finset.sum_sub_distrib]

--   have part₁ : ↑N.succ * ↑(RamseyOld x (y + 1)) - (2 * ↑(v_i x y i)) * ↑(RamseyOld x (y + 1)) =  ↑(RamseyOld x y.succ) * (↑N.succ - 2 * ↑(RamseyOld x y.succ) + 2 * ↑i : ℤ) := by
--     rw [v_i]
--     rw [← mul_sub_right_distrib]
--     linarith

--   have part₂ : ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (2 * ↑(G.t_i x y x_1 p) * ↑x_1 - ↑(G.s_i x y x_1) * ↑x_1 : ℤ) = ∑ j ∈ Finset.range (σ_G hxy).succ, ↑j * (2 * ↑(G.t_i x y j p) - ↑(G.s_i x y j): ℤ) := by
--     apply Finset.sum_bij (λ a ha ↦ a) <;> simp
--     intros a ha
--     linarith

--   rw [part₂]
--   simp at part₁
--   rw [part₁]
--   simp

-- theorem Corollary₂  (hxy : G.isXYGraph 3 y.succ) (hp: G.degree p = v_i 2 y i) :
--   2 * e₂ G p = ↑y * ((↑N.succ) - 2 * ↑y + 2 * ↑i) + ∑ j in Finset.range (σ_G hxy).succ, (↑j : ℤ) * (2 * ↑ (t_i G 2 y j p) - ↑(s_i G 2 y j)) := by
--   have Prop₂ := Prop₂ 2 y p i hxy hp
--   suffices tmp: G.e₁ p = 0 ∧ RamseyOld 2 y.succ = y
--   rw [tmp.left, tmp.right] at Prop₂
--   simp_all
--   apply And.intro
--   · simp [Finset.filter_eq_empty_iff]
--     by_contra H
--     simp at H
--     obtain ⟨⟨u, v⟩, uvProp⟩ := H
--     simp [isXYGraph] at hxy
--     suffices : (G.H₁ p).cliqueNum < 2

--     simp [cliqueNum2CliqueFree, CliqueFree, isNClique_iff] at this
--     have contra := this {u,v}
--     simp [IsClique] at contra uvProp
--     simp [uvProp] at contra
--     rw [Finset.card_insert_of_not_mem] at contra
--     trivial

--     by_contra
--     simp_all

--     have H₁CliqueNum_UB := cliqueNumMono G p
--     simp[← Nat.sub_lt_sub_iff_right (oneLeCN G)] at hxy
--     linarith

--   · have tmp := GraphRamsey2 y
--     simp [GraphRamsey2RamseyOld] at tmp
--     exact tmp
