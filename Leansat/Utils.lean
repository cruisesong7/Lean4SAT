import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Finite
--------------------------------------------------
/-
The expected input format is the upper triangular portion of the edge adjacency matrix,
provided in column-by-column order. In this format, only the entries where the row index
is less than the column index (i.e., above the main diagonal) are included.

For a 3×3 matrix, the valid positions (edges) are:
  - Edge between vertex 1 and vertex 2 (position (1,2))
  - Edge between vertex 1 and vertex 3 (position (1,3))
  - Edge between vertex 2 and vertex 3 (position (2,3))

For example, suppose the edge assignments are:
  - Edge (1,2): "1"  (a positive edge, which maps to some 1)
  - Edge (1,3): "-1" (a negative edge, which maps to some 0)
  - Edge (2,3): "0"  (an unknown edge, which maps to none)

Then, the input list should be:
  ["1", "-1", "0"]

The corresponding full matrix representation of the symmetric edge adjacency is:

      v1   v2   v3
  v1   -    1   -1
  v2   1    -    0
  v3  -1    0    -

Here, the upper triangle (above the main diagonal) is provided by the input,
and the lower triangle is its mirror image. The diagonal is typically omitted.
-/
@[export readInput]
def readInput (input : List String) : List (Option (Fin 2)) :=
  input.map (λ str ↦
    if str.toInt!  = 0 then none  -- Zero maps to None (unknown)
    else some (if str.toInt! > 0 then 1 else 0)  -- Positive: Some 1, Negative: Some 0
  )

-- #eval readInput ([])
-- #eval readInput ("1 -2 3".splitOn " ") -- Expected: [some 1, some 0, some 1]
-- #eval readInput ("1 2 3".splitOn " ") -- Expected: [some 1, some 1, some 1]
-- #eval readInput ("-1 -2 -3".splitOn " ") -- Expected: [some 0, some 0, some 0]
-- #eval readInput ("1 -2 3 4".splitOn " ") -- Expected: [some 1, some 0, some 1]

lemma List.get_ith_eq_tail_get_pred {α} [Inhabited α]:
∀ (l : List α) (i : ℕ), i ≠ 0 → i < l.length → l ≠ [] → l.get! i = (l.tail).get! i.pred := by
  intros l i h
  cases l with
  | nil => simp_all
  | cons hd tl =>
    intros
    have tmp := List.get!_cons_succ tl hd i.pred
    have tmp' : i.pred + 1 = i := by simp[Nat.sub_one_add_one h]
    rw [tmp'] at tmp
    simp only [tmp, List.tail]

theorem readInput_correct : ∀ (input : List String) (i:ℕ ), i < (readInput input).length →
  ((input.get! i).toInt! > 0 → (readInput input).get! i = some 1) ∧
  ((input.get! i).toInt! < 0 → (readInput input).get! i = some 0) ∧
  ((input.get! i).toInt! = 0 → (readInput input).get! i = none) := by
  intros input i i_bound
  simp [readInput] at i_bound
  induction input generalizing i with
  | nil => simp_all
  | cons hd tl ih =>
    refine ⟨?_, ?_, ?_⟩
    all_goals
      intros h
      by_cases ieq0 : i = 0
    · simp_all[readInput]; by_contra; simp_all
    swap
    · simp_all[readInput]; by_cases hd.toInt! = 0 <;> simp_all; linarith
    pick_goal 3
    · simp_all[readInput]
    all_goals
      have tmp : ((hd :: tl).get! i).toInt! = (tl.get! (i - 1)).toInt! := by
        have _ := (hd::tl).get_ith_eq_tail_get_pred i ieq0 i_bound (by simp[readInput])
        simp_all
      have i_pred_bound: i - 1 < tl.length := by rw[← Nat.succ_pred ieq0, List.length, Nat.succ_lt_succ_iff] at i_bound; exact i_bound
      rcases ih i.pred i_pred_bound with ⟨ih1, ih2, ih3⟩
      have tmp' := List.get_ith_eq_tail_get_pred (readInput (hd :: tl)) i ieq0 (by simp[readInput]; exact i_bound) (by simp[readInput])
      rw [tmp] at h
    · rw [← ih1 h]
      tauto
    · rw [← ih2 h]
      tauto
    · rw [← ih3 h]
      tauto

theorem readInput_correct' : ∀ (input : List String) (i:ℕ ), i < (readInput input).length →
  ((readInput input).get! i = some 1 →  (input.get! i).toInt! > 0) ∧
  ((readInput input).get! i = some 0 →  (input.get! i).toInt! < 0) ∧
  ((readInput input).get! i = none →  (input.get! i).toInt! = 0) := by
  intros input i i_bound
  simp [readInput] at i_bound
  induction input generalizing i with
  | nil => simp_all
  | cons hd tl ih =>
    apply And.intro
    rotate_left
    apply And.intro
    rotate_right
    all_goals
      intros h
      by_cases ieq0 : i = 0

    · simp_all[readInput]
    swap
    · simp_all[readInput]
      by_cases hd.toInt! = 0 <;> simp_all
      have _ :=  lt_or_eq_of_le h
      simp_all
    pick_goal 3
    · simp_all[readInput]
    all_goals
      have tmp : (hd :: tl)[i]!.toInt! = (tl)[i-1]!.toInt! := by
        have _ := (hd::tl).get_ith_eq_tail_get_pred i ieq0 i_bound (by simp[readInput])
        simp_all
      have i_pred_bound: i - 1 < tl.length := by rw[← Nat.succ_pred ieq0, List.length, Nat.succ_lt_succ_iff] at i_bound; exact i_bound
      have tmp' := List.get_ith_eq_tail_get_pred (readInput (hd :: tl)) i ieq0 (by simp[readInput]; exact i_bound) (by simp[readInput])
      rcases ih i.pred i_pred_bound with ⟨ih1, ih2, ih3⟩
      simp only [tmp'] at h
    · have tmp'' := ih1 h
      simp_all
    · have tmp'' := ih2 h
      simp_all
    · have tmp'' := ih3 h
      simp_all

--------------------------------------------------
-- Function to compute the vertices (i, j) associated with the k-th edge
def edge2Ver (k N : ℕ) : Option (ℕ × ℕ) :=
 if k ≠ 0 ∧ k ≤ N then
    let j :=  (Nat.sqrt (1 + 8 * (k - 1)) + 1) / 2
    if j < N then
      let i := k - 1 - (j * (j - 1)) / 2
      if i < j then
        some (i, j)
      else
        none
    else
      none
  else
    none
#eval edge2Ver 1 3


-- Function to compute the index in the adjacency list for the edge between vertices i and j
def ver2Edge (i j : Nat) (H : i < j): Nat :=
  i + j * (j - 1) / 2 + 1

-- def ver2EdgeMat (N: Nat) : Matrix (Fin N) (Fin N) Nat := λ i j ↦

-- revise the order of simplegraph

def graphMk (adjList : List (Option (Fin 2))) : SimpleGraph (Fin ((adjList.length)*(adjList.length)/2)) :=

  SimpleGraph.mk (λ v w ↦ if H : v < w then adjList.get! (ver2Edge v w H) = some 1
  else if H : w < v then adjList.get! (ver2Edge w v H) = some 1
  else False) -- neq -> v w = 1 or w v = 1
  (by
    -- Prove the symmetric property (undirected graph)
    intros v w Hvw
    by_cases wltv : w < v
    · have not_vltw : ¬ v < w := lt_asymm wltv
      simp_all
    · by_cases vneqw : v = w
      · simp_all
      · have vltw : v < w := Ne.lt_of_le (vneqw) (le_of_not_lt wltv)
        simp_all
  )
  (by
    -- Prove the irreflexive property (no self-loops)
    intro x H
    simp_all
  )
-- #eval (graphMk (readInput ("1 -2 3".splitOn " "))).edgeFinset

-- theorem graphMk_correct (adjList : List (Option (Fin 2))) :
--   let G := graphMk adjList
--   ∀ (v w : Fin adjList.length), G.Adj v w ↔ v ≠ w ∧ if v < w then (adjList.get! (ver2Edge v w)) = some 1
--   else  (adjList.get! (ver2Edge w v)) = some 1 := by simp_all [graphMk]

-- -- Function to compute the index in the adjacency list for the edge between vertices i and j
-- def ver2Edge (i j : Nat) (H: i<j): Nat :=
--   i + j * (j - 1) / 2 + 1



-- #eval ver2Edge 2 3
-- #eval ver2Edge 1 3

-- def graphMk (adjList : List (Option (Fin 2))) : SimpleGraph (Fin adjList.length) :=

--   SimpleGraph.mk (λ v w ↦ match Nat.lt_trichotomy v w with
--     | Or.inl H => sorry
--     | Or.inr (Or.inl H) =>
--     | Or.inr (Or.inr H) =>
--   end)


-- -- #eval (graphMk (readInput ("1 -2 3".splitOn " "))).edgeFinset

-- theorem graphMk_correct (adjList : List (Option (Fin 2))) :
--   let G := graphMk adjList
--   ∀ (v w : Fin adjList.length), G.Adj v w ↔ (v < w ∧ adjList.get! (ver2Edge v w) = some 1)
--   ∨ (w < v ∧ adjList.get! (ver2Edge w v) = some 1 ) := by simp_all [graphMk]


  --  (v < w ∧ adjList.get! (ver2Edge v w ) = some 1)
  -- ∨ (w < v ∧ adjList.get! (ver2Edge w v) = some 1 ) )-- neq -> v w = 1 or w v = 1
  -- (by
  --   -- Prove the symmetric property (undirected graph)
  --   intros v w Hvw
  --   rcases Hvw with left | right
  --   exact Or.inr left
  --   exact Or.inl right
  -- )
  -- (by
  --   -- Prove the irreflexive property (no self-loops)
  --   intro x H
  --   simp_all
  -- )
