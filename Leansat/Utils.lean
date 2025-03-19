import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

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

-- @[export readInput_Int]
def readInput_Int(input : List Int) : List (Fin 2) :=
  input.map (λ x ↦
    if x > 0 then 1  -- Connected (>0) maps to 1
    else 0 -- Disconnected and unknown (<=0) map to 0
  )
@[export readInput_Str]
def readInput_Str(input : String) : List (Fin 2) :=
  readInput_Int ((input.splitOn " ").map (λ str ↦ str.toInt!))

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

theorem readInput_Int_correct : ∀ (input : List Int) (i : ℕ), i < (readInput_Int input).length →
  ((input.get! i) > 0 → (readInput_Int input).get! i = 1) ∧
  ((input.get! i) ≤ 0 → (readInput_Int input).get! i = 0) := by
  intros input i i_bound
  simp [readInput_Int] at i_bound
  induction input generalizing i with
  | nil => simp_all
  | cons hd tl ih =>
    refine ⟨?_, ?_⟩
    all_goals
      intros h
      by_cases ieq0 : i = 0
    · simp_all[readInput_Int]
    swap
    · simp_all[readInput_Int]
    all_goals
      have tmp : ((hd :: tl).get! i) = (tl.get! (i - 1)) := by
        have _ := (hd::tl).get_ith_eq_tail_get_pred i ieq0 i_bound (by simp[readInput_Int])
        tauto
      have i_pred_bound: i - 1 < tl.length := by rw[← Nat.succ_pred ieq0, List.length, Nat.succ_lt_succ_iff] at i_bound; exact i_bound
      rcases ih i.pred i_pred_bound with ⟨ih1, ih2⟩
      have tmp' := List.get_ith_eq_tail_get_pred (readInput_Int (hd :: tl)) i ieq0 (by simp[readInput_Int]; exact i_bound) (by simp[readInput_Int])
      rw [tmp] at h
    · rw [← ih1 h]
      tauto
    · rw [← ih2 h]
      tauto


theorem readInput_Int_correct' : ∀ (input : List Int) (i : ℕ), i < (readInput_Int input).length →
  ((readInput_Int input).get! i = 1 →  (input.get! i) > 0) ∧
  ((readInput_Int input).get! i = 0 →  (input.get! i) ≤ 0) := by
  intros input i i_bound
  simp [readInput_Int] at i_bound
  induction input generalizing i with
  | nil => simp_all
  | cons hd tl ih =>
    refine ⟨?_, ?_⟩
    all_goals
      intros h
      by_cases ieq0 : i = 0

    · simp_all[readInput_Int]
    swap
    · simp_all[readInput_Int]
    all_goals
      have tmp : (hd :: tl)[i]! = (tl)[i-1]! := by
        have _ := (hd::tl).get_ith_eq_tail_get_pred i ieq0 i_bound (by simp[readInput_Int])
        simp_all
      have i_pred_bound: i - 1 < tl.length := by rw[← Nat.succ_pred ieq0, List.length, Nat.succ_lt_succ_iff] at i_bound; exact i_bound
      have tmp' := List.get_ith_eq_tail_get_pred (readInput_Int (hd :: tl)) i ieq0 (by simp[readInput_Int]; exact i_bound) (by simp[readInput_Int])
      rcases ih i.pred i_pred_bound with ⟨ih1, ih2⟩
      simp only [tmp'] at h
    · have tmp'' := ih1 h
      simp_all
    · have tmp'' := ih2 h
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
-- #eval edge2Ver 1 3


-- Function to compute the index in the adjacency list for the edge between vertices i and j
def ver2Edge (i j : ℕ) (H : i < j): ℕ :=
  i + j * (j - 1) / 2

def graphOrderFromListLen (N : ℕ) : ℕ :=
  (1 + Nat.sqrt (1 + 8 * N) / 2)

-- #eval graphOrderFromListLen 6

def adjListToAdjMat (adjList : List (Fin 2)) : Matrix (Fin (graphOrderFromListLen adjList.length)) (Fin (graphOrderFromListLen adjList.length)) (Fin 2) :=
  λ i j =>
  if H : i > j then adjList.get! (ver2Edge j i H)
  else if H : j > i then adjList.get! (ver2Edge i j H)
  else 0

theorem isAdjMat (adjList : List (Fin 2)) : (adjListToAdjMat adjList).IsAdjMatrix := by
  constructor
  · intros i j
    match (adjListToAdjMat adjList i j) with
    | 0 => norm_num
    | 1 => norm_num
  · simp [Matrix.IsSymm.ext_iff]
    intros i j
    simp [adjListToAdjMat]
    by_cases H : i = j
    · simp_all
    · push_neg at H
      rw [ne_iff_lt_or_gt] at H
      rcases H with h | h
      · have h' := lt_asymm h; simp[h, h']
      · have h' := lt_asymm h; simp_all
  · intros i
    simp [adjListToAdjMat]

def SimpleGraph.mk_mat(adjList : List (Fin 2)) : SimpleGraph (Fin (graphOrderFromListLen adjList.length)) :=
  Matrix.IsAdjMatrix.toGraph (isAdjMat adjList)

instance mk_mat_DecidableRelAdj (adjList : List (Fin 2)): DecidableRel (SimpleGraph.mk_mat (adjList)).Adj := by
  simp[SimpleGraph.mk_mat]
  infer_instance

def SimpleGraph.mk_list (adjList : List (Fin 2)) : SimpleGraph (Fin (graphOrderFromListLen adjList.length)) :=

  SimpleGraph.mk (λ v w ↦ if H : v < w then adjList.get! (ver2Edge v w H) = 1
  else if H : w < v then adjList.get! (ver2Edge w v H) = 1
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
instance mk_List_DecidableRelAdj (adjList : List (Fin 2)): DecidableRel (SimpleGraph.mk_list (adjList)).Adj := by
  simp[SimpleGraph.mk_list]
  infer_instance
