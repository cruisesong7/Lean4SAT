import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.AffineSpace.Combination


--------------------------------------------------

-- Function to parse a partial assignment string and return a List of Option (Fin 2)
def readInput (input : List String) : List (Option (Fin 2)) :=
  input.map (λ str =>
    if str.toInt!  = 0 then none  -- Zero maps to None (unknown)
    else some (if str.toInt! > 0 then 1 else 0)  -- Positive: Some 1, Negative: Some 0
  )

#eval readInput ("1 -2 3".splitOn " ") -- Expected: [some 1, some 0, some 1]
#eval readInput ("1 2 3".splitOn " ") -- Expected: [some 1, some 1, some 1]
#eval readInput ("-1 -2 -3".splitOn " ") -- Expected: [some 0, some 0, some 0]
#eval readInput ("1 -2 3 4".splitOn " ") -- Expected: [some 1, some 0, some 1]

lemma List.get_ith_eq_tail_get_pred {α}[Inhabited α]: ∀ (l : List α) (i:ℕ), i ≠ 0 → i < l.length → l ≠ []
  → l.get! i = (l.tail).get! i.pred := by
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
    apply And.intro
    rotate_left
    apply And.intro
    rotate_right
    all_goals
      intros h
      by_cases ieq0 : i = 0
    · simp_all[readInput]; by_contra; simp_all
    swap
    · simp_all[readInput]; by_cases hd.toInt! = 0 <;> simp_all; linarith
    pick_goal 3
    · simp_all[readInput]
    all_goals
      simp_all
      have tmp : (hd :: tl)[i]!.toInt! = (tl)[i-1]!.toInt! := by
        have _ := (hd::tl).get_ith_eq_tail_get_pred i ieq0 i_bound (by simp[readInput])
        simp_all
      have i_pred_bound: i - 1 < tl.length := by rw[← Nat.succ_pred ieq0, Nat.succ_lt_succ_iff] at i_bound; exact i_bound
      rcases ih i.pred i_pred_bound with ⟨ih1, ih2, ih3⟩
      have tmp' := List.get_ith_eq_tail_get_pred (readInput (hd :: tl)) i ieq0 (by simp[readInput]; exact i_bound) (by simp[readInput])
      simp at tmp'
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

    · simp_all[readInput]; by_cases hd.toInt! = 0 <;> simp_all
    swap
    · simp_all[readInput]
      by_cases hd.toInt! = 0 <;> simp_all
      have _ :=  lt_or_eq_of_le h
      simp_all
    pick_goal 3
    · simp_all[readInput]
    all_goals
      simp_all
      have tmp : (hd :: tl)[i]!.toInt! = (tl)[i-1]!.toInt! := by
        have _ := (hd::tl).get_ith_eq_tail_get_pred i ieq0 i_bound (by simp[readInput])
        simp_all
      have i_pred_bound: i - 1 < tl.length := by rw[← Nat.succ_pred ieq0, Nat.succ_lt_succ_iff] at i_bound; exact i_bound
      have tmp' := List.get_ith_eq_tail_get_pred (readInput (hd :: tl)) i ieq0 (by simp[readInput]; exact i_bound) (by simp[readInput])
      rcases ih i.pred i_pred_bound with ⟨ih1, ih2, ih3⟩
      simp at tmp'
      simp [tmp'] at h
    · have tmp'' := ih1 h
      simp_all
    · have tmp'' := ih2 h
      simp_all
    · have tmp'' := ih3 h
      simp_all

-- theorem readInput_correct' : ∀ (input : List String) (i:ℕ ), i < (readInput input).length →
--   ((input.get! i).toInt! = 0 → (readInput input).get! i = none) := by
--   intros input i i_bound
--   simp [readInput] at i_bound
--   induction input generalizing i with
--   | nil => simp_all
--   | cons hd tl ih =>
--     intros h
--     by_cases ieq0 : i = 0
--     · simp_all[readInput]
--     · simp_all
--       have tmp : (hd :: tl)[i]!.toInt! = (tl)[i-1]!.toInt! := by
--         have _ := (hd::tl).get_ith_eq_tail_get_pred i ieq0 i_bound (by simp[readInput])
--         simp_all
--       have i_pred_bound: i - 1 < tl.length := by rw[← Nat.succ_pred ieq0, Nat.succ_lt_succ_iff] at i_bound; exact i_bound
--       rw [tmp] at h
--       rw [← ih i.pred i_pred_bound h]
--       have _ := List.get_ith_eq_tail_get_pred (readInput (hd :: tl)) i ieq0 (by simp[readInput]; exact i_bound) (by simp[readInput])
--       simp_all
--       tauto


    --   · simp_all
    --   · simp[readInput]; intro h'; by_contra; simp_all
    -- have temp : i.pred + 1 < tl.length := by s
    -- have temp := ih (by simp h) (i.pred)
    -- by_cases ih' : i < tl.length
    -- induction tl with
    -- | nil => simp_all; exfalso; exact Fin.elim0
    --   · simp_all
    -- · simp_all
    --   by_cases hd.toInt! = 0
    --   · simp_all
    --   · simp_all
    -- · sorry

  -- simp [List.get]
  -- by_cases kval_pos: ((input.splitOn " ").get! i).toInt! > 0
--------------------------------------------------
-- Function to count the number of edges in adjList
def countEdges (adjList : List (Option (Fin 2))) : ℕ := adjList.count (some 1)

-- theorem countEdges_correct (adjList : List (Option (Fin 2))): eq number of postive literals in the string
theorem countEdges_correct (input: List String) : countEdges (readInput input) = (input.countP (λ x => x.toInt! > 0)) := by
  induction input with
  | nil => simp_all[readInput, countEdges]
  | cons hd tl ih =>
    by_cases hd.toInt! > 0
    · have tmp : hd.toInt! > 0 → countEdges (readInput (hd :: tl)) = countEdges (readInput tl) + 1 := by
        intro H
        have tmp := (readInput_correct (hd :: tl) 0 (by simp[readInput])).left H
        simp_all[readInput, countEdges]
      simp_all
    · simp_all[readInput, countEdges, List.count]
      by_cases hd.toInt! = 0 <;> simp_all


-- def countEdges (adjList : List (Option (Fin 2))) : ℕ :=
--   adjList.foldl (λ acc elem =>
--     match elem with
--     | some 1 => acc + 1
--     | _ => acc
--   ) 0

-- lemma List.foldl_add1_nat  (l : List ℕ) (x : ℕ) :
--   List.foldl (λ x y => 0) (x + 1) l = List.foldl (λ x y => 0) x l + 1 := by
--   slim_check
--   induction l with
--   | nil => simp
--   | cons hd tl ih =>
--     simp
--     rw [ih]

-- lemma test (l : List ((Fin 2))) :
--     List.foldl (fun acc elem =>
--         match elem.val with
--         | 1 => acc + 1
--         | _ => acc)
--       1 l =
--       List.foldl (fun acc elem =>
--         match elem.val with
--         | 1 => acc + 1
--         | _ => acc)
--       0 l + 1 := by

-- lemma hd_cons_tail_pos : ∀ (l: List (Option (Fin 2))), l ≠ [] → l.head! = some 1 → countEdges l = countEdges l.tail + 1 := by
--   intros l h h'
--   cases l with
--   | nil => simp_all
--   | cons hd tl =>
--     simp only[countEdges]
--     simp_all
--     have : ∀ l, List.foldl (fun acc (elem : Option (Fin 2)) => match elem with | some 1 => acc + 1 | _ => acc) 1 l
--             = List.foldl (fun acc elem => match elem with | some 1 => acc + 1 | _ => acc) 0 l + 1 := by
--       intros l
--       induction l with
--       | nil => simp
--       | cons hd tl ih =>
--         cases hd with
--         | none => exact ih
--         | some f =>
--           by_cases f = 1
--           · simp_all
--           · simp_all
--     apply this

-- lemma hd_cons_tail_pos': ∀ (l : List String), l ≠ [] → l.head!.toInt! > 0 → countEdges (readInput l) = countEdges (readInput l.tail) + 1 := by
--   intros l h h'
--   cases l with
--   | nil => simp_all
--   | cons hd tl =>
--     by_cases hd_pos: hd.toInt! > 0
--     · simp_all[countEdges,readInput]
--       have tmp := (readInput_correct (hd::tl) 0 (by simp[readInput])).left hd_pos
--       simp_all
--       tauto
--       rw [List.foldr_cons readInput_correct (tl) hd]
--       have _ :
--       List.foldl
--         (fun acc elem =>
--           match elem with
--           | some 1 => acc + 1
--           | x => acc)
--         0 (readInput (hd :: tl)) =
--       List.foldl
--         (fun acc elem =>
--           match elem with
--           | some 1 => acc + 1
--           | x => acc)
--         0 (readInput (tl))  + 1 := by simp_all
--     · simp_all

-- theorem countEdges_correct (input: List String) : countEdges (readInput input) = (input.filter (λ x => x.toInt! > 0)).length := by
--   induction input with
--   | nil => simp_all[readInput, countEdges]
--   | cons hd tl ih =>
--     by_cases hd.toInt! > 0
--     · have tmp : hd.toInt! > 0 → countEdges (readInput (hd :: tl)) = countEdges (readInput tl) + 1 := by
--         intro H
--         have tmp := (readInput_correct (hd :: tl) 0 (by simp[readInput])).left H
--         simp [countEdges]
--         simp at tmp
--         sorry
--       have tmp' : hd.toInt! < 0 → countEdges (readInput (hd :: tl)) = countEdges (readInput tl) := by sorry
--       simp_all
--     · simp_all[readInput, countEdges]
--       by_cases hd.toInt! = 0 <;> simp_all
--------------------------------------------------

-- Function to check if the number of edges is greater than or equal to maxEdge
def isEdgesGT (adjList : List (Option (Fin 2))) (maxEdge : ℕ) : Fin (2) :=
  let numEdges := countEdges adjList
  if numEdges >= maxEdge then 1 else 0

def exampleList : List (Option (Fin 2)):= readInput ("1 -2 3".splitOn " ")

#eval isEdgesGT exampleList 1  -- Expected: 1
#eval isEdgesGT exampleList 2  -- Expected: 1
#eval isEdgesGT exampleList 3  -- Expected: 0

theorem isEdgesGT_correct (adjList : List (Option (Fin 2))) (maxEdge : ℕ) :
  isEdgesGT adjList maxEdge = 1 ↔ countEdges adjList ≥ maxEdge := by simp [isEdgesGT]
--------------------------------------------------

-- Function to compute the index in the adjacency list for the edge between vertices i and j
def ver2Edge (i j : Nat) : Nat :=
  i + j * (j - 1) / 2 + 1
-- injective

theorem ver2Edge_correct (i j : ℕ) : i < j → Set.InjOn (ver2Edge) (Finset.range j) := by
  intro iLtj
  intros x x_in y y_in h
  sorry
-- Function to check if an edge exists between vertices i and j using the adjacency list
def isEdge (adjList : List (Option (Fin 2))) (i j : ℕ) : Bool :=
  adjList.get! (ver2Edge i j - 1) == some 1

def isEdge' (input : List String) (i j : ℕ) : Bool :=
 (input.get! (ver2Edge i j - 1) ).toInt!> 0

-- Function to count the number of triangles in the graph
def countTriangles (adjList : List (Option (Fin 2))) (N : ℕ) : ℕ :=
  let vertices := List.range N  -- List of vertices from 0 to N-1
  let triples := vertices.sublistsLen 3  -- Get all combinations of 3 vertices
  triples.countP (fun triple =>
    match triple with
    | [i, j, k] =>
      isEdge adjList i j ∧ isEdge adjList j k ∧ isEdge adjList i k
    | _ => false  -- This case won't occur because we're using sublistsLen 3
  )

def countTriangles' (input : List String) (N : ℕ) : ℕ :=
  let vertices := List.range N  -- List of vertices from 0 to N-1
  let triples := vertices.sublistsLen 3  -- Get all combinations of 3 vertices
  triples.countP (fun triple =>
    match triple with
    | [i, j, k] =>
      isEdge' input i j ∧ isEdge' input j k ∧ isEdge' input i k
    | _ => false  -- This case won't occur because we're using sublistsLen 3
  )

def adjList := [some (1:Fin 2), some (0:Fin 2), some (1:Fin 2), some (1:Fin 2), some (1:Fin 2), some (1:Fin 2)]  -- Triangle between vertices 0, 1, and 2
#eval countTriangles adjList 4  -- Output: 1

-- theorem countTriangles_correct (input : List String) (N : ℕ) :
--   let adjList := readInput input
--   countTriangles adjList N = countTriangles' input N := by
--   induction adjList with
--   | nil => simp_all[readInput, countTriangles, countTriangles']
--   | cons hd tl ih =>
--     by_cases hd.toInt! > 0
--     · have tmp : hd.toInt! > 0 → countEdges (readInput (hd :: tl)) = countEdges (readInput tl) + 1 := by
--         intro H
--         have tmp := (readInput_correct (hd :: tl) 0 (by simp[readInput])).left H
--         simp_all[readInput, countEdges]
--       simp_all
--     · simp_all[readInput, countEdges, List.count]
--       by_cases hd.toInt! = 0 <;> simp_all
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
--------------------------------------------------

#eval ver2Edge 0 1

-- lemma helper: ∀ k :ℕ,
--  (1 + (1 + (k - 1) * 8).sqrt) / 2 * ((1 + (1 + (k - 1) * 8).sqrt) / 2 - 1) / 2 ≤ k -1 := by
--  omega
--   intro k
--   intro k s
--   decide

-- change to ->
-- theorem edge2Ver_correct: ∀ (i j k N: ℕ),
-- (edge2Ver k N = some (i, j)) ↔ ver2Edge i j = k := by
--   intro i j k N
--   simp [edge2Ver, ver2Edge]

--   by_cases cond : ( k ≠ 0 ∧ k ≤ N ∧ k - 1 - ((1 + 8 * (k - 1)).sqrt + 1) / 2 * (((1 + 8 * (k - 1)).sqrt + 1) / 2 - 1) / 2 < ((1 + 8 * (k - 1)).sqrt + 1) / 2  ∧ ((1 + 8 * (k - 1)).sqrt + 1) / 2 < N)
--   · rcases cond with ⟨kne0, kltN, iltj, jltN⟩
--     simp [kne0, kltN, iltj, jltN]
--     apply Iff.intro
--     · intro h
--       rw [← h.left, ← h.right]
--       ring_nf
--       let x := (1 + (1 + (k - 1) * 8).sqrt) / 2
--       let y := x * (x - 1) / 2
--       change 1 + (k - 1 - y) + y = k
--       have h' := helper k (by by_contra; simp_all); change y ≤ k - 1 at h'
--       have h'': k - 1 - y + y = k - 1 := by simp [Nat.sub_add_cancel h']
--       have kge1 : 1 ≤ k := by by_contra; simp_all
--       rw [Nat.add_assoc 1 (k - 1 - y) y, h'',Nat.add_sub_of_le kge1 ]
--     · sorry
--   · simp at cond
--     sorry

--------------------------------------------------
-- -- Define a structure that includes the adj matrix and its properties
-- structure AdjMat (N : ℕ) where
--   (mat : Matrix (Fin N) (Fin N) (Fin 2))
--   (isSymm : mat.IsSymm)
--   (isIrrefl : ∀ i, mat i i = 0)

-- -- #check SimpleGraph.mk

-- -- Symmetrically extend an upper triangular adjacency matrix and prove its properties
-- def extendAdjMat {N : ℕ} (adjMatrix : Matrix (Fin N) (Fin N) (Fin 2)) : (AdjMat N ):=
--   let completedMatrix := λ i j =>
--     if i == j then 0  -- diagonal
--     else if j > i then adjMatrix i j  -- upper triangule
--     else adjMatrix j i  -- lower triangule
--   {
--     mat := completedMatrix,
--     isSymm := by {
--       simp [Matrix.IsSymm.ext_iff]
--       intros i j
--       simp [completedMatrix]
--       by_cases ieqj : i = j
--       · simp_all
--       · rw [← ne_eq] at ieqj
--         simp [ieqj, Ne.symm]
--         rw [ne_iff_lt_or_gt] at ieqj
--         rcases ieqj with h|h
--         · simp_all; intro h'; have h'' := lt_asymm h ; contradiction
--         · simp_all; have h' := lt_asymm h; simp [h']
--     },
--     isIrrefl := by simp[completedMatrix]
--   }

-- def graphMk (adj2DArr : Array (Array (Fin 2))) : SimpleGraph (Fin adj2DArr.size) :=
--   let adjMatrix := extendAdjMat (arrayToMatrix adj2DArr)
--   let isSymm := adjMatrix.isSymm
--   let isIref := adjMatrix.isIrrefl
--   SimpleGraph.mk (λ v w => adjMatrix.mat v w = 1) -- neq -> v w = 1 or w v = 1
--   (by
--     -- Prove the symmetric property (no self-loops)
--     intros x y
--     simp [Matrix.IsSymm.ext_iff] at isSymm
--     simp_all
--   )
--   (by
--     -- Prove the irreflexive property (undirected graph)
--     intros x y
--     simp_all
--   )

--   def graphMk' (adjList :  List (Option (Fin 2))) : SimpleGraph (Fin adjList.length) :=
--   SimpleGraph.mk (λ v w => adjList.get v w = 1) -- neq -> v w = 1 or w v = 1
--   (by
--     -- Prove the symmetric property (no self-loops)
--     intros x y
--     simp [Matrix.IsSymm.ext_iff] at isSymm
--     simp_all
--   )
--   (by
--     -- Prove the irreflexive property (undirected graph)
--     intros x y
--     simp_all
--   )
-- open Finset

-- theorem graphMk_correct (adj2DArr : Array (Array (Fin 2))) :
--   let G := graphMk adj2DArr
--   let adjMatrix := extendAdjMat (arrayToMatrix adj2DArr)
--   ∀ (v w : Fin adj2DArr.size), G.Adj v w → adjMatrix.mat v w = 1 := by
--   intros G adjMatrix v w h_adj
--   simp [G, graphMk] at h_adj
--   simp [adjMatrix]
--   exact h_adj

-- -- Function to check if the graph has no fewer than `minTriangles` triangles
-- def countTriangles {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (maxTri : ℕ)  : ℕ :=
-- let triangleCount :=
--   univ.sum (λ v1 =>
--     univ.sum (λ v2 =>
--       univ.sum (λ v3 =>
--         if v1 < v2 ∧ v2 < v3 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v1 v3 then
--           1
--         else
--           0)))
-- if triangleCount >= maxTri then 1 else 0



-- def G : SimpleGraph (Fin (#[#[0, 1, 0], #[0, 0, 1], #[0, 0, 0]]).size):=
-- graphMk ((#[#[0, 1, 0], #[0, 0, 1], #[0, 0, 0]]))

-- --instance

-- -- #eval countTriangles G 1
--------------------------------------------------
