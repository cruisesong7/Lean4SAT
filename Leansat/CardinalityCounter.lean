import Leansat.Utils
--------------------------------------------------
-- Function to count the number of edges in adjList
@[export countEdges]
def countEdges (adjList : List (Option (Fin 2))) : ℕ := adjList.count (some 1)

-- theorem countEdges_correct (adjList : List (Option (Fin 2))): eq number of postive literals in the string
theorem countEdges_correct (input: List Int) : countEdges (readInput_Int input) = (input.countP (λ x ↦ x > 0)) := by
  induction input with
  | nil => simp_all[readInput_Int, countEdges]
  | cons hd tl ih =>
    by_cases hd > 0
    · have tmp : hd > 0 → countEdges (readInput_Int (hd :: tl)) = countEdges (readInput_Int tl) + 1 := by
        intro H
        have tmp := (readInput_Int_correct (hd :: tl) 0 (by simp[readInput_Int])).left H
        simp_all[readInput_Int, countEdges]
      simp_all
    · simp_all[readInput_Int, countEdges, List.count]
      -- by_cases hd.toInt! = 0 <;> simp_all

--------------------------------------------------
@[export edgesExceedBound]
-- Function to check if the number of edges is greater than or equal to an upperbound
def edgesExceedBound (adjList : List (Option (Fin 2))) (upperbound : ℕ) : Fin 2 :=
  let numEdges := countEdges adjList
  if numEdges >= upperbound then 1 else 0

-- def exampleList : List (Option (Fin 2)):= readInput_Int ([1,-2,3])
-- #eval isEdgesGT exampleList 1  -- Expected: 1
-- #eval isEdgesGT exampleList 2  -- Expected: 1
-- #eval isEdgesGT exampleList 3  -- Expected: 0

theorem edgesExceedBound_correct (adjList : List (Option (Fin 2))) (upperbound : ℕ) :
  edgesExceedBound adjList upperbound = 1 ↔ countEdges adjList ≥ upperbound := by simp [edgesExceedBound]
--------------------------------------------------
@[export DegreeExceedBound]
def DegreeExceedBound (adjList : List (Option (Fin 2))) (upperbound : ℕ) : Fin 2 :=
  if (SimpleGraph.mk_list adjList).maxDegree ≥ upperbound then 1 else 0

theorem DegreeExceedBound_correct (adjList : List (Option (Fin 2))) :
  ∀ upperbound : ℕ, DegreeExceedBound adjList upperbound = 1 ↔ (SimpleGraph.mk_list adjList).maxDegree ≥ upperbound := by simp[DegreeExceedBound]
--------------------------------------------------
