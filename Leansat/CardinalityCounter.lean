import Leansat.Utils
import Mathlib.Combinatorics.SimpleGraph.Clique
--------------------------------------------------
-- Function to count the number of edges in adjList
@[export countEdges]
def countEdges (adjList : List (Fin 2)) : ℕ := adjList.count 1

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
--------------------------------------------------
@[export edgesExceedBound]
-- Function to check if the number of edges is greater than or equal to an upperbound
def edgesExceedBound (adjList : List (Fin 2)) (upperbound : ℕ) : Bool :=
  let numEdges := countEdges adjList
  if numEdges >= upperbound then true else false

theorem edgesExceedBound_correct (adjList : List (Fin 2)) (upperbound : ℕ) :
  edgesExceedBound adjList upperbound = true ↔ countEdges adjList ≥ upperbound := by simp [edgesExceedBound]
--------------------------------------------------
@[export NCliquesExceedBound]
-- Function to check if the number of N-Cliques is greater than or equal to an upperbound
def NCliquesExceedBound (adjList : List (Fin 2)) (N : ℕ) (upperbound : ℕ) : Bool :=
  let G := SimpleGraph.mk_list adjList
  let numCLiques := (Finset.univ.filter (λ S ↦ G.IsNClique N S) |>.card)
  if numCLiques >= upperbound then true else false
--------------------------------------------------
@[export DegreeExceedBound]
-- Function to check if there exist a vertex whose degree is greater than or equal to an upperbound
def DegreeExceedBound (adjList : List (Fin 2)) (upperbound : ℕ) : Bool :=
  let G := SimpleGraph.mk_list adjList
  if G.maxDegree ≥ upperbound then true else false

theorem DegreeExceedBound_correct (adjList : List (Fin 2)) :
  ∀ upperbound : ℕ, DegreeExceedBound adjList upperbound = true ↔ (SimpleGraph.mk_list adjList).maxDegree ≥ upperbound := by simp[DegreeExceedBound]
--------------------------------------------------
