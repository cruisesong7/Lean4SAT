import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

-- Function to compute the vertices (i, j) associated with the k-th edge
def computeRowCol (k N : ℕ) : Option (ℕ × ℕ) :=
  let j :=  (Nat.sqrt (1 + 8 * k) + 1) / 2
  if j < N then
    let i := k - (j * (j - 1)) / 2
    if i < j then
      some (i, j)
    else
      none
  else
    none

#eval (Nat.sqrt (1 + 8 * 2) + 1) / 2
#eval computeRowCol 2 3

-- Initialize a 2D array for the adjacency matrix
def initAdjMatrix (N : ℕ) : Array (Array (Fin 2)) :=
  Array.mkArray N (Array.mkArray N 0)

-- Parse a partial assignment string and construct an adjacency matrix using the index formula
def parsePartialAssignment (input : String) : Option (Array (Array (Fin 2))) :=
  let assignments := input.splitOn " "
  let M := assignments.length
  let N := (1 + Nat.sqrt (1 + 8 * M)) / 2  -- Calculate N from the input size

  if N * (N - 1) / 2 ≠ M then
    none  -- Return none if the input length is invalid
  else
    let initMat := initAdjMatrix N

    let matrix := List.foldl (λ (matrix : Array (Array (Fin 2))) (k_val : String × ℕ) =>
      let (h, k) := k_val  -- h is the string value, k is the index
      match computeRowCol k N with
      | some (i, j) =>
        let value := h.toInt!  -- cast string to integer
        let row := matrix.get! i
        let newRow := if value > 0 then row.set! j 1 else row.set! j 0
        matrix.set! i newRow
      | none => matrix  -- Skip if there's an invalid position
    ) initMat (assignments.zip (List.range M))

    some matrix

#eval parsePartialAssignment "1 -2 3"
#eval parsePartialAssignment "1 1 1"
#eval parsePartialAssignment "-1 -1 -1"
#eval parsePartialAssignment "1 -1 1 1"

-- Function to symmetrically extend an upper triangular adjacency matrix
def completeAdjMatrix (adjMatrix : Array (Array (Fin 2))) : Array (Array (Fin 2)) :=
  let N := adjMatrix.size
  adjMatrix.modify (λ matrix =>
    matrix.modifyIdx (λ i row =>
      row.modifyIdx (λ j _ =>
        if i == j then 0  -- No self-loops
        else if j > i then adjMatrix.get! i.get! j  -- Upper triangular part
        else adjMatrix.get! j.get! i  -- Mirror lower triangular part
      )
    )
  )


-- Function to generate a SimpleGraph from the adjacency matrix
def graphPropagator {N : ℕ} (adjMatrix : Array (Array (Fin 2))) : SimpleGraph (Fin N) :=
  SimpleGraph.mk (λ v w => (adjMatrix.get! v.val).get! w.val = 1)  -- Adjacency relation
  (by
    -- Symmetric property: if there's an edge between v and w, there's an edge between w and v
    intros v w
    simp
    intros h
    rw [←h]
    simp_all
  )
    (by
    -- Irreflexive property: no vertex has an edge to itself (no self-loops)
    intros v
    simp [Fin.ext_iff]
    exact Nat.ne_of_lt v.is_lt
  )
