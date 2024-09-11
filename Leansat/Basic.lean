import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric

open Matrix

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
def parsePartialAssignment (N: ℕ) (input : String) : (Array (Array (Fin 2))) :=
  let assignments := input.splitOn " "
  let M := assignments.length

  let initMat := initAdjMatrix N

  let matrix := List.foldl (λ (matrix : Array (Array (Fin 2))) (k_val : String × ℕ) =>
    let (h, k) := k_val  -- h is the string value, k is the index
    match computeRowCol k N with
    | some (i, j) =>
      let value := h.toInt!  -- cast string to integer
      let row := matrix.get! i
      let newRow := if value > 0 then row.set! j 1 else row.set! j 0 -- 2 is unknown
      matrix.set! i newRow
    | none => matrix  -- Skip if there's an invalid position
  ) initMat (assignments.zip (List.range M))

  matrix

#eval parsePartialAssignment 3 "1 -2 3"
#eval parsePartialAssignment 3 "1 1 1"
#eval parsePartialAssignment 3 "-1 -1 -1"
#eval parsePartialAssignment 3 "1 -1 1 1"

-- Convert a 2D array of Fin 2 into a Matrix (Fin N) (Fin N) (Fin 2)
def arrayToMatrix (arr : Array (Array (Fin 2))): Matrix (Fin arr.size) (Fin arr.size) (Fin 2) :=
  λ i j => (arr.get! i).get! j

--------------------
-- Function to count the number of edges in the upper triangle of adjmat
def countEdges {N : ℕ} (adjMatrix : Matrix (Fin N) (Fin N) (Fin 2)) : ℕ :=
  Finset.univ.sum (λ i =>
    Finset.univ.sum (λ j =>
      if i < j ∧ adjMatrix i j = 1 then 1 else 0))

-- Function to check if the number of edges is greater than or equal to maxEdge
def checkEdges (adj2DArr : Array (Array (Fin 2))) (maxEdge : ℕ) : ℕ :=
  let adjMatrix := arrayToMatrix adj2DArr
  let numEdges := countEdges adjMatrix
  if numEdges >= maxEdge then 1 else 0

def exampleArray : Array (Array (Fin 2)) := #[#[0, 1, 0], #[0, 0, 1], #[0, 0, 0]]

-- Test cases
#eval checkEdges exampleArray 1  -- Expected: 1
#eval checkEdges exampleArray 2  -- Expected: 1
#eval checkEdges exampleArray 3  -- Expected: 0

-------------------


-- Define a structure that includes the adj matrix and its properties
structure AdjMat (N : ℕ) where
  (mat : Matrix (Fin N) (Fin N) (Fin 2))
  (isSymm : mat.IsSymm)
  (isIrrefl : ∀ i, mat i i = 0)

-- Symmetrically extend an upper triangular adjacency matrix and prove its properties
def extendAdjMat {N : ℕ} (adjMatrix : Matrix (Fin N) (Fin N) (Fin 2)) : AdjMat N :=
  let completedMatrix := λ i j =>
    if i == j then 0  -- diagonal
    else if j > i then adjMatrix i j  -- upper triangule
    else adjMatrix j i  -- lower triangule
  {
    mat := completedMatrix,
    isSymm := by {
      simp [Matrix.IsSymm.ext_iff]
      intros i j
      simp [completedMatrix]
      by_cases ieqj : i = j
      · simp_all
      · rw [← ne_eq] at ieqj
        simp [ieqj, Ne.symm]
        rw [ne_iff_lt_or_gt] at ieqj
        rcases ieqj with h|h
        · simp_all; intro h'; have h'' := lt_asymm h ; contradiction
        · simp_all; have h' := lt_asymm h; simp [h']
    },
    isIrrefl := by simp[completedMatrix]
  }

def graphMk (adj2DArr : Array (Array (Fin 2))) : SimpleGraph (Fin adj2DArr.size) :=
  let adjMatrix := extendAdjMat (arrayToMatrix adj2DArr)
  let isSymm := adjMatrix.isSymm
  let isIref := adjMatrix.isIrrefl
  SimpleGraph.mk (λ v w => adjMatrix.mat v w = 1)
  (by
    -- Prove the symmetric property (no self-loops)
    intros x y
    simp [Matrix.IsSymm.ext_iff] at isSymm
    simp_all
  )
  (by
    -- Prove the irreflexive property (undirected graph)
    intros x y
    simp_all
  )
open Finset

-- Function to check if the graph has no fewer than `minTriangles` triangles
def countTriangles {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (maxTri : ℕ)  : ℕ :=
let triangleCount :=
  univ.sum (λ v1 =>
    univ.sum (λ v2 =>
      univ.sum (λ v3 =>
        if v1 < v2 ∧ v2 < v3 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v1 v3 then
          1
        else
          0)))
if triangleCount >= maxTri then 1 else 0



def G : SimpleGraph (Fin (#[#[0, 1, 0], #[0, 0, 1], #[0, 0, 0]]).size):=
graphMk ((#[#[0, 1, 0], #[0, 0, 1], #[0, 0, 0]]))

-- #eval countTriangles G 1





-- Function to symmetrically complete an upper triangular adjacency matrix
-- def completeMatrix {N : ℕ} (adjMatrix : Matrix (Fin N) (Fin N) (Fin 2)) : Matrix (Fin N) (Fin N) (Fin 2) :=
--   λ i j =>
--     if i == j then 0  -- diagonal
--     else if j > i then adjMatrix i j  -- upper triangule
--     else adjMatrix j i  -- lower triangule

-- lemma completeMatrix_diag_0 {N : ℕ} (adjMatrix : Matrix (Fin N) (Fin N) (Fin 2)) : ∀i, completeMatrix adjMatrix i i = 0 :=
--   by simp [completeMatrix]

-- #eval completeMatrix (arrayToMatrix (#[#[0, 1, 0], #[0, 0, 1], #[0, 0, 0]]))
-- #eval ![0,1,0] 0
