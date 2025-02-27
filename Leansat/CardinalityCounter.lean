import Leansat.Ramseygood
import Leansat.Utils
--------------------------------------------------
-- Function to count the number of edges in adjList
def countEdges (adjList : List (Option (Fin 2))) : ℕ := adjList.count (some 1)

-- theorem countEdges_correct (adjList : List (Option (Fin 2))): eq number of postive literals in the string
theorem countEdges_correct (input: List String) : countEdges (readInput input) = (input.countP (λ x ↦ x.toInt! > 0)) := by
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
      -- by_cases hd.toInt! = 0 <;> simp_all

--------------------------------------------------

-- Function to check if the number of edges is greater than or equal to maxEdge
def isEdgesGT (adjList : List (Option (Fin 2))) (maxEdge : ℕ) : Fin (2) :=
  let numEdges := countEdges adjList
  if numEdges >= maxEdge then 1 else 0

def exampleList : List (Option (Fin 2)):= readInput ("1 -2 3".splitOn " ")

-- #eval isEdgesGT exampleList 1  -- Expected: 1
-- #eval isEdgesGT exampleList 2  -- Expected: 1
-- #eval isEdgesGT exampleList 3  -- Expected: 0

theorem isEdgesGT_correct (adjList : List (Option (Fin 2))) (maxEdge : ℕ) :
  isEdgesGT adjList maxEdge = 1 ↔ countEdges adjList ≥ maxEdge := by simp [isEdgesGT]
--------------------------------------------------

def processProofFile (content : String) : List (List String) :=
  let lines := content.splitOn "\n"
  let solutionLines := lines.filter (λ line => line.startsWith "v" ∧ line.endsWith "0")
  let solutions := solutionLines.map (λ line =>
    line.splitOn " " |>.tail!.filter (· ≠ "0")
  )
  solutions

-- #eval processProofFile (RamseyGood 3 4 8)

def processAndCountEdges (content : String) : List ℕ :=
  let solutions := processProofFile content
  let counts := solutions.map (λ solution =>
    let adjList := readInput solution
    countEdges adjList
  )
  counts
-- #eval processAndCountEdges ramseygood_2_5

def e_ramseyGraph (k l n : ℕ) : ℕ :=
  let counts := processAndCountEdges (RamseyGood k l n)
  match List.min? counts with
  | some count => count
  | none => 0

def E_ramseyGraph (k l n : ℕ) : ℕ :=
  let counts := processAndCountEdges (RamseyGood k l n)
  match List.maximum counts with
  | some count => count
  | none => 0

-- #eval e_ramseyGraph 2 5 4
-- #eval E_ramseyGraph 3 4 8

def Theorem₁_RHS (k l n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  (List.range (n)).map (λ i ↦
    let nᵢ := (Finset.filter (λ v => G.degree v = i) Finset.univ).card
    let E₁ := E_ramseyGraph (k - 1) l i
    let E₂ := E_ramseyGraph (l - 1) k (n - i - 1)
    2 * E₁ + 2 * E₂ + (3 * i * ((n - i - 1) * (n - 1) * (n - 2))) * nᵢ
  ) |>.sum

def Theorem₁ (k l n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]: Bool := Theorem₁_RHS k l n G ≥ 0

--------------------------------------------------
-- def processProofFile_IO (filePath : String) : IO (List (List String)) := do
--   let content ← IO.FS.readFile filePath
--   let lines := content.splitOn "\n"
--   let solutionLines := lines.filter (λ line ↦ line.startsWith "v")
--   let solutions := solutionLines.map (λ line ↦
--     line.splitOn " " |>.tail!.filter (· ≠ "0")
--   )
--   return solutions

-- #eval processProofFile_IO "./data/ramseygood_2_5.proof"

-- def processAndCountEdges_IO (filePath : String) : IO (List ℕ) := do
--   let solutions ← processProofFile_IO filePath
--   let counts := solutions.map (λ solution ↦
--     let adjList := readInput solution
--     countEdges adjList
--   )
--   return counts
-- #eval processAndCountEdges_IO "./data/ramseygood_3_4.proof"


-- def e_ramseyGraph_IO (k l n : ℕ) : IO ℕ := do
--   let counts ← processAndCountEdges_IO s!"./data/output_{k}_{l}_{n}.proof"
--   match List.minimum? counts with
--   | some count => return count
--   | none => return 0

-- def E_ramseyGraph_IO (k l n: ℕ): IO (ℕ) := do
--   let counts ← processAndCountEdges_IO s!"./data/output_{k}_{l}_{n}.proof"
--   match List.maximum? counts with
--   | some count => return count
--   | none => return 0

-- #eval e_ramseyGraph_IO 2 5 4
-- #eval E_ramseyGraph_IO 3 4 8

-- def Theorem₁_RHS_IO (k l n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : IO ℕ := do
--   let terms ← List.range (n + 1) |>.mapM (λ i => do
--     let nᵢ := (Finset.filter (λ v => G.degree v = i) Finset.univ).card
--     let E₁ ← E_ramseyGraph_IO (k - 1) l i
--     let E₂ ← E_ramseyGraph_IO (l - 1) k (n - i - 1)
--     return 2 * E₁ + 2 * E₂ + (3 * i * ((n - i - 1) * (n - 1) * (n - 2))) * nᵢ
--   )
--   return terms.sum

-- def Theorem₁_IO (k l n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]: IO Bool := do
--   let RHS ← Theorem₁_RHS_IO k l n G
--   return RHS ≥ 0
