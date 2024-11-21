import Init.Prelude
--import Mathlib.Data.List.Sublists
-- import Std.Data.HashMap.Basic


open Std List

def sublistsLenAux {α β : Type} : Nat → List α → (List α → β) → List β → List β
  | 0, _, f, r => f []::r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)

def sublistsLen {α : Type} (n : Nat) (l : List α) : List (List α) := sublistsLenAux n l id []

def keyToValue (i j: Nat): Nat := j + i * (i - 1) / 2 + 1

def main (argv : List String) : IO UInt32 := do
  let N := argv[2]!.toNat!; let S := argv[0]!.toNat!; let T := argv[1]!.toNat!
  let s_cliques := (sublistsLen S (range N))
  let t_cliques := (sublistsLen T (range N))

  let vars := toString (length (sublistsLen 2 (range N)))
  let clauses := toString (length s_cliques + length t_cliques)

  if (clauses == "0") then
    IO.print "p cnf 0 0\n"
    return 0

  let result := "p cnf " ++ vars ++ " " ++ clauses ++ "\n"
  let clauses := s_cliques.map λclique => (String.intercalate " "
    ((sublistsLen 2 clique).map λx => toString (keyToValue x.getLast! x.head!)))
  let clauses' := t_cliques.map λclique => (String.intercalate " "
    ((sublistsLen 2 clique).map λx => "-" ++ toString (keyToValue x.getLast! x.head!)))
  IO.print ( result ++ String.intercalate " 0\n" (clauses ++ clauses') ++ " 0\n")
  return 0

-- #eval (do main ["1", "2", "5"])
