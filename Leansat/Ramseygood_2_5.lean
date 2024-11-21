def R_2_5 (k l n : Nat) : String :=
  match (k, l, n) with
  | (2, 5, 1) => "s SATISFIABLE
v 0
s SOLUTIONS 1"
  | (2, 5, 2) => "s SATISFIABLE
v 1 0
s SOLUTIONS 1"
  | (2, 5, 3) => "s SATISFIABLE
v 1 2 3 0
s SOLUTIONS 1"
  | (2, 5, 4) => "s SATISFIABLE
v 1 2 3 4 5 6 0
s SOLUTIONS 1"
  | _ => "No solution available for the specified (k, l, n)"
