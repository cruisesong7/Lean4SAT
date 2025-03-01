import Lake
open Lake DSL

package "leansat" where
  -- add package configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.16.0-rc1"

@[default_target]
lean_lib «Leansat» where
-- roots := #[`Leansat.Utils,`Leansat.CardinalityCounter]
defaultFacets := #[`shared]
moreLinkArgs :=
  #["-L.lake/packages/aesop/.lake/build/lib/", "-lAesop",
    "-L.lake/packages/Cli/.lake/build/lib/", "-lCli",
    "-L.lake/packages/importGraph/.lake/build/lib/", "-lImportGraph",
    "-L.lake/packages/mathlib/.lake/build/lib/", "-lMathlib",
    "-L.lake/packages/proofwidgets/.lake/build/lib/", "-lProofWidgets",
    "-L.lake/packages/Qq/.lake/build/lib/", "-lQq",
    "-L.lake/packages/batteries/.lake/build/lib/", "-lBatteries",
    "-L.lake/packages/LeanSearchClient/.lake/build/lib/", "-lLeanSearchClient",
    "-lLake", "-lLean"]
  -- add library configuration options here

-- lean_exe "leansat" where
--   root := `Main

-- Adding ramseyEncoder from previous project

lean_exe "ramseyEncoder" where
  srcDir := "code"
  root := `RamseyEncoder

script ramsey (args) do
  if List.length args != 3 then
    IO.println "Usage: lake script run ramsey <K> <L> <N>"
    return 1
  else
    let buildCmd := "lake build"
    let _ ← IO.Process.run { cmd := "sh", args := #["-c", buildCmd] }

    let exePath := "./.lake/build/bin/ramseyEncoder"
    let outputPath := "./data/input.cnf"

    -- Construct and run the shell command with output redirection to 'output.cnf'
    let runCmd := s!"{exePath} {String.intercalate " " args} > {outputPath}"
    let _ ← IO.Process.output { cmd := "sh", args := #["-c", runCmd] }

    return 0

script sat (_args) do
  let inputPath := "./data/input.cnf"
  let outputPath := "./data/output.proof" --change it to .log
  let runCmd := s!"./picosat-965/picosat --all {inputPath} -o {outputPath}"
  let _ ← IO.Process.output { cmd := "sh", args := #["-c", runCmd] }
  return 0

script allsat (args) do
  if args.length < 3 then
    IO.println "Usage: lake script run allsat <K> <L> <N> [buildUpon] [isLast]"
    return 1
  else
    let maxN := String.toNat! args[2]!
    let k := args[0]!
    let l := args[1]!
    let buildUpon := if args.length <= 3 then false else args[3]! = "true"
    let isLast := if args.length <= 4 then false else args[4]! = "true"

    -- let finalOutputPath := s!"./data/ramseygood_{k}_{l}.proof"
    let leanOutputPath := s!"./Leansat/Ramseygood.lean"

    -- Initialize the final output file by creating it empty
    -- let _ ← IO.FS.writeFile finalOutputPath ""

    if buildUpon then
      IO.println s!"Appending to existing {leanOutputPath}"
    else
      let initContent := s!"def RamseyGood (k l n : Nat) : String :=\n  match (k, l, n) with\n"
      let _ ← IO.FS.writeFile leanOutputPath initContent

    for n in [1:maxN+1] do
      -- Run `ramsey` logic directly: build and execute `ramseyEncoder`
      let buildCmd := "lake build"
      let _ ← IO.Process.run { cmd := "sh", args := #["-c", buildCmd] }

      let exePath := "./.lake/build/bin/ramseyEncoder"
      let inputPath := s!"./data/input_{k}_{l}_{n}.cnf"
      let ramseyCmd := s!"{exePath} {toString k} {l} {n} > {inputPath}"
      let _ ← IO.Process.output { cmd := "sh", args := #["-c", ramseyCmd] }

      -- Run `sat` logic directly: execute `picosat`
      let outputPath := s!"./data/output_{k}_{l}_{n}.proof"
      let satCmd := s!"./picosat-965/picosat --all {inputPath} -o {outputPath}"
      let _ ← IO.Process.output { cmd := "sh", args := #["-c", satCmd] }

      -- Read the content of `output_{n}.proof`
      let proofContent ← IO.FS.readFile outputPath

      -- Append the proof content to the final output file
      -- let handle ← IO.FS.Handle.mk finalOutputPath IO.FS.Mode.append
      -- handle.putStr proofContent

      -- Append a match case for this specific (k, l, n) combination in the Lean file
      let leanHandle ← IO.FS.Handle.mk leanOutputPath IO.FS.Mode.append
      let leanContent := s!"  | ({k}, {l}, {n}) => \"{proofContent.trim}\"\n"
      leanHandle.putStr leanContent

    -- Close the `match` expression with a default case, only if initializing or file was recreated
    if (isLast) then
      let finalHandle ← IO.FS.Handle.mk leanOutputPath IO.FS.Mode.append
      finalHandle.putStr "  | _ => \"No solution available for the specified (k, l, n)\"\n"

    IO.println s!"All solutions concatenated into {leanOutputPath}"
    return 0
