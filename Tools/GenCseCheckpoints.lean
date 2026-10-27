import Tools.GenWordStages

/-! Propose bounded CSE transitions. Native evaluation supplies literals only;
each transition and each structural composition is checked by the kernel. -/
open Lean Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

deriving instance ToExpr for Misc.BalancedMap.Map
deriving instance ToExpr for WordCse.Knowledge

namespace CseCheckpoints
abbrev Program := WordLangProgHOL (BitVec 64)

structure State where
  literals : Std.HashMap Expr String := {}
  knowledge : Std.HashMap Expr String := {}
  data : Array String := #[]
  proofs : Array String := #[]
  next : Nat := 0

def literal (state : IO.Ref State) (expr : Expr) (type body : String) : IO String := do
  if let some name := (← state.get).literals[expr]? then return name
  let name := s!"literal{(← state.get).literals.size}"
  state.modify fun st => {st with
    literals := st.literals.insert expr name,
    data := st.data.push s!"def {name} : {type} := {body}\n"}
  return name

partial def sparse (state : IO.Ref State) (tree : Spt Nat) : IO String := do
  if let some name := (← state.get).literals[toExpr tree]? then return name
  let body ← match tree with
    | .ln => pure ".ln"
    | .ls n => pure s!".ls {n}"
    | .bn l r => do pure s!".bn {← sparse state l} {← sparse state r}"
    | .bs l n r => do pure s!".bs {← sparse state l} {n} {← sparse state r}"
  literal state (toExpr tree) "Spt Nat" body

partial def balanced (env : Environment) (state : IO.Ref State)
    (tree : Misc.BalancedMap.Map (List Nat) Nat) : IO String := do
  if let some name := (← state.get).literals[toExpr tree]? then return name
  let body ← match tree with
    | .tip => pure ".tip"
    | .bin size key value l r => do
      let key ← renderWordStage env (toExpr key)
      pure s!".bin {size} ({key}) {value} {← balanced env state l} {← balanced env state r}"
  literal state (toExpr tree) "Misc.BalancedMap.Map (List Nat) Nat" body

def knowledge (env : Environment) (state : IO.Ref State) (k : WordCse.Knowledge) : IO String := do
  let expr := toExpr k
  if let some name := (← state.get).knowledge[expr]? then return name
  let canonical ← sparse state k.toCanonical
  let latest ← sparse state k.toLatest
  let gets ← renderWordStage env (toExpr k.getsMem)
  let instrs ← balanced env state k.instrsMem
  let loads ← balanced env state k.loadsMem
  let name := s!"knowledge{(← state.get).knowledge.size}"
  let body := s!"WordCse.Knowledge.mk {canonical} {latest} ({gets}) {instrs} {loads}"
  state.modify fun st => {st with
    knowledge := st.knowledge.insert expr name,
    data := st.data.push (s!"def {name} : WordCse.Knowledge := (InitECandidate.Proofs.ComputationCache.boxedValue ({body})).val\n" ++
      s!"theorem {name}_def : {name} = ({body}) := InitECandidate.Proofs.ComputationCache.boxedValue_eq _\n")}
  return name

-- Saturate at the bound: a long sequence costs O(bound), not O(program size).
partial def boundedSize (p : Program) (fuel : Nat) : Nat :=
  if fuel == 0 then 0 else
  match p with
  | .seq a b | .ite _ _ _ a b =>
    let aSize := boundedSize a (fuel-1)
    1 + aSize + boundedSize b (fuel-1-aSize)
  | .mustTerminate b | .loop _ b _ => 1 + boundedSize b (fuel-1)
  | _ => 1

partial def checkpoint (env : Environment) (state : IO.Ref State)
    (programs : IO.Ref PancakeDataState) (bound : Nat)
    (input : WordCse.Knowledge) (p : Program) : IO (WordCse.Knowledge × Program × Nat) := do
  let inputName ← knowledge env state input
  let pName ← wordProgData env programs p
  let mut proof := ""
  let (output, q) ← if boundedSize p (bound+1) <= bound then do
      let result := WordCse.wordCse input p
      let outputName ← knowledge env state result.1
      let defs := if inputName == outputName then s!"{inputName}_def"
        else s!"{inputName}_def, {outputName}_def"
      proof := s!"  rw [{defs}]\n  kernel_rfl\n"
      pure result
    else match p with
    | .seq a b => do
      let (middle, aOut, ha) ← checkpoint env state programs bound input a
      let (output, bOut, hb) ← checkpoint env state programs bound middle b
      proof := s!"  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node{ha}_eq node{hb}_eq\n"
      pure (output, .seq aOut bOut)
    | .ite c r imm a b => do
      let (left, aOut, ha) ← checkpoint env state programs bound input a
      let (right, bOut, hb) ← checkpoint env state programs bound input b
      let output := WordCse.mergeData left right
      let leftName ← knowledge env state left
      let rightName ← knowledge env state right
      let outputName ← knowledge env state output
      let defs := (#[leftName, rightName, outputName]).toList.eraseDups
      let defs := String.intercalate ", " (defs.map (· ++ "_def"))
      proof := s!"  apply InitECandidate.Proofs.CseComputation.ite_checkpoint _ _ _ _ _ _ _ _ _ _ _ node{ha}_eq node{hb}_eq\n  rw [{defs}]\n  kernel_rfl\n"
      pure (output, .ite c r imm aOut bOut)
    | .mustTerminate b => do
      let (output, bOut, hb) ← checkpoint env state programs bound input b
      proof := s!"  exact InitECandidate.Proofs.CseComputation.mustTerminate_of_eq _ _ _ _ node{hb}_eq\n"
      pure (output, .mustTerminate bOut)
    | .loop names b exits => do
      let (_, bOut, hb) ← checkpoint env state programs bound WordCse.emptyData b
      let emptyName ← knowledge env state WordCse.emptyData
      proof := s!"  have h := node{hb}_eq\n  rw [{emptyName}_def] at h ⊢\n  exact InitECandidate.Proofs.CseComputation.loop_of_eq _ _ _ _ _ _ h\n"
      pure (WordCse.emptyData, .loop names bOut exits)
    | _ => throw (IO.userError "bounded CSE checkpoint: unexpected large leaf")
  let outputName ← knowledge env state output
  let qName ← wordProgData env programs q
  let index := (← state.get).next
  state.modify fun st => {st with
    next := index+1,
    proofs := st.proofs.push (s!"theorem node{index}_eq : WordCse.wordCse {inputName} {pName} = ({outputName}, {qName}) := by\n" ++ proof)}
  return (output,q,index)

unsafe def main (args : List String) : IO Unit := do
  let some label := args.head?.bind String.toNat? | throw (IO.userError "usage: LABEL [BOUND]")
  let bound := (args[1]?.bind String.toNat?).getD 64
  if bound == 0 then throw (IO.userError "BOUND must be positive")
  let inputModule := (s!"InitECandidate.Proofs.WordStages.Pass{label}_3").toName
  let outputModule := (s!"InitECandidate.Proofs.CseCheckpoints{label}.Program").toName
  let existingOutput := args.contains "--existing-output"
  let modules := #[{module := `Tools.GenWordStages}, {module := inputModule}]
  let modules := if existingOutput then modules.push {module := outputModule} else modules
  let env ← importModules modules {} 0
  -- The preceding equations already certify this program against the current
  -- guest. Re-evaluating the entire frontend here adds no proof obligation.
  let .ok p3 := env.evalConst Program {} (s!"InitECandidate.Proofs.WordStages.pass{label}_3").toName
    | throw (IO.userError "cannot evaluate checked predecessor")
  let state ← IO.mkRef ({} : State)
  let programs ← IO.mkRef ({tag := "program"} : PancakeDataState)
  -- Seed from the actual checked predecessor modules, whose local numbering
  -- may differ between legacy and fresh generators. This is proposal data;
  -- every generated equation still has to pass the kernel.
  let nodePrefix := s!"InitECandidate.Proofs.WordStages.word{label}_2_"
  let names := env.constants.fold (init := #[]) fun names name info =>
    if name.toString.startsWith nodePrefix && info.type == toTypeExpr Program then names.push name else names
  for (name,index) in names.zipIdx do
    let _ ← seedWordProgConst env programs name
    if index % 1024 == 0 then IO.println s!"CSE {label}: seeded {index+1}/{names.size} literals"
  let (_,output,root) ← checkpoint env state programs bound WordCse.emptyData p3
  let inputName ← wordProgData env programs p3
  let outputName ← wordProgData env programs output
  let emptyName ← knowledge env state WordCse.emptyData
  let st ← state.get
  let dir := s!"/tmp/init-e-phase3b/submission/InitECandidate/Proofs/CseCheckpoints{label}"
  IO.FS.createDirAll dir
  let ns := s!"InitECandidate.Proofs.CseCheckpoints{label}"
  let header := "set_option Elab.async false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend\n" ++ s!"namespace {ns}\n"
  let outputImport := if existingOutput then s!"import {outputModule}\n" else ""
  let imports := outputImport ++ s!"import {inputModule}\nimport InitECandidate.Proofs.CseComputation\nimport InitECandidate.Proofs.CompactComputation\n"
  let stateChunks := (st.data.size+2047)/2048
  for i in List.range stateChunks do
    let previous := if i == 0 then imports else s!"import {ns}.State{i-1}\n"
    writeCompactCertificate (dir ++ s!"/State{i}.lean") (previous ++ header ++
      String.join (st.data.toList.drop (i*2048) |>.take 2048) ++ s!"end {ns}\n")
  let previous := if stateChunks == 0 then imports else s!"import {ns}.State{stateChunks-1}\n"
  writeCompactCertificate (dir ++ "/Data.lean") (previous ++ header ++
    String.intercalate "\n" (← programs.get).lines.toList ++ s!"\nend {ns}\n")
  let chunks := (st.next+63)/64
  -- A larger bound may emit fewer chunks on regeneration.
  for item in ← (System.FilePath.mk dir).readDir do
    let file := item.fileName
    if file.startsWith "Proof" && file.endsWith ".lean" then
      if let some index := (file.drop 5 |>.toString |>.dropEnd 5 |>.toString).toNat? then
        if index >= chunks then IO.FS.removeFile item.path
    if file.startsWith "State" && file.endsWith ".lean" then
      if let some index := (file.drop 5 |>.toString |>.dropEnd 5 |>.toString).toNat? then
        if index >= stateChunks then IO.FS.removeFile item.path
  for i in List.range chunks do
    let previous := if i == 0 then s!"{ns}.Data" else s!"{ns}.Proof{i-1}"
    writeCompactCertificate (dir ++ s!"/Proof{i}.lean") (s!"import {previous}\n" ++ header ++
      String.join (st.proofs.toList.drop (i*64) |>.take 64) ++ s!"end {ns}\n")
  writeCompactCertificate (dir ++ "/Closed.lean") (s!"import {ns}.Proof{chunks-1}\nimport InitECandidate.Proofs.WordStages.Pass{label}_3\n" ++ header ++
    s!"theorem checked : WordCse.wordCommonSubexpElim InitECandidate.Proofs.WordStages.pass{label}_3 = {outputName} := by\n" ++
    s!"  have h := congrArg Prod.snd node{root}_eq\n  rw [{emptyName}_def] at h\n  exact h\n#print axioms checked\nend {ns}\n")
  IO.println s!"CSE {label}: {st.next} checked transitions, {st.knowledge.size} states, {st.literals.size} shared state trees; input {inputName}, output {outputName}"

end CseCheckpoints

unsafe def main := CseCheckpoints.main
