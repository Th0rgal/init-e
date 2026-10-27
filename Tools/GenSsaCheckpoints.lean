import Tools.GenWordStages
import InitECandidate.Proofs.SmallSsaKernelComputation

/-! Native SSA proposals with independently kernel-checked bounded transitions.
No proposal is accepted without checking its original structural SSA equation. -/
open Lean Flapjack Flapjack.Compiler.Backend
open WordAlloc
namespace SsaCheckpoints
open InitECandidate.Proofs.SmallSsaKernelComputation
abbrev Program := WordLangProgHOL (BitVec 64)
abbrev Context := List (Spt Nat × Spt Unit × Spt Unit)
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

structure State where
  literals : Std.HashMap Expr String := {}
  data : Array String := #[]
  proofs : Array String := #[]
  next : Nat := 0

def literal (st : IO.Ref State) (expr : Expr) (type body : String) : IO String := do
  if let some name := (← st.get).literals[expr]? then return name
  let name := s!"state{(← st.get).literals.size}"
  st.modify fun s => {s with
    literals := s.literals.insert expr name
    data := s.data.push s!"def {name} : {type} := {body}\n"}
  return name

partial def sparse {α : Type} [ToExpr α] (env : Environment) (st : IO.Ref State)
    (type : String) (tree : Spt α) : IO String := do
  if let some name := (← st.get).literals[toExpr tree]? then return name
  let body ← match tree with
    | .ln => pure ".ln"
    | .ls n => do pure s!".ls ({← renderWordStage env (toExpr n)})"
    | .bn l r => do pure s!".bn {← sparse env st type l} {← sparse env st type r}"
    | .bs l n r => do
      pure s!".bs {← sparse env st type l} ({← renderWordStage env (toExpr n)}) {← sparse env st type r}"
  literal st (toExpr tree) type body

def context (env : Environment) (st : IO.Ref State) (lt : Context) : IO String := do
  if let some name := (← st.get).literals[toExpr lt]? then return name
  let entries ← lt.mapM fun (ssa,names,exits) => do
    let ssa ← sparse env st "Spt Nat" ssa
    let names ← sparse env st "Spt Unit" names
    let exits ← sparse env st "Spt Unit" exits
    pure s!"({ssa},{names},{exits})"
  literal st (toExpr lt) "List (Spt Nat × Spt Unit × Spt Unit)"
    ("[" ++ String.intercalate ", " entries ++ "]")

partial def boundedSize (p : Program) (fuel : Nat) : Nat :=
  if fuel == 0 then 0 else
  match p with
  | .seq a b | .ite _ _ _ a b =>
    let left := boundedSize a (fuel-1)
    1 + left + boundedSize b (fuel-1-left)
  | .mustTerminate p | .loop _ p _ => 1 + boundedSize p (fuel-1)
  | .call (some (_,_,p,_,_)) _ _ h =>
    let left := boundedSize p (fuel-1)
    1 + left + (match h with | none => 0 | some (_,q,_,_) => boundedSize q (fuel-1-left))
  | _ => 1

partial def checkpoint (env : Environment) (st : IO.Ref State)
    (programs : IO.Ref PancakeDataState) (bound : Nat)
    (p : Program) (ssa : Spt Nat) (next : Nat) (lt : Context) :
    IO (Program × Spt Nat × Nat × Nat) := do
  let pName ← wordProgData env programs p
  let input ← sparse env st "Spt Nat" ssa
  let ctx ← context env st lt
  let mut children : List Nat := []
  let result ← if boundedSize p (bound+1) <= bound then
      pure (ssaStructural p ssa next lt)
    else match p with
    | .seq a b => do
      let (aOut,middle,na,ha) ← checkpoint env st programs bound a ssa next lt
      let (bOut,output,nb,hb) ← checkpoint env st programs bound b middle na lt
      children := [ha,hb]
      pure (.seq aOut bOut,output,nb)
    | .mustTerminate p => do
      let (pOut,output,na,hp) ← checkpoint env st programs bound p ssa next lt
      children := [hp]
      pure (.mustTerminate pOut,output,na)
    | .ite _ _ _ a b => do
      let (_,_,na,ha) ← checkpoint env st programs bound a ssa next lt
      let (_,_,_,hb) ← checkpoint env st programs bound b ssa na lt
      children := [ha,hb]
      pure (ssaStructural p ssa next lt)
    | .loop names body exits => do
      let (_,refreshed,na) := loopSetup (width := 64) names exits ssa next
      let (_,_,_,hb) ← checkpoint env st programs bound body (sptInter refreshed names) na
        ((refreshed,names,exits)::lt)
      children := [hb]
      pure (ssaStructural p ssa next lt)
    | .call (some (ret,cutsets,body,_,_)) _ _ handler => do
      let allNames := sptUnion cutsets.1 cutsets.2
      let names := (sptToAList allNames).map Prod.fst
      let (_,saved,na) := listNextVarRenameMove (width := 64) ssa (next+2) names
      let (_,restored,nb) := listNextVarRenameMove (width := 64) (sptInter saved allNames) (na+2) names
      let (_,retState,nc) := listNextVarRename ret restored nb
      let (_,_,nd,hr) ← checkpoint env st programs bound body retState nc lt
      children := [hr]
      if let some (name,body,_,_) := handler then
        let (_,excState,ne) := nextVarRename name restored nd
        let (_,_,_,he) ← checkpoint env st programs bound body excState ne lt
        children := children ++ [he]
      pure (ssaStructural p ssa next lt)
    | _ => throw (IO.userError "unexpected large SSA leaf")
  let (output,map,counter) := result
  let outputName ← wordProgData env programs output
  let outputMap ← sparse env st "Spt Nat" map
  let index := (← st.get).next
  let rewrites := String.intercalate ", " (children.map fun n => s!"node{n}_eq")
  let proof := if children.isEmpty then "  kernel_rfl\n"
    else s!"  unfold {pName}\n  rw [ssaStructural.eq_def]\n  dsimp only\n  rw [{rewrites}]\n  kernel_rfl\n"
  st.modify fun s => {s with
    next := index+1
    proofs := s.proofs.push (s!"theorem node{index}_eq : ssaStructural {pName} {input} {next} {ctx} = ({outputName},{outputMap},{counter}) := by\n" ++ proof)}
  return (output,map,counter,index)

unsafe def main (args : List String) : IO Unit := do
  let some label := args.head?.bind String.toNat? | throw (IO.userError "usage: LABEL ARGC [BOUND]")
  let some argc := args[1]?.bind String.toNat? | throw (IO.userError "missing ARGC")
  let bound := (args[2]?.bind String.toNat?).getD 64
  if bound == 0 then throw (IO.userError "BOUND must be positive")
  let ns := s!"InitECandidate.Proofs.SsaCheckpoints{label}"
  let inputModule := (s!"InitECandidate.Proofs.WordStages.Pass{label}_1").toName
  let env ← importModules #[{module := `Tools.GenWordStages},
    {module := inputModule}, {module := (ns ++ ".Program").toName}] {} 0
  let .ok p := env.evalConst Program {} (s!"InitECandidate.Proofs.WordStages.pass{label}_1").toName
    | throw (IO.userError "cannot evaluate predecessor")
  let programs ← IO.mkRef ({tag := "program"} : PancakeDataState)
  let nodePrefix := s!"InitECandidate.Proofs.WordStages.word{label}_"
  let names := env.constants.fold (init := #[]) fun names name info =>
    if name.toString.startsWith nodePrefix && info.type == toTypeExpr Program then names.push name else names
  for (name,index) in names.zipIdx do
    let .ok value := env.evalConst Program {} name
      | throw (IO.userError s!"cannot evaluate literal {name}")
    let expr ← shareWordStageExpr programs (toExpr value)
    programs.modify fun s => {s with values := s.values.insert expr name.toString}
    if index % 1024 == 0 then IO.println s!"SSA {label}: seeded {index+1}/{names.size} literals"
  let st ← IO.mkRef ({} : State)
  let limit := limitVar p
  let (move,map,next) := setupSSA (outputWidth := 64) argc limit p
  let (_,_,_,root) ← checkpoint env st programs bound p map next []
  let moveName ← wordProgData env programs move
  let mapName ← sparse env st "Spt Nat" map
  let s ← st.get
  let dir := s!"/tmp/init-e-phase3b/submission/InitECandidate/Proofs/SsaCheckpoints{label}"
  IO.FS.createDirAll dir
  let header := "set_option Elab.async false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nopen Flapjack Flapjack.Compiler.Backend\nopen InitECandidate.Proofs.SmallSsaKernelComputation\n" ++ s!"namespace {ns}\n"
  let imports := s!"import {ns}.Program\nimport InitECandidate.Proofs.SmallSsaKernelComputation\n"
  let stateChunks := (s.data.size+2047)/2048
  for i in List.range stateChunks do
    let previous := if i == 0 then imports else s!"import {ns}.State{i-1}\n"
    writeCompactCertificate (dir ++ s!"/State{i}.lean") (previous ++ header ++
      String.join (s.data.toList.drop (i*2048) |>.take 2048) ++ s!"end {ns}\n")
  let previous := if stateChunks == 0 then imports else s!"import {ns}.State{stateChunks-1}\n"
  writeCompactCertificate (dir ++ "/Data.lean") (previous ++ header ++
    String.intercalate "\n" (← programs.get).lines.toList ++ s!"\nend {ns}\n")
  let chunks := (s.next+63)/64
  -- Regenerating at a larger bound can reduce the chunk count.
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
      String.join (s.proofs.toList.drop (i*64) |>.take 64) ++ s!"end {ns}\n")
  let pName := s!"InitECandidate.Proofs.WordStages.pass{label}_1"
  writeCompactCertificate (dir ++ "/Closed.lean") (s!"import {ns}.Proof{chunks-1}\n" ++ header ++
    s!"theorem limit_eq : WordAlloc.limitVar {pName} = {limit} := by kernel_rfl\n" ++
    s!"theorem setup_eq : WordAlloc.setupSSA (outputWidth := 64) {argc} {limit} {pName} = ({moveName},{mapName},{next}) := by kernel_rfl\n" ++
    s!"theorem checked : WordAlloc.fullSsaCcTrans {argc} {pName} = InitECandidate.Proofs.WordStages.pass{label}_2 := by\n" ++
    s!"  rw [fullSsaStructural_eq]\n  unfold fullSsaStructural\n  rw [limit_eq]\n  dsimp only\n  rw [setup_eq]\n  dsimp only\n  have root_eq := node{root}_eq\n  change ssaStructural {pName} {mapName} {next} [] = _ at root_eq\n  rw [root_eq]\n  kernel_rfl\n#print axioms checked\nend {ns}\n")
  IO.println s!"SSA {label}: {s.next} transitions, {s.literals.size} shared state literals"

end SsaCheckpoints
unsafe def main := SsaCheckpoints.main
