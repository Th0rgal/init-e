import Lean
import Flapjack.Pancake.WordLang
import Flapjack.Compiler.Backend.RegAlloc.ClashTree

/-! Shared literal rendering and structural Word DAG interning for stage generators.
The cache contains proposals only; generated compiler equations require kernel checks. -/
open Lean Flapjack

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

deriving instance ToExpr for Flapjack.BinOp
deriving instance ToExpr for Flapjack.Shift
deriving instance ToExpr for Flapjack.Cmp
deriving instance ToExpr for Flapjack.WordMemOp
deriving instance ToExpr for Flapjack.WordStore
deriving instance ToExpr for Flapjack.WordRegImm
deriving instance ToExpr for Flapjack.Spt
deriving instance ToExpr for Flapjack.RegAlloc.ClashTree
deriving instance ToExpr for Flapjack.Basis.Pure.MlString.MlString
deriving instance ToExpr for Flapjack.WordLangArith
deriving instance ToExpr for Flapjack.WordLangAddr
deriving instance ToExpr for Flapjack.WordLangInst
deriving instance ToExpr for Flapjack.WordLangExpHOL
deriving instance ToExpr for Flapjack.WordLangProgHOL

def renderWordStage (env : Environment) (e : Expr) : IO String := do
  let options := ({} : Options).set `pp.maxDepth (1000000 : Nat)
    |>.set `pp.width (120 : Nat) |>.set `pp.universes false
    |>.set `pp.maxSteps (1000000000 : Nat) |>.set `pp.deepTerms true
    |>.set `pp.fieldNotation false
    |>.set `maxRecDepth (1000000 : Nat) |>.set `maxHeartbeats (0 : Nat)
  let (fmt, _, _) ← Meta.MetaM.toIO (Meta.ppExpr e)
    { fileName := "<word-stage>", fileMap := default, options := options }
    { env := env }
  let rendered := fmt.pretty
  if rendered.startsWith "failed to pretty print" || rendered.contains '⋯' then
    throw (IO.userError "incomplete pretty-printer output")
  pure rendered

structure PancakeDataState where
  tag : String := "body"
  values : Std.HashMap Expr String := {}
  lines : Array String := #[]

partial def wordProgData (env : Environment) (state : IO.Ref PancakeDataState)
    (program : WordLangProgHOL (BitVec 64)) : IO String := do
  let expr := toExpr program
  let st ← state.get
  if let some name := st.values[expr]? then return name
  let text ← match program with
    | .seq a b => do
      let a ← wordProgData env state a
      let b ← wordProgData env state b
      pure s!".seq {a} {b}"
    | .mustTerminate body => do
      let body ← wordProgData env state body
      pure s!".mustTerminate {body}"
    | .ite op lhs rhs a b => do
      let op ← renderWordStage env (toExpr op)
      let rhs ← renderWordStage env (toExpr rhs)
      let a ← wordProgData env state a
      let b ← wordProgData env state b
      pure s!".ite ({op}) {lhs} ({rhs}) {a} {b}"
    | .loop before body after => do
      let before ← renderWordStage env (toExpr before)
      let after ← renderWordStage env (toExpr after)
      let body ← wordProgData env state body
      pure s!".loop ({before}) {body} ({after})"
    | .call ret target args handler => do
      let ret ← match ret with
        | none => pure "none"
        | some (names, cutsets, body, first, second) => do
          let names ← renderWordStage env (toExpr names)
          let cutsets ← renderWordStage env (toExpr cutsets)
          let body ← wordProgData env state body
          pure s!"some (({names}), ({cutsets}), {body}, {first}, {second})"
      let handler ← match handler with
        | none => pure "none"
        | some (name, body, first, second) => do
          let body ← wordProgData env state body
          pure s!"some ({name}, {body}, {first}, {second})"
      let target ← renderWordStage env (toExpr target)
      let args ← renderWordStage env (toExpr args)
      pure s!".call ({ret}) ({target}) ({args}) ({handler})"
    | _ => renderWordStage env expr
  let st ← state.get
  let name := s!"{st.tag}{st.values.size}"
  state.modify fun st => {st with
    values := st.values.insert expr name
    lines := st.lines.push s!"def {name} : WordLangProgHOL (BitVec 64) :=\n{text}\n"}
  return name
