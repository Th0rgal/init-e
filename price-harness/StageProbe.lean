import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import CandidateAst
import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanStructs.CompileDeclsExact
import Flapjack.Pancake.PanGlobals.CompileTopExact
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.PanToCrep.CompileExact
import Flapjack.Pancake.LoopToWord.CompFuncExact

open Flapjack
open Flapjack.Compiler.Backend

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def cds : List (Pancake.PanLang.DeclHOL 64) :=
  Candidate.guestAst.map Pancake.PanLang.declToHOL
def cp1 := Pancake.PanStructs.CompileShapeExact.compileTopExact cds
def cp2 := compileTopExactHOL cp1 (Basis.Pure.MlString.ofString "main")
def cp3 : List (Pancake.PanLang.MlS × List Nat × CrepProgHOL 64) := compileProgDeclsHOLW cp2
def cp4 : List (Nat × List Nat × HolLoopProg 64) :=
  compileProgHOLExact Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa cp3
def cw : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  (cp3.map (fun x => x.1)).zip cp4 |>.zipIdx |>.map fun ((nm, (idx, params, body)), i) =>
    (i + 64, params.length + 1, loopToWordCompFuncHOL (i + 64) params body)

unsafe def main : IO Unit := do
  IO.println s!"decls {cds.length} p3 {cp3.length} loop {cp4.length} word {cw.length}"
  for ((nm, _, _), (lbl, argc, _)) in cp3.zip cw do
    IO.println s!"{lbl}\t{argc}\t{Flapjack.Basis.Pure.MlString.toStringOfBytes nm}"
