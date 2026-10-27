import Tools.WordStageData
import InitECandidate.Proofs.SmallOptimizerComputation

/- Native evaluation proposes literals only. Every output below receives an
independent standard-axiom equation before it is used in a certificate. -/
open Lean Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitE.GenSmallStages

def prepare (env : Environment) (label argc : Nat)
    (source : WordLangProgHOL (BitVec 64)) (oracle : Option (Spt Nat)) : IO Unit := do
  let regs := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)
  let p0 := WordSimp.compileExp source
  let p1 := WordInst.instSelectExecutable riscvConfig (maxVarHOL p0 + 1) p0
  let p2 := WordAlloc.fullSsaCcTrans argc p1
  let p3 := WordAlloc.removeDeadProg p2
  let p4 := WordCse.wordCommonSubexpElim p3
  let p5 := WordCopy.copyProp p4
  let p6 := WordInst.threeToTwoRegProg riscvConfig.twoRegArith p5
  let p7 := WordUnreach.removeUnreach p6
  let p8 := WordAlloc.removeDeadProg p7
  let p9 := WordToWord.wordAllocWith RegAlloc.regAllocExecutable label riscvConfig 3 regs p8 oracle
  let p10 := WordRemove.removeMustTerminate p9
  let passes := #[p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10]
  let ns := s!"InitECandidate.Proofs.SmallStages.Compact{label}"
  let header := "set_option autoImplicit false\nset_option Elab.async false\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option cbv.maxSteps 1000000000\nset_option cbv.warning false\nopen scoped InitECandidate.Proofs.SmallOptimizerComputation InitECandidate.Proofs.ClashComputation\nopen Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target\nopen InitECandidate.Proofs.WordStages\n"
  let dir := s!"submission/InitECandidate/Proofs/SmallStages/Compact{label}"
  IO.FS.createDirAll dir
  let oracleText ← renderWordStage env (toExpr oracle)
  let mut data := s!"import InitECandidate.Proofs.SmallOptimizerComputation\nimport InitECandidate.Proofs.WordStages.Source{label}\n" ++ header ++ s!"namespace {ns}\ndef oracle : Option (Spt Nat) :=\n{oracleText}\n"
  let st ← IO.mkRef ({} : PancakeDataState)
  for index in [2,3,4,5,6,7,8,10] do
    st.modify fun state => { state with tag := s!"body{index}_", lines := #[] }
    let body ← wordProgData env st ((passes[index]?).getD .skip)
    data := data ++ String.intercalate "\n" (← st.get).lines.toList ++ s!"\ndef pass{index} : WordLangProgHOL (BitVec 64) := {body}\n"
  data := data ++ s!"end {ns}\n"
  IO.FS.writeFile s!"{dir}/Data.lean" data
  let exprs := #[
    s!"WordSimp.compileExp source{label}.2.2",
    "WordInst.instSelectExecutable riscvConfig (maxVarHOL pass0 + 1) pass0",
    s!"(let p0 := WordSimp.compileExp source{label}.2.2; let p1 := WordInst.instSelectExecutable riscvConfig (maxVarHOL p0 + 1) p0; WordAlloc.fullSsaCcTrans {argc} p1)",
    "WordAlloc.removeDeadProg pass2",
    "WordCse.wordCommonSubexpElim pass3",
    "WordCopy.copyProp pass4",
    "WordInst.threeToTwoRegProg riscvConfig.twoRegArith pass5",
    "WordUnreach.removeUnreach pass6",
    "WordAlloc.removeDeadProg pass7",
    s!"WordToWord.wordAllocWith RegAlloc.regAllocExecutable {label} riscvConfig 3 (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) pass8 oracle",
    s!"WordRemove.removeMustTerminate (WordToWord.wordAllocWith RegAlloc.regAllocExecutable {label} riscvConfig 3 (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) pass8 oracle)"]
  for index in [2,3,4,5,6,7,8,10] do
    let proof := if index == 2 then
      "  dsimp only\n  rw [InitECandidate.Proofs.SmallSsaKernelComputation.fullSsaStructural_eq]\n  kernel_rfl\n"
      else "  kernel_rfl\n"
    IO.FS.writeFile s!"{dir}/Pass{index}.lean"
      ("import InitECandidate.Proofs.CompactComputation\n" ++
       (if index == 2 then "import InitECandidate.Proofs.SmallSsaKernelComputation\n" else "") ++
       s!"import {ns}.Data\n" ++ header ++ s!"namespace {ns}\ntheorem pass{index}_eq : {exprs[index]!} = pass{index} := by\n" ++ proof ++ s!"#print axioms pass{index}_eq\nend {ns}\n")
  IO.println s!"Prepared {label}: {data.utf8ByteSize} bytes, 8 independently checked pass proposals"

end InitE.GenSmallStages
