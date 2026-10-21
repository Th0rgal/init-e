import InitECandidate.Runtime.StackWeightedCall
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

/-- Returning-call entry charges its visited return-label materialization and
actual callee jump. The extra clock unit belongs to the materialization;
the jump consumes the original source call unit. -/
theorem callEnter_weighted {F : Type}
    {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {start : LabSem.State 64 LabToTarget.Config F}
    {link l1 l2 : Nat} {dest : Nat ⊕ Nat} {prog : HolProg 64}
    (encoded : LabProgHOL 64) (related : stateRel source start)
    (positive : source.clock ≠ 0)
    (fetchA : asmFetchAux start.pc start.code = some (.labAsm (.locValue link (.lab l1 l2)) 0 [] 0))
    (fetchB : asmFetchAux (start.pc + 1) start.code = some (compileJumpHOL dest))
    (returnLocation : locToPc l1 l2 start.code = some (start.pc + 2))
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog) :
    ∃ (calleeSection pc : Nat) (middle : LabSem.State 64 LabToTarget.Config F),
      middle.code = start.code ∧ middle.pc = pc ∧
      stateRel (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) middle ∧
      locToPc calleeSection 0 start.code = some pc ∧
      StackProps.callArgs prog start.ptrReg start.lenReg start.ptr2Reg start.len2Reg start.linkReg ∧
      codeInstalled pc (appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL true prog
        calleeSection (StackAlloc.nextLabHOL prog 2) [] []).1) start.code ∧
      LabToTarget.WeightedMixedTrace encoded {start with clock := start.clock + 1} middle
        (LabToTarget.controlWork 2 encoded start.pc + callJumpWork dest) := by
  let beforeJump := incPc (updReg link (.loc l1 l2) start)
  have relBefore : stateRel (StackSemStateOps.setVar link (.loc l1 l2) source) beforeJump :=
    StateRel.setVarUpdReg related
  have regs : ∀ r v, (source.regs.eraseEq link).lookup r = some v → beforeJump.regs r = v := by
    intro r v read
    simp only [HolFiniteMapExact.eraseEq, FDOMSUB_HOL] at read
    split_ifs at read with different
    simp only [beforeJump, incPc, updReg, different, if_false]
    exact InstCorrect.regOfLookup related read
  obtain ⟨calleeSection, pc, lookup, entry, args, installed, middleRel, jump⟩ :=
    compileJumpEnter_weighted encoded regs relBefore positive fetchB found
  let middle := {beforeJump with pc := pc, clock := beforeJump.clock - 1}
  have materialize := locvalue_update_weighted start encoded link (.lab l1 l2) (start.pc + 2)
    fetchA (by simpa [getPcValue] using returnLocation)
  refine ⟨calleeSection, pc, middle, rfl, rfl, middleRel, entry, args, installed, ?_⟩
  have joined := LabToTarget.weightedMixedTrace_append materialize.toMixed jump
  simpa only [beforeJump, middle, labToLoc] using joined

#print axioms callEnter_weighted
end InitECandidate.Runtime.StackToLab
