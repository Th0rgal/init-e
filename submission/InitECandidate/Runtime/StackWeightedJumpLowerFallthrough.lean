import InitECandidate.Runtime.StackWeightedCall
import InitECandidate.Runtime.StackWeightedBranch
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

/-- A non-taken JumpLower falls through without executing a callee or
consuming a source call tick. It pays only the visited branch encoding. -/
theorem normalWeightedFlatten_jumpLower_fallthrough {F : Type}
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (regX regY dest : Nat) (x y : BitVec 64)
    (readX : StackSemStateOps.getVar regX source = some (.word x))
    (readY : StackSemStateOps.getVar regY source = some (.word y))
    (chosen : wordCmpHOL .lower x y = false) :
    NormalWeightedFlatten (.jumpLower regX regY dest) source
      (fun encoded pc => LabToTarget.controlWork 3 encoded pc) := by
  intro flag post sectionId labelId continues breaks start encoded hyps
  rcases hyps with ⟨evaluated, _, related, _, installed, _⟩
  rw [StackSemEvaluate.evaluate_jumpLower, readX, readY] at evaluated
  simp only [chosen, Bool.false_eq_true, if_false, Prod.mk.injEq, true_and] at evaluated
  subst post
  have fetch : asmFetchAux start.pc start.code =
      some (.labAsm (.jumpCmp .lower regX (.reg regY) (.lab dest 0)) 0 [] 0) :=
    fetchSingle rfl
      (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using installed)
  have branchChosen : wordSemWordCmp .lower (start.regs regX) (regImm (.reg regY) start) = some false := by
    simp [regImm, InstCorrect.regOfLookup related readX, InstCorrect.regOfLookup related readY,
      wordSemWordCmp, chosen]
  have trace := branch_fallthrough_update_weighted start encoded .lower regX (.reg regY)
    (.lab dest 0) fetch branchChosen
  refine ⟨incPc start, 1, LabToTarget.controlWork 3 encoded start.pc, related, ?_, rfl,
    Nat.le_refl _, trace.toMixed⟩
  simp [incPc, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]

#print axioms normalWeightedFlatten_jumpLower_fallthrough
end InitECandidate.Runtime.StackToLab
