import InitECandidate.Runtime.WordStackExecutedSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Assembly
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- The quantitative obligation for the actual guest register configuration.
Semantic witnesses outside this configuration use original compiler correctness. -/
def RegisterQualifiedSimulation {F : Type} (ac : AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (budget : Nat) : Prop :=
  ∀ (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (WordSemResult 64))
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (lens : List Nat),
    (WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) →
    f ≤ 92 → k = 22 →
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (targetResult : Option (StackSemResult 64)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens ∧
      stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        compiled {target with clock := target.clock + extraClock} ≤ budget

theorem executedSimulation_of_registers {F : Type} {ac : AsmConfigExact 64}
    {program : WordLangProgHOL (BitVec 64)}
    {source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {budget : Nat}
    (actual : RegisterQualifiedSimulation ac program source budget) :
    ExecutedSimulation ac program source budget := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small
  by_cases registers : k = 22
  · obtain ⟨clock, final, output, run, related, cost⟩ :=
      actual k f frame post target result bs bsPost n nPost compiled lens premises small registers
    exact ⟨clock, final, output, run, related, fun _ => cost⟩
  · obtain ⟨clock, final, output, run, related⟩ :=
      Flapjack.WordToStackProofs.CompCorrect.compCorrect ac program source
        k f frame post target result bs bsPost n nPost compiled lens premises
    exact ⟨clock, final, output, run, related, fun equality => False.elim (registers equality)⟩

theorem ExecutedSimulation.registered {F : Type} {ac : AsmConfigExact 64}
    {program : WordLangProgHOL (BitVec 64)}
    {source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {budget : Nat}
    (simulation : ExecutedSimulation ac program source budget) :
    RegisterQualifiedSimulation ac program source budget := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small registers
  obtain ⟨clock, final, output, run, related, cost⟩ :=
    simulation k f frame post target result bs bsPost n nPost compiled lens premises small
  exact ⟨clock, final, output, run, related, cost registers⟩

#print axioms ExecutedSimulation.registered

#print axioms executedSimulation_of_registers
end InitECandidate.Runtime.WordToStack
