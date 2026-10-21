import InitECandidate.Runtime.WordStackAllInstructionCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Inst
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

/-- Quantitative Word-to-Stack simulation. The budget is a bound to prove,
not an assumed target run or an additional-clock allowance. All original
compiler correctness premises and result/resource postconditions remain.
The frame limit and quantitative register guard specialize the cost proof to
the concrete guest (22 allocatable registers). Original semantic witnesses
remain available for every register count. -/
def ExecutedSimulation {F : Type} (ac : AsmConfigExact 64)
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
    f ≤ 92 →
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (targetResult : Option (StackSemResult 64)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens ∧
      (k = 22 → stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
        compiled {target with clock := target.clock + extraClock} ≤ budget)

theorem ExecutedSimulation.mono {F : Type} {ac : AsmConfigExact 64}
    {program : WordLangProgHOL (BitVec 64)}
    {source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {a b : Nat}
    (simulation : ExecutedSimulation ac program source a) (bound : a ≤ b) :
    ExecutedSimulation ac program source b := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small
  obtain ⟨clock, final, output, run, related, cost⟩ :=
    simulation k f frame post target result bs bsPost n nPost compiled lens premises small
  exact ⟨clock, final, output, run, related, fun actualRegisters => (cost actualRegisters).trans bound⟩

/-- The original instruction correctness witness now also carries a bound
on the actual reached target fragment, including spill reads and writes. -/
theorem executedSimulation_inst {F : Type} (ac : AsmConfigExact 64)
    (instruction : WordLangInst (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.inst instruction) source 43 := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises small
  obtain ⟨clock, final, output, run, related⟩ :=
    Flapjack.WordToStackProofs.CompCorrect.Inst.compCorrectInst ac instruction source
      k f frame post target result bs bsPost n nPost compiled lens premises
  refine ⟨clock, final, output, run, related, ?_⟩
  intro actualRegisters
  have programEq := congrArg Prod.fst premises.2.2.2.2.2.1
  simp only [compNative] at programEq
  rw [← programEq]
  exact wordInst_cost (HolInst.ofWordLangInst instruction) (k, f, frame) small _

#print axioms ExecutedSimulation.mono
#print axioms executedSimulation_inst
end InitECandidate.Runtime.WordToStack
