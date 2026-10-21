import InitECandidate.Runtime.SSALoopSetupExecutedCost
import InitECandidate.Runtime.WordLineCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticInst

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
set_option maxHeartbeats 6000000

/-- Exact per-pair overhead of the fixed-register moves inserted by SSA.
Ordinary instructions have no overhead; variable shifts insert one pair,
long multiplication/division four, and carry/overflow their actual pairs. -/
def ssaInstructionMovePrice : WordLangInst (BitVec 64) → Nat
  | .arith (.shift _ _ _ (.reg _)) => 24
  | .arith (.longMul _ _ _ _) | .arith (.longDiv _ _ _ _ _) => 96
  | .arith (.addCarry _ _ _ _) => 48
  | .arith (.addOverflow _ _ _ _) | .arith (.subOverflow _ _ _ _) => 24
  | _ => 0

/-- Straight fragments emitted by SSA instruction conversion. -/
def optimizerInstructionLeaf : WordLangProgHOL (BitVec 64) → Option Nat
  | .skip => some 0
  | .inst instruction => some (max 24 (WordToStack.refinedNativeInstructionPrice (HolInst.ofWordLangInst instruction)))
  | .move _ pairs => some (24 * pairs.length)
  | _ => none

/-- Check every actual SSA instruction constructor, including its emitted
fixed-register pre/post moves. No compiled-code run or cost is assumed. -/
theorem ssa_instruction_line_budget (instruction : WordLangInst (BitVec 64))
    (map : Spt Nat) (next : Nat) :
    ∃ n, lineBound optimizerInstructionLeaf (ssaCcTransInst instruction map next).1 = some n ∧
      n ≤ max 24 (WordToStack.refinedNativeInstructionPrice (HolInst.ofWordLangInst instruction)) +
        ssaInstructionMovePrice instruction := by
  cases instruction with
  | skip | const _ _ =>
    simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, optimizerInstructionLeaf,
      HolInst.ofWordLangInst, WordToStack.refinedNativeInstructionPrice, ssaInstructionMovePrice]
  | arith operation =>
    cases operation with
    | binop op dst src operand | shift op dst src operand =>
      cases operand <;> simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, optimizerInstructionLeaf,
        HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
        WordToStack.refinedNativeInstructionPrice, ssaInstructionMovePrice]
    | _ => simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, optimizerInstructionLeaf,
        HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm,
        WordToStack.refinedNativeInstructionPrice, ssaInstructionMovePrice]
  | mem operation destination address =>
    cases address
    cases operation <;> simp [ssaCcTransInst, nextVarRename, lineBound, isLeafProg, optimizerInstructionLeaf,
      HolInst.ofWordLangInst, HolAddr.ofWordLangAddr, WordToStack.refinedNativeInstructionPrice,
      ssaInstructionMovePrice]

theorem optimizerInstructionLeaf_sound {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) (n : Nat)
    (priced : optimizerInstructionLeaf program = some n) : wordOptimizerLocalPrice program source ≤ n := by
  cases program <;> simp only [optimizerInstructionLeaf, reduceCtorEq, Option.some.injEq] at priced
  all_goals subst n
  all_goals exact Nat.le_refl _

/-- Actual SSA instruction work is bounded with coefficient one, plus only
the fixed-register moves required by that opcode. The bound is independent
of the chosen source permutation, because the source node is atomic. -/
theorem ssa_instruction_executed_cost {C F C' F' : Type}
    (instruction : WordLangInst (BitVec 64)) (map : Spt Nat) (next : Nat)
    (source : WordSemStateFiniteExact 64 C F) (target : WordSemStateFiniteExact 64 C' F') :
    wordExecutionCost wordOptimizerLocalPrice (ssaCcTransInst instruction map next).1 target ≤
      wordExecutionCost wordOptimizerLocalPrice (.inst instruction) source + ssaInstructionMovePrice instruction := by
  obtain ⟨n, line, bound⟩ := ssa_instruction_line_budget instruction map next
  have runCost := wordCost_le_lineBound wordOptimizerLocalPrice optimizerInstructionLeaf
    (fun _ _ _ => rfl) (fun p s n _ priced => optimizerInstructionLeaf_sound p s n priced)
    _ n line target
  rw [wordExecutionCost_atomic wordOptimizerLocalPrice (.inst instruction) source rfl]
  exact runCost.trans bound

/-- Keep the original semantic permutation witness and the executed-cost
bound together for the actual instruction compiler. All original SSA entry
premises are retained; no target execution is supplied by a caller. -/
theorem ssa_instruction_semantics_and_cost {C F : Type}
    (instruction : WordLangInst (BitVec 64)) (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (premises : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.inst instruction) = true ∧
      ssaMapOK next map ∧ ltOK tables) :
    ssaSimulation (.inst instruction) source target map next tables ∧
      ∀ permutation : Nat → Nat → Nat,
        wordExecutionCost wordOptimizerLocalPrice (ssaCcTrans (.inst instruction) map next tables).1 target ≤
          wordExecutionCost wordOptimizerLocalPrice (.inst instruction) {source with permute := permutation} +
            ssaInstructionMovePrice instruction := by
  refine ⟨ssaCcTransCorrectInst source target map next instruction tables premises, ?_⟩
  intro permutation
  simpa only [ssaCcTrans] using ssa_instruction_executed_cost instruction map next
    {source with permute := permutation} target

#print axioms ssa_instruction_line_budget
#print axioms optimizerInstructionLeaf_sound
#print axioms ssa_instruction_executed_cost
#print axioms ssa_instruction_semantics_and_cost
end InitECandidate.Runtime.FineCost
