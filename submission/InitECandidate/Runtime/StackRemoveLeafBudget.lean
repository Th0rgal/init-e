import InitECandidate.Runtime.StackRemoveZeroBudget
import InitECandidate.Runtime.StackRemoveMemoryBudget

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate

/-- Constructors with zero additional stack clock under the full relation. -/
def zeroClockLeaf {width : Nat} [NeZero width] : HolProg width → Bool
  | .call _ _ _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .jumpLower _ _ _ | .rawCall _
  | .stackAlloc _ | .storeConsts _ _ _ => false
  | _ => true

local macro "normalize_result" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨clock, zero, post, run, relation⟩
    refine ⟨clock, zero, post, run, ?_⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

theorem zeroClockLeaf_correct {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (leaf : zeroClockLeaf program = true)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
      stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound program pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
        (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  cases program
  all_goals first
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectFFI _ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectGet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectSet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectBitmapLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectInstall _ _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectDataBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectSkip _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectHalt _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectAlloc _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackLoadAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackStoreAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectLocValue _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectTick _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectReturn _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectRaise _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectBreak _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectContinue _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectShMemOp _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackFree _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectOpCurrHeap _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackStore _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectInst _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectCodeBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackGetSize _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackSetSize _ _ _ _ _ _ _ _ hypothesis))
    | solve | simp [zeroClockLeaf] at leaf

#print axioms zeroClockLeaf_correct
end InitECandidate.Runtime.StackRemove
