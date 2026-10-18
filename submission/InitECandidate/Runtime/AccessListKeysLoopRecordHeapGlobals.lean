import InitECandidate.Runtime.AccessListKeysLoopHeapGlobals
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_keys_loop_and_record_heap_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessKeysLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (run : evaluateHOLFiniteState state accessKeysLoopAndRecord = (none,post)) :
    post.globals = state.globals := by
  rw [source_access_keys_loop_and_record,evaluateHOLFiniteState_seq_line780] at run
  cases loopRun : evaluateHOLFiniteState state accessKeysLoop with
  | mk result middle =>
    rw [loopRun] at run
    cases result with
    | some result => cases run
    | none =>
      have same := access_keys_loop_normal_heap_globals state middle array count buffer input inputLength scratch frame ceiling inputLimit valid
        inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeBuffer aligned fits budget loopRun
      apply HolFiniteMapExact.ext
      funext watched
      have supported : avoidsGlobalAssignment watched accessRecordScope = true := by
        simp only [accessRecordScope,accessKeysLoopAndRecord,accessAt,authorizationNext,sourceFunctionBody,
          InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
        rfl
      have retained := evaluate_avoidsGlobalAssignment watched accessRecordScope supported middle
      dsimp only at run
      rw [run] at retained
      exact retained.trans (congrArg (fun g => g.lookup watched) same)

#print axioms access_keys_loop_and_record_heap_globals
end InitECandidate.Runtime
