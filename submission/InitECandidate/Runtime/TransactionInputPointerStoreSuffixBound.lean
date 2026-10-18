import InitECandidate.Runtime.TransactionInputLengthStoreSuffixBound
import InitECandidate.Runtime.StraightLocalFrame
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.StraightLineNoTimeout
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionInputPointerStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "tx"),.const 384]) (.var .local (ofString "p"))

theorem source_transactionInputPointerStore : transactionAt 4 = .seq transactionInputPointerStore (transactionAt 5) := by
  simp only [transactionInputPointerStore,transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transaction_input_pointer_store_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame array tx kind : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (positive : 0 < inputLength.toNat) (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : array.toNat + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (budget : transactionTypedSuffixCost inputLength.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 4)
    state.clock ≤ evaluated.2.clock + transactionTypedSuffixCost inputLength.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have clock := clockPreserving_of_straightLine transactionInputPointerStore (by rfl) state
  have noTimeout := evaluate_straightLine_no_timeout transactionInputPointerStore (by rfl) state
  have locals : ∀ key, (evaluateHOLFiniteState state transactionInputPointerStore).2.locals.lookup key = state.locals.lookup key :=
    fun key => evaluate_straight_local_frame key transactionInputPointerStore (by rfl) state
  have globals : ∀ key, (evaluateHOLFiniteState state transactionInputPointerStore).2.globals.lookup key = state.globals.lookup key :=
    fun key => evaluate_avoidsGlobalAssignment key transactionInputPointerStore (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state transactionInputPointerStore
  rw [source_transactionInputPointerStore,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state transactionInputPointerStore with
  | mk result post =>
    rw [stored] at clock noTimeout locals globals metadata
    dsimp only at clock noTimeout locals globals metadata
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,noTimeout⟩
    | none =>
      dsimp only
      have bounded := transaction_input_length_store_suffix_bounded post input inputLength scratch frame array tx kind ceiling inputLimit
        ((locals _).trans pointerLocal) ((locals _).trans lengthLocal) positive noWrap inputBound limitBound
        ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal) (metadata.1.trans code) orderedFrame framePositive scratchBelow
        (by intro address low high; rw [metadata.2.1]; exact arena address low high)
        ((globals _).trans heap) arrayBound countLimit
        (by intro address low high; rw [metadata.2.1]; exact heapArena address low high)
        inputBeforeFrame inputBeforeArray ((locals _).trans txLocal) ((locals _).trans byteLocal) headerBefore reserve (by rw [clock]; exact budget)
      exact ⟨by have spent := bounded.1; omega,by have remaining := bounded.2.1; omega,bounded.2.2⟩

#print axioms source_transactionInputPointerStore
#print axioms transaction_input_pointer_store_suffix_bounded
end InitECandidate.Runtime
