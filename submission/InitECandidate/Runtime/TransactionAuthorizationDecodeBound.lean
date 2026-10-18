import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.AuthorizationsDeclarationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual transaction authorization decoding includes both result stores and index advance. -/
theorem evaluate_transaction_authorization_decode_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "aul") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (arrayAligned : array.toNat % 8 = 0)
    (reserve : array.toNat + length.toNat * 248 ≤ frame.toNat)
    (budget : authorizationBodyCost length.toNat + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionAuthorizationDecode
    state.clock ≤ evaluated.2.clock + (authorizationBodyCost length.toNat + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.rfield 0 (.var .local (ofString "aul")),.rfield 1 (.var .local (ofString "aul"))] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal]
  rw [source_transaction_authorization_decode]
  exact evaluate_authorization_declaration_bounded state (ofString "au") transactionAuthorizationFinish (by rfl) _
    pointer length scratch frame array ceiling inputLimit args noWrap lengthBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
    arrayBeforeFrame arrayAligned reserve budget

#print axioms evaluate_transaction_authorization_decode_bounded
end InitECandidate.Runtime
