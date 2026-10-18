import InitECandidate.Runtime.TransactionTypeScopeBound
import InitECandidate.Runtime.TransactionCountScopeHeapBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_scope_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (budget : transactionTypedSuffixCost inputLength.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 7)
    state.clock ≤ evaluated.2.clock + transactionTypedSuffixCost inputLength.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let value : ValueHOL 64 := .val (.word 0)
  let middle := setVarHOLFinite (ofString "t") value state
  have locals : ∀ key, key ≠ ofString "t" → middle.locals.lookup key = state.locals.lookup key := by
    intro key different
    simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have installed : middle.locals.lookup (ofString "t") = some (.val (.word (0 : BitVec 64))) := by
    simp [middle,value,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := transaction_count_scope_heap_bounded middle input inputLength scratch frame array tx kind ceiling inputLimit
    ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal) positive noWrap inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    inputBeforeFrame inputBeforeArray ((locals _ (by decide)).trans txLocal) installed ((locals _ (by decide)).trans byteLocal) headerBefore arrayAbove budget
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.const 0) = some value := by
    simp [value,evalHOLExact]
  have checked : shapeEqHOL .one (shapeOfHOLExact value) = true := by
    simp [value,shapeOfHOLExact,shapeEqHOL]
  rw [source_transaction_t_scope,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  dsimp only
  rw [checked]
  exact bounded

#print axioms source_transaction_t_scope
#print axioms transaction_type_scope_heap_bounded
end InitECandidate.Runtime
