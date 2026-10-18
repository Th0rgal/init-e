import InitECandidate.Runtime.TransactionByteScopeBound
import InitECandidate.Runtime.TransactionAllocationSuffixHeapBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_byte_scope_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (positive : 0 < inputLength.toNat) (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (txBound : tx.toNat + 400 ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ tx.toNat)
    (heapAbove : ceiling ≤ tx.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionAllocationSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 1)
    state.clock ≤ evaluated.2.clock + transactionAllocationSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_transaction_byte_scope,evaluateHOLFiniteState_dec_total]
  dsimp only
  cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be input with
  | none =>
    have initial : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.loadByte (.var .local (ofString "p"))) = none := by
      simp [evalHOLExact,pointerLocal,loaded]
    rw [initial]
    exact ⟨by change state.clock ≤ state.clock + _; omega,Nat.le_refl _,by simp⟩
  | some byte =>
    let kind := BitVec.ofNat 64 byte.toNat
    let middle := setVarHOLFinite (ofString "b0") (.val (.word kind)) state
    have locals : ∀ key, key ≠ ofString "b0" → middle.locals.lookup key = state.locals.lookup key := by
      intro key different
      simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have atByte : middle.locals.lookup (ofString "b0") = some (.val (.word kind)) := by
      simp [middle,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have bounded := transaction_allocation_suffix_heap_bounded middle input inputLength scratch frame tx kind ceiling inputLimit
      ((locals _ (by decide)).trans pointerLocal) ((locals _ (by decide)).trans lengthLocal) positive noWrap inputBound limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap txBound countLimit heapArena
      inputBeforeFrame inputBeforeArray atByte heapAbove txAligned budget
    have initial : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.loadByte (.var .local (ofString "p"))) = some (.val (.word kind)) := by
      simp [kind,evalHOLExact,pointerLocal,loaded]
    rw [initial]
    dsimp only
    have checked : shapeEqHOL .one (shapeOfHOLExact (.val (.word kind))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
    rw [checked]
    exact bounded

#print axioms source_transaction_byte_scope
#print axioms transaction_byte_scope_heap_bounded
end InitECandidate.Runtime
