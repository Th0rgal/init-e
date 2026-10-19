import InitECandidate.Runtime.PayloadSplitReturnedEntries
import InitECandidate.Runtime.PayloadSplitEntryReturned
import InitECandidate.Runtime.PayloadTransactionSpan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Ordered offsets and the original transaction-list suffix export the variable hash entries and their input-based bounds. -/
theorem payload_offset_returned_entries {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offsets length payload pointer heapPointer : BitVec 64) (value : ValueHOL 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (afterPayload : payload.toNat + 136 ≤ heapPointer.toNat)
    (small : length.toNat ≤ 134217712)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header16 : state.memaddrs (payload + 16)) (header24 : state.memaddrs (payload + 24))
    (header32 : state.memaddrs (payload + 32)) (header40 : state.memaddrs (payload + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    ∃ array count withdrawals balance : BitVec 64,
      withdrawals.toNat ≤ balance.toNat ∧ balance.toNat ≤ length.toNat ∧
      count.toNat ≤ 134217712 ∧ ((balance - withdrawals) / 44).toNat ≤ 134217712 ∧
      (length - balance).toNat ≤ 134217712 ∧
      RlpSliceEntry post payload 2 array count ∧
      RlpSliceEntry post payload 3 (pointer + withdrawals) ((balance - withdrawals) / 44) ∧
      RlpSliceEntry post payload 4 (pointer + balance) (length - balance) := by
  obtain ⟨txs,withdrawals,balance,entry,output,txLower,txUpper,txWd,wdBal,balLength,tail,
      locals,installed,domain,globals,_,_,postMemory,postGlobals,postDomain⟩ :=
    payload_split_entry_returned state post offsets length payload pointer value atOffsets atLength atPayload atPointer
      domain0 domain8 domain16 domain24 header16 header24 code run
  have pl : entry.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atPayload
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atPointer
  have tx : entry.locals.lookup (ofString "o_txs") = some (.val (.word txs)) := by
    rw [locals]
    simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_txs" by decide,show ofString "o_wd" ≠ ofString "o_txs" by decide]
  have wd : entry.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)) := by
    rw [locals]
    simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_wd" by decide]
  have bal : entry.locals.lookup (ofString "o_bal") = some (.val (.word balance)) := by
    rw [locals]; simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE]
  have span := payload_transaction_span pointer length txs withdrawals txWd (by omega) inputFits
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atLength
  obtain ⟨array,count,countBound,entries⟩ := payload_split_returned_entries entry output payload pointer txs withdrawals balance heapPointer length
    value pl p len tx wd bal (by rw [globals]; exact heap) heapBound aligned afterPayload
    (by have inside := span.2.2.1; omega) (by rw [domain]; exact header32) (by rw [domain]; exact header40)
    (installed.trans code) tail
  have bounds := payload_tail_hash_bounds length withdrawals balance small wdBal balLength
  have txLength : (withdrawals - txs).toNat ≤ length.toNat := by
    rw [BitVec.toNat_sub_of_le txWd]; omega
  refine ⟨array,count,withdrawals,balance,wdBal,balLength,(by omega),bounds.1,bounds.2,?_,?_,?_⟩
  · exact entries.1.after_frame output post payload 2 _ _ postDomain (congrFun postMemory _) (congrFun postMemory _)
  · exact entries.2.1.after_frame output post payload 3 _ _ postDomain (congrFun postMemory _) (congrFun postMemory _)
  · exact entries.2.2.after_frame output post payload 4 _ _ postDomain (congrFun postMemory _) (congrFun postMemory _)

#print axioms payload_offset_returned_entries
end InitECandidate.Runtime
