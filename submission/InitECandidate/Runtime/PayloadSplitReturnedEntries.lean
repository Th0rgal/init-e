import InitECandidate.Runtime.SszSplitVarListDeclarationArrayOrigin
import InitECandidate.Runtime.PayloadSplitSuffixBound
import InitECandidate.Runtime.PayloadTransactionSuffixInputPrefix
import InitECandidate.Runtime.PayloadTransactionHeaderReturnedEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual transaction-list declaration exports the hash slice entries through the full remaining payload suffix. -/
theorem payload_split_returned_entries {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload pointer txs withdrawals balance heapPointer length : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atTxs : state.locals.lookup (ofString "o_txs") = some (.val (.word txs)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (afterPayload : payload.toNat + 136 ≤ heapPointer.toNat)
    (inputFits : (pointer + txs).toNat + (withdrawals - txs).toNat < 2 ^ 64)
    (header32 : state.memaddrs (payload + 32)) (header40 : state.memaddrs (payload + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 16) = (some (.returned value),post)) :
    ∃ array count : BitVec 64, count.toNat ≤ (withdrawals - txs).toNat / 4 ∧
      RlpSliceEntry post payload 2 array count ∧
      RlpSliceEntry post payload 3 (pointer + withdrawals) ((balance - withdrawals) / 44) ∧
      RlpSliceEntry post payload 4 (pointer + balance) (length - balance) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadSplitArguments = some [.val (.word (pointer + txs)),.val (.word (withdrawals - txs)),
        .val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadSplitArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atTxs,atWithdrawals,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_payload_split_call] at run
  obtain ⟨array,count,nextHeap,ready,output,tail,locals,installed,domain,inputPrefix,countBound,
      nextGlobal,nextBound,nextAligned,growth,arrayBefore,origin,postMemory,postGlobals,postDomain⟩ :=
    sszSplitVarList_declaration_array_origin state post (ofString "txs") (payloadAt 17) payloadSplitArguments
      (pointer + txs) (withdrawals - txs) 9223372036854775807 heapPointer value args code heap heapBound aligned inputFits run
  have pl : ready.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atPayload,show ofString "txs" ≠ ofString "pl" by decide]
  have list : ready.locals.lookup (ofString "txs") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have wd : ready.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atWithdrawals,show ofString "txs" ≠ ofString "o_wd" by decide]
  have bal : ready.locals.lookup (ofString "o_bal") = some (.val (.word balance)) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,atBalance,show ofString "txs" ≠ ofString "o_bal" by decide]
  have d32 : ready.memaddrs (payload + 32) := by rw [domain]; exact header32
  have d40 : ready.memaddrs (payload + 40) := by rw [domain]; exact header40
  have p : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,atPointer,show ofString "txs" ≠ ofString "p" by decide]
  have len : ready.locals.lookup (ofString "len") = some (.val (.word length)) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,atLength,show ofString "txs" ≠ ofString "len" by decide]
  have entries := payload_transaction_header_returned_entries ready output payload array count withdrawals balance pointer length value
    pl list wd bal p len d32 d40 (installed.trans code) tail
  exact ⟨array,count,countBound,
    entries.1.after_frame output post payload 2 _ _ postDomain (congrFun postMemory _) (congrFun postMemory _),
    entries.2.1.after_frame output post payload 3 _ _ postDomain (congrFun postMemory _) (congrFun postMemory _),
    entries.2.2.after_frame output post payload 4 _ _ postDomain (congrFun postMemory _) (congrFun postMemory _)⟩

#print axioms payload_split_returned_entries
end InitECandidate.Runtime
