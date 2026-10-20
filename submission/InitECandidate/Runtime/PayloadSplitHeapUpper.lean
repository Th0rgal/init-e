import InitECandidate.Runtime.SszSplitDeclarationHeapUpper
import InitECandidate.Runtime.PayloadSplitReturnedSlices
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned original payload list declaration and complete remaining tail
retain readable transaction slices, the installed header pointer/count, and a
capped aligned heap beyond the slice array. -/
theorem payload_split_returned_slices_heap_upper {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload pointer txs withdrawals balance heapPointer : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
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
    ∃ array count nextHeap : BitVec 64,
      RlpSliceInputPrefix post array (pointer + txs) (withdrawals - txs) count.toNat ∧
      count.toNat ≤ (withdrawals - txs).toNat / 4 ∧
      post.memory (payload + 32) = .word array ∧ post.memory (payload + 40) = .word count ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧ heapPointer.toNat ≤ nextHeap.toNat ∧
      array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧ (count = 0 ∨ payload.toNat + 136 ≤ array.toNat) ∧
      nextHeap.toNat≤heapPointer.toNat+4*(withdrawals-txs).toNat+7 := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadSplitArguments = some [.val (.word (pointer + txs)),.val (.word (withdrawals - txs)),
        .val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadSplitArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atTxs,atWithdrawals,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_payload_split_call] at run
  obtain ⟨array,count,nextHeap,ready,output,tail,locals,installed,domain,inputPrefix,countBound,
      nextGlobal,nextBound,nextAligned,growth,arrayBefore,origin,postMemory,postGlobals,postDomain,upper⟩ :=
    sszSplitVarList_declaration_array_origin_heap_upper state post (ofString "txs") (payloadAt 17) payloadSplitArguments
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
  have above : count = 0 ∨ payload.toNat + 136 ≤ array.toNat := by
    rcases origin with zero | rfl
    · exact Or.inl zero
    · exact Or.inr afterPayload
  obtain ⟨retained,tailGlobals⟩ := payload_transaction_suffix_input_prefix ready output payload array count withdrawals balance
    (pointer + txs) (withdrawals - txs) value pl list wd bal d32 d40 above (by omega) inputPrefix (installed.trans code) tail
  have header := payload_transaction_header_returned ready output payload array count withdrawals balance value
    pl list wd bal d32 d40 (installed.trans code) tail
  have finalPrefix : RlpSliceInputPrefix post array (pointer + txs) (withdrawals - txs) count.toNat := by
    intro index inside
    obtain ⟨p,n,item⟩ := retained index inside
    exact ⟨p,n,item.after_frame output post array index p n (pointer + txs) (withdrawals - txs)
      postDomain (congrFun postMemory _) (congrFun postMemory _)⟩
  refine ⟨array,count,nextHeap,finalPrefix,countBound,?_,?_,?_,nextBound,nextAligned,growth,arrayBefore,above,upper⟩
  · rw [postMemory]; exact header.1
  · rw [postMemory]; exact header.2
  · rw [postGlobals,tailGlobals]; exact nextGlobal

#print axioms payload_split_returned_slices_heap_upper
end InitECandidate.Runtime
