import InitECandidate.Runtime.SszSplitVarListCallBound
import InitECandidate.Runtime.PayloadTransactionHeaderSuffixBound
import InitECandidate.Runtime.PanDecCallContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadSplitArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.var .local (ofString "o_txs")],
    .op .sub [.var .local (ofString "o_wd"),.var .local (ofString "o_txs")],.const 9223372036854775807]

theorem source_payload_split_call : payloadAt 16 =
    .decCall (ofString "txs") (.comb [.one,.one]) (ofString "ssz_split_var_list") payloadSplitArguments (payloadAt 17) := by
  simp only [payloadSplitArguments,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual transaction-list declaration and full remaining payload tail
are bounded, including SSZ and allocator rejection and failed header stores. -/
theorem evaluate_payload_split_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer txs withdrawals balance heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atTxs : state.locals.lookup (ofString "o_txs") = some (.val (.word txs)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (budget : sszSplitBound (withdrawals - txs) + 68 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 16)
    state.clock ≤ evaluated.2.clock + (sszSplitBound (withdrawals - txs) + 68) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadSplitArguments = some [.val (.word (pointer + txs)),.val (.word (withdrawals - txs)),
        .val (.word (9223372036854775807 : BitVec 64))] := by
    simp [payloadSplitArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atTxs,atWithdrawals,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word (pointer + txs)))).update
      (ofString "len",.val (.word (withdrawals - txs)))).update (ofString "lim",.val (.word (9223372036854775807 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word (pointer + txs))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide,show ofString "lim" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word (withdrawals - txs))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "lim" ≠ ofString "len" by decide]
  have atLimit : entry.locals.lookup (ofString "lim") = some (.val (.word (9223372036854775807 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_sszSplitVarList_body entry (pointer + txs) (withdrawals - txs) (9223372036854775807 : BitVec 64) heapPointer code atPointer atLength atLimit heap pointerBound
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "ssz_split_var_list")
    (ofString "p") (ofString "len") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
    (.comb [.one,.one]) (pointer + txs) (withdrawals - txs) (9223372036854775807 : BitVec 64) (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_sszSplitVarList_lookup)
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
  rw [source_payload_split_call]
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list) with
  | mk result post =>
    rw [bodyRun] at bounded metadata
    dsimp only at bounded metadata
    have spent : state.clock ≤ post.clock + (sszSplitBound (withdrawals - txs) + 1) := by
      have consumed := bounded.1
      change state.clock - 1 ≤ post.clock + sszSplitBound (withdrawals - txs) at consumed
      omega
    have composed := evaluate_decCall_continuation_bounded state post (ofString "txs") (ofString "ssz_split_var_list")
      (.comb [.one,.one]) (.comb [.one,.one]) payloadSplitArguments
      [.val (.word (pointer + txs)),.val (.word (withdrawals - txs)),.val (.word (9223372036854775807 : BitVec 64))]
      (sourceFunctionBody Guest.guestFn_ssz_split_var_list) (payloadAt 17) callee result
      (sszSplitBound (withdrawals - txs) + 1) 67 args lookup (by omega) bodyRun bounded.2.1 spent
      (bounded.2.2.1 (by change sszSplitBound (withdrawals - txs) ≤ state.clock - 1; omega))
      (by
        intro value returned
        let resumed := setVarHOLFinite (ofString "txs") value {post with locals := state.locals}
        have wd : resumed.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)) := by
          simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atWithdrawals,
            show ofString "txs" ≠ ofString "o_wd" by decide]
        have bal : resumed.locals.lookup (ofString "o_bal") = some (.val (.word balance)) := by
          simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atBalance,
            show ofString "txs" ≠ ofString "o_bal" by decide]
        exact evaluate_payload_transaction_header_suffix_bounded resumed withdrawals balance wd bal
          (metadata.1.trans code) (by change 67 ≤ post.clock; omega))
    simpa only [Nat.add_assoc, Nat.reduceAdd] using composed

#print axioms evaluate_payload_split_suffix_bounded
end InitECandidate.Runtime
