import InitECandidate.Runtime.TransactionDataSequenceBound
import InitECandidate.Runtime.TransactionWitnessLocals
import InitECandidate.Runtime.PanDecCallCheckedNormalIntro
import InitECandidate.Runtime.PanDecCallAppendBound
import InitECandidate.Runtime.PanSeqAssoc
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionDataScoped : ProgHOL 64 :=
  .decCall (ofString "data") (.comb [.one,.one]) (ofString "tx_bytes_item") transactionDataArguments
    (.seq transactionDataFinish transactionTypedSignature)

theorem evaluate_decCall_continuation_congr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (first second : ProgHOL 64)
    (same : ∀ current : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState current first = evaluateHOLFiniteState current second) :
    evaluateHOLFiniteState state (.decCall name shape function arguments first) =
      evaluateHOLFiniteState state (.decCall name shape function arguments second) := by
  simp only [evaluateHOLFiniteState_decCall_total]
  simp_rw [same]

theorem evaluate_seq_second_congr {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second third : ProgHOL 64)
    (same : ∀ current : PanSemStateFiniteExact 64 F, evaluateHOLFiniteState current second = evaluateHOLFiniteState current third) :
    evaluateHOLFiniteState state (.seq first second) = evaluateHOLFiniteState state (.seq first third) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  simp_rw [same]

theorem evaluate_transaction_data_scope {F : Type} (state : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState state (transactionAt 32) = evaluateHOLFiniteState state transactionDataScoped := by
  rw [source_transaction_data]
  unfold transactionDataScoped
  apply evaluate_decCall_continuation_congr
  intro current
  unfold transactionDataFinish transactionPairFinish
  rw [evaluate_seq_assoc]
  apply evaluate_seq_second_congr
  intro next
  exact (evaluate_seq_assoc next _ _ _).symm

theorem transaction_data_scoped_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 8 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionDataSequenceCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionDataScoped
    state.clock ≤ evaluated.2.clock + transactionDataSequenceCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634
  let tail := transactionTypedSignatureCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have inside : valid.index.toNat < count.toNat := by omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k")] = some [.val (.word array),.val (.word valid.index)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,valid.arrayLocal,valid.indexLocal]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word valid.index))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word valid.index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid.slices slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have firstBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    omega
  have bounded := evaluate_txBytesItem_input_bounded entry array valid.index input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena firstBudget
  have installed : state.code.lookup (ofString "tx_bytes_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_bytes_item,.comb [.one,.one]) := by
    rw [valid.code]; exact originalRuntimeCode_txBytesItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_bytes_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_bytes_item) (.comb [.one,.one]) array valid.index (by decide) installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_bytes_item) with
  | mk result bodyPost =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    unfold transactionDataScoped
    apply evaluate_decCall_append_bounded state bodyPost (ofString "data") (ofString "tx_bytes_item")
      (.comb [.one,.one]) (.comb [.one,.one]) transactionDataArguments _ _ transactionDataFinish transactionTypedSignature callee result first tail
      args lookup (by dsimp [transactionDataSequenceCost] at budget; omega) bodyRun bounded.2.1
      (by have spent := bounded.1; change state.clock - 1 ≤ bodyPost.clock + _ at spent; dsimp [first]; omega) bounded.2.2 (by rfl)
    intro value returned checked output prefixRun
    have actualBody := bodyRun
    rw [returned] at actualBody
    have fieldRun := evaluate_decCall_checked_normal_intro state bodyPost output (ofString "data") (ofString "tx_bytes_item")
      (.comb [.one,.one]) (.comb [.one,.one]) transactionDataArguments _ _ transactionDataFinish callee value args lookup
      (by dsimp [transactionDataSequenceCost] at budget; omega) actualBody checked prefixRun
    change evaluateHOLFiniteState state transactionDataField = _ at fieldRun
    obtain ⟨next,indexEqual,heapEqual,space,futureTicks⟩ := transaction_decode_after_data_reserves state _
      array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive
      scratchBelow arrayBelow (by omega)
      (inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7) tail
      (by omega) ticks fieldRun
    let active := next.withLocals output.locals
      (by exact (restore_other_local output.locals (ofString "data") (ofString "arr") _ (by decide)).symm)
      (by exact (restore_other_local output.locals (ofString "data") (ofString "tx") _ (by decide)).symm)
      (by exact (restore_other_local output.locals (ofString "data") (ofString "t") _ (by decide)).symm)
      (by exact (restore_other_local output.locals (ofString "data") (ofString "k") _ (by decide)).symm)
    have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
      rfl
    have activeFields : active.index.toNat + 7 ≤ count.toNat := by change next.index.toNat + 7 ≤ count.toNat; rw [indexEqual,addOne]; omega
    exact transaction_typed_signature_bounded output array count tx kind input inputLength scratch frame ceiling inputLimit
      active activeFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore (by change next.heap.toNat + _ + _ + _ + 7 ≤ frame.toNat; omega) futureTicks

#print axioms transaction_data_scoped_bounded
end InitECandidate.Runtime
