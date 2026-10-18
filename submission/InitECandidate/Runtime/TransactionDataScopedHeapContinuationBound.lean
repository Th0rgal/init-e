import InitECandidate.Runtime.TransactionDataScopedBound
import InitECandidate.Runtime.TransactionDataHeapClockReserve
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_data_scoped_heap_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (headerBefore : tx.toNat + 200 < array.toNat)
    (continuation : ProgHOL 64) (tailCost : Nat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + tailCost ≤ state.clock)
    (tailBound : ∀ middle : PanSemStateFiniteExact 64 F,
      ∀ next : TransactionDecodeWitness middle array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index + 1 → next.heap = valid.heap → tailCost ≤ middle.clock →
      let evaluated := evaluateHOLFiniteState middle continuation
      middle.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ middle.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall (ofString "data") (.comb [.one,.one]) (ofString "tx_bytes_item") transactionDataArguments (.seq transactionDataFinish continuation))
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 + tailCost) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634
  let tail := tailCost
  have ticks : first + tail ≤ state.clock := budget
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
    apply evaluate_decCall_append_bounded state bodyPost (ofString "data") (ofString "tx_bytes_item")
      (.comb [.one,.one]) (.comb [.one,.one]) transactionDataArguments _ _ transactionDataFinish continuation callee result first tail
      args lookup (by omega) bodyRun bounded.2.1
      (by have spent := bounded.1; change state.clock - 1 ≤ bodyPost.clock + _ at spent; dsimp [first]; omega) bounded.2.2 (by rfl)
    intro value returned checked output prefixRun
    have actualBody := bodyRun
    rw [returned] at actualBody
    have fieldRun := evaluate_decCall_checked_normal_intro state bodyPost output (ofString "data") (ofString "tx_bytes_item")
      (.comb [.one,.one]) (.comb [.one,.one]) transactionDataArguments _ _ transactionDataFinish callee value args lookup
      (by omega) actualBody checked prefixRun
    change evaluateHOLFiniteState state transactionDataField = _ at fieldRun
    obtain ⟨next,indexEqual,heapEqual,futureTicks⟩ := transaction_decode_after_data_heap_clock_reserve state _
      array count tx kind input inputLength scratch frame ceiling inputLimit valid inside inputBound limitBound orderedFrame framePositive
      scratchBelow arrayFits arrayAbove headerBefore tail ticks fieldRun
    let active := next.withLocals output.locals
      (by exact (restore_other_local output.locals (ofString "data") (ofString "arr") _ (by decide)).symm)
      (by exact (restore_other_local output.locals (ofString "data") (ofString "tx") _ (by decide)).symm)
      (by exact (restore_other_local output.locals (ofString "data") (ofString "t") _ (by decide)).symm)
      (by exact (restore_other_local output.locals (ofString "data") (ofString "k") _ (by decide)).symm)
    exact tailBound output active indexEqual heapEqual futureTicks

#print axioms transaction_data_scoped_heap_continuation_bounded
end InitECandidate.Runtime
