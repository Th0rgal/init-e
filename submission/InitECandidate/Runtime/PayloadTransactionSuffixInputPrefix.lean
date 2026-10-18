import InitECandidate.Runtime.PayloadArrayCellSeparation
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned payload suffix preserves its transaction slices and allocator
globals. The array may be empty; otherwise it lies above the payload header. -/
theorem payload_transaction_suffix_input_prefix {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (payload array count withdrawals balance input inputLength : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atList : state.locals.lookup (ofString "txs") = some (.rStruct [.val (.word array),.val (.word count)]))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (arrayDomain : state.memaddrs (payload + 32)) (countDomain : state.memaddrs (payload + 40))
    (arrayAbove : count = 0 ∨ payload.toNat + 136 ≤ array.toNat)
    (arrayBound : array.toNat + count.toNat * 16 ≤ 33806089496)
    (inputPrefix : RlpSliceInputPrefix state array input inputLength count.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 17) = (some (.returned value),post)) :
    RlpSliceInputPrefix post array input inputLength count.toNat ∧ post.globals = state.globals := by
  have small : ∀ offset : BitVec 64,
      offset ∈ ([32,40,48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) → offset.toNat ≤ 128 := by
    intro offset member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  have headerSeparated : ∀ offset : BitVec 64,
      offset ∈ ([32,40,48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) → payload ≠ payload + offset := by
    intro offset member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  have globalFrame := (payload_transaction_suffix_memory_frame state post payload array count withdrawals balance payload value
    atPayload atList atWithdrawals atBalance arrayDomain countDomain headerSeparated code run).2
  refine ⟨?_,globalFrame⟩
  by_cases empty : count = 0
  · subst count
    exact rlpSliceInputPrefix_empty post array input inputLength
  · have above : payload.toNat + 136 ≤ array.toNat := arrayAbove.resolve_left empty
    have metadata := evaluateHOLFiniteState_metadata state (payloadAt 17)
    rw [run] at metadata
    intro index inside
    obtain ⟨pointer,length,item⟩ := inputPrefix index inside
    have pointerFrame := (payload_transaction_suffix_memory_frame state post payload array count withdrawals balance
      (array + index * 16) value atPayload atList atWithdrawals atBalance arrayDomain countDomain
      (by
        intro offset member
        have separated := payload_array_cell_separate payload array count index 0 offset above arrayBound inside (by decide) (small offset member)
        change array + index * 16 + (0#64) ≠ payload + offset at separated
        rw [BitVec.add_zero] at separated
        exact separated)
      code run).1
    have lengthFrame := (payload_transaction_suffix_memory_frame state post payload array count withdrawals balance
      (array + index * 16 + 8) value atPayload atList atWithdrawals atBalance arrayDomain countDomain
      (fun offset member => payload_array_cell_separate payload array count index 8 offset above arrayBound inside
        (by decide) (small offset member)) code run).1
    exact ⟨pointer,length,item.after_frame state post array index pointer length input inputLength
      metadata.2.1 pointerFrame lengthFrame⟩

#print axioms payload_transaction_suffix_input_prefix
end InitECandidate.Runtime
