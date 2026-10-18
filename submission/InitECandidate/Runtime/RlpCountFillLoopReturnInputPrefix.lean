import InitECandidate.Runtime.RlpCountFillLoopInputPrefix
import InitECandidate.Runtime.RlpSlicesReturnMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpCountFill_loop_return_input_prefix {F : Type}
    (pointer length scratch frame array sliceCount : BitVec 64) (ceiling inputLimit : Nat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (checkedFinal : PanSemStateFiniteExact 64 F)
    (finalCount : checkedFinal.locals.lookup (ofString "count") = some (.val (.word sliceCount)))
    (checked unchecked post : PanSemStateFiniteExact 64 F)
    (vc : RlpListCountLoopWitness checked pointer length scratch frame ceiling)
    (vu : RlpSlicesMemoryWitness unchecked pointer sliceCount array)
    (offsetMatch : vu.control.offset = vc.offset) (countMatch : vu.control.index = vc.count)
    (filled : RlpSliceInputPrefix unchecked array pointer length vu.control.index.toNat)
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs (fun a => Classical.propDecidable (unchecked.memaddrs a)) unchecked.be (pointer + BitVec.ofNat 64 byteOffset))
    (checkedBudget : (length.toNat - vc.offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ≤ checked.clock)
    (uncheckedBudget : (sliceCount.toNat - vu.control.index.toNat) * 12 ≤ unchecked.clock)
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedFinal))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState unchecked rlpSlicesLoopAndReturn = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word sliceCount)] ∧
    RlpSliceInputPrefix post array pointer length sliceCount.toNat := by
  obtain ⟨result,loopPost,loopRun,_,_,_,done,noReturn⟩ := evaluate_rlpSlices_loop_memory_bounded unchecked pointer sliceCount array vu uncheckedBudget
  rw [source_rlpSlices_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    obtain ⟨next,_,_⟩ := done rfl
    have filledInput := rlpCountFill_loop_input_prefix pointer length scratch frame array sliceCount ceiling inputLimit
      noWrap lengthBound limitBound orderedFrame framePositive scratchBelow inputBeforeFrame inputBeforeArray
      checkedFinal loopPost finalCount checked unchecked vc vu offsetMatch countMatch filled reads checkedBudget uncheckedBudget checkedRun loopRun
    have returned : evaluateHOLFiniteState loopPost
        (.return (.rstruct [.var .local (ofString "arr"),.var .local (ofString "count")])) =
        (some (.returned (.rStruct [.val (.word array),.val (.word sliceCount)])),emptyLocalsHOLFinite loopPost) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,next.arrayLocal,next.control.countLocal,
        shapeOfHOLExact,sizeOfShapeWithContextHOL]
    have equal := Prod.mk.inj (run.symm.trans returned)
    refine ⟨PanSemResultExact.returned.inj (Option.some.inj equal.1),?_⟩
    rw [equal.2]
    intro slot inside
    obtain ⟨p,n,entry⟩ := filledInput slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame loopPost _ _ _ _ _ _ _ entry rfl rfl rfl⟩

#print axioms rlpCountFill_loop_return_input_prefix
end InitECandidate.Runtime
