import InitECandidate.Runtime.RlpCountFillLoopReturnInputPrefix
import InitECandidate.Runtime.RlpSlicesInitializationBound
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_initialized_return_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (checked checkedFinal : PanSemStateFiniteExact 64 F)
    (vc : RlpListCountLoopWitness checked pointer length scratch frame ceiling)
    (offsetZero : vc.offset = 0) (countZero : vc.count = 0)
    (finalCount : checkedFinal.locals.lookup (ofString "count") = some (.val (.word count)))
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedFinal))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (checkedBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ checked.clock)
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 byteOffset))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 ≤ state.clock)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (domain : ∀ slot : BitVec 64, slot.toNat < count.toNat →
      state.memaddrs (array + slot * 16#64) ∧ state.memaddrs (array + slot * 16#64 + 8#64))
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesInitialized = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word count)] ∧ RlpSliceInputPrefix post array pointer length count.toNat := by
  let initial := setVarHOLFinite (ofString "off") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
  have atPointer : initial.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "p" by decide,show ofString "i" ≠ ofString "p" by decide] using pointerLocal
  have atCount : initial.locals.lookup (ofString "count") = some (.val (.word count)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "count" by decide,show ofString "i" ≠ ofString "count" by decide] using countLocal
  have atOffset : initial.locals.lookup (ofString "off") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : initial.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  let valid : RlpSlicesLoopWitness initial pointer count :=
    ⟨0,0,atPointer,atCount,atOffset,atIndex,by simp,code⟩
  have atArray : initial.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide] using arrayLocal
  let memoryValid : RlpSlicesMemoryWitness initial pointer count array :=
    ⟨valid,atArray,fits,domain,rlpSlicePrefix_empty initial array⟩
  rw [source_rlpSlices_initialized] at run
  obtain ⟨middle,bodyRun,restoredI⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0) 0
    (.dec (ofString "off") .one (.const 0) rlpSlicesLoopAndReturn) (some (.returned value)) (by rfl) run
  obtain ⟨output,tailRun,restoredOff⟩ := evaluate_dec_word_result_scope
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) middle
    (ofString "off") (.const 0) 0 rlpSlicesLoopAndReturn (some (.returned value)) (by rfl) bodyRun
  obtain ⟨shape,filled⟩ := rlpCountFill_loop_return_input_prefix pointer length scratch frame array count ceiling inputLimit
    noWrap lengthBound limitBound orderedFrame framePositive scratchBelow inputBeforeFrame inputBeforeArray
    checkedFinal finalCount checked initial output vc memoryValid
    (by change (0 : BitVec 64) = vc.offset; exact offsetZero.symm)
    (by change (0 : BitVec 64) = vc.count; exact countZero.symm)
    (rlpSliceInputPrefix_empty initial array pointer length) reads
    (by simpa [offsetZero] using checkedBudget)
    (by change (count.toNat - 0) * 12 ≤ state.clock; simpa only [Nat.sub_zero] using budget)
    checkedRun value tailRun
  refine ⟨shape,?_⟩
  rw [restoredI,restoredOff]
  intro slot inside
  obtain ⟨p,n,entry⟩ := filled slot inside
  exact ⟨p,n,RlpSliceInputEntry.after_frame output _ _ _ _ _ _ _ entry rfl rfl rfl⟩

#print axioms rlpSlices_initialized_return_input_prefix
end InitECandidate.Runtime
