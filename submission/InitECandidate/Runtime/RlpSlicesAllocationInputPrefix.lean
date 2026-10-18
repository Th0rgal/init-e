import InitECandidate.Runtime.AllocationReturnedGuard
import InitECandidate.Runtime.RlpSlicesInitializationInputPrefix
import InitECandidate.Runtime.RlpSlicesAllocationDomain
import InitECandidate.Runtime.RlpSlicesAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual successful allocator declaration supplies the array base and
writable domains; successful filling returns a fully readable slice array. -/
theorem rlpSlices_allocation_success_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (checked checkedFinal : PanSemStateFiniteExact 64 F)
    (vc : RlpListCountLoopWitness checked pointer length scratch frame ceiling)
    (offsetZero : vc.offset = 0) (countZero : vc.count = 0)
    (finalCount : checkedFinal.locals.lookup (ofString "count") = some (.val (.word count)))
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedFinal))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (checkedBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ checked.clock)
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 byteOffset))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countBound : count.toNat * 16 < 2^64)
    (request : count * 16 ≤ (33806089496 : BitVec 64) - array)
    (arena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 + 2 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesAllocation = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word count)] ∧ RlpSliceInputPrefix post array pointer length count.toNat := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,_,clock,memory,locals,readyCode,domain,_,endian,_,decl⟩ := evaluate_alloc_call_and_declaration state argument array
    (count * 16) args code (by omega) heap request (allocationEnd_within_heap array (count * 16) arrayBound request)
  let entered := setVarHOLFinite (ofString "arr") (.val (.word array)) ready
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "arr" ≠ ofString "p" by decide] using pointerLocal
  have atCount : entered.locals.lookup (ofString "count") = some (.val (.word count)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "arr" ≠ ofString "count" by decide] using countLocal
  have atArray : entered.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have interval := rlpSlices_allocation_interval array count arrayBound countBound request
  have arrayDomain := rlpSlices_allocation_domains state array count interval arena
  have enteredDomain : ∀ slot : BitVec 64, slot.toNat < count.toNat →
      entered.memaddrs (array + slot * 16#64) ∧ entered.memaddrs (array + slot * 16#64 + 8#64) := by
    intro slot inside
    change ready.memaddrs _ ∧ ready.memaddrs _
    rw [domain]
    exact arrayDomain slot inside
  rw [source_rlpSlices_allocation] at run
  change evaluateHOLFiniteState state (.decCall (ofString "arr") .one (ofString "alloc") [argument] rlpSlicesInitialized) = _ at run
  rw [decl] at run
  cases tail : evaluateHOLFiniteState entered rlpSlicesInitialized with
  | mk result output =>
    rw [tail] at run
    dsimp only at run
    have same := Prod.mk.inj run
    have returned : result = some (.returned value) := same.1
    subst result
    obtain ⟨shape,filled⟩ := rlpSlices_initialized_return_input_prefix entered output pointer count array length scratch frame ceiling inputLimit
      checked checkedFinal vc offsetZero countZero finalCount checkedRun noWrap lengthBound limitBound orderedFrame
      framePositive scratchBelow inputBeforeFrame inputBeforeArray checkedBudget
      (by
        intro byteOffset inside
        have kept := input_bytes_of_memory_below state entered pointer length frame inputBeforeFrame
          (by intro address below; change ready.memory address = state.memory address; rw [memory]) domain endian byteOffset inside
        exact (reads byteOffset inside).trans kept.symm) atPointer atCount (readyCode.trans code)
      (by change count.toNat * 12 ≤ ready.clock; omega) atArray (by omega) enteredDomain value tail
    refine ⟨shape,?_⟩
    rw [← same.2]
    intro slot inside
    obtain ⟨p,n,entry⟩ := filled slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame output _ _ _ _ _ _ _ entry rfl rfl rfl⟩

theorem rlpSlices_allocation_return_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (checked checkedFinal : PanSemStateFiniteExact 64 F)
    (vc : RlpListCountLoopWitness checked pointer length scratch frame ceiling)
    (offsetZero : vc.offset = 0) (countZero : vc.count = 0)
    (finalCount : checkedFinal.locals.lookup (ofString "count") = some (.val (.word count)))
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedFinal))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (checkedBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ checked.clock)
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ state.memory state.memaddrs (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 byteOffset))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countBound : count.toNat * 16 < 2^64)
    (arena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 + 2 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesAllocation = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word count)] ∧ RlpSliceInputPrefix post array pointer length count.toNat := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  have called : evaluateHOLFiniteState state (.decCall (ofString "arr") .one (ofString "alloc") [argument] rlpSlicesInitialized) =
      (some (.returned value),post) := by simpa only [source_rlpSlices_allocation] using run
  have request := alloc_declaration_returned_request state post argument array (count * 16) (ofString "arr") .one
    rlpSlicesInitialized value args code heap called
  exact rlpSlices_allocation_success_input_prefix state post pointer count array length scratch frame ceiling inputLimit
    checked checkedFinal vc offsetZero countZero finalCount checkedRun noWrap lengthBound limitBound orderedFrame
    framePositive scratchBelow inputBeforeFrame inputBeforeArray checkedBudget reads pointerLocal countLocal heap arrayBound countBound
    request arena code budget value run

#print axioms rlpSlices_allocation_return_input_prefix

#print axioms rlpSlices_allocation_success_input_prefix
end InitECandidate.Runtime
