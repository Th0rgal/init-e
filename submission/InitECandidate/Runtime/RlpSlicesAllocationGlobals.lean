import InitECandidate.Runtime.AllocationReturnedGuard
import InitECandidate.Runtime.RlpSlicesInitializationGlobals
import InitECandidate.Runtime.RlpSlicesAllocationDomain
import InitECandidate.Runtime.RlpSlicesAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual successful allocator declaration supplies the array base and
writable domains; successful filling returns a fully readable slice array. -/
theorem rlpSlices_allocation_success_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countBound : count.toNat * 16 < 2^64)
    (request : count * 16 ≤ (33806089496 : BitVec 64) - array)
    (arena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 + 2 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesAllocation = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word count)] ∧ RlpSlicePrefix post array count.toNat ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd array (count * 16)))) state).globals := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  obtain ⟨ready,_,clock,_,locals,readyCode,domain,_,_,readyGlobals,decl⟩ := evaluate_alloc_call_and_declaration state argument array
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
    obtain ⟨shape,filled,filledGlobals⟩ := rlpSlices_initialized_return_globals entered output pointer count array atPointer atCount (readyCode.trans code)
      (by change count.toNat * 12 ≤ ready.clock; omega) atArray (by omega) enteredDomain value tail
    refine ⟨shape,?_,?_⟩
    · rw [← same.2]
      intro slot inside
      obtain ⟨p,n,entry⟩ := filled slot inside
      exact ⟨p,n,RlpSliceEntry.after_frame output _ _ _ _ _ entry rfl rfl rfl⟩
    · rw [← same.2]
      exact filledGlobals.trans readyGlobals

theorem rlpSlices_allocation_return_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countBound : count.toNat * 16 < 2^64)
    (arena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 + 2 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesAllocation = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word count)] ∧ RlpSlicePrefix post array count.toNat ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd array (count * 16)))) state).globals := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  have called : evaluateHOLFiniteState state (.decCall (ofString "arr") .one (ofString "alloc") [argument] rlpSlicesInitialized) =
      (some (.returned value),post) := by simpa only [source_rlpSlices_allocation] using run
  have request := alloc_declaration_returned_request state post argument array (count * 16) (ofString "arr") .one
    rlpSlicesInitialized value args code heap called
  exact rlpSlices_allocation_success_globals state post pointer count array pointerLocal countLocal heap arrayBound countBound
    request arena code budget value run

#print axioms rlpSlices_allocation_return_globals

#print axioms rlpSlices_allocation_success_globals
end InitECandidate.Runtime
