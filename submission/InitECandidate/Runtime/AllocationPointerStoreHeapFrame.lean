import InitECandidate.Runtime.HeapGlobalsFrame
import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original array-allocation declaration followed by its header pointer
store. The continuation sees the new pointer, while its exit restores the
caller's previous binding of the allocation local. -/
theorem evaluate_allocation_pointer_store_heap_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name tableName : MlS) (argument : ExpHOL 64) (pointer size table offset : BitVec 64)
    (continuation : ProgHOL 64) (different : name ≠ tableName)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (request : size ≤ (33806089496 : BitVec 64) - pointer)
    (finishBound : (allocationEnd pointer size).toNat ≤ 33806089496)
    (tableLocal : state.locals.lookup tableName = some (.val (.word table)))
    (domain : state.memaddrs (table + offset)) :
    ∃ ready, evaluateHOLFiniteState state
        (.decCall name .one (ofString "alloc") [argument]
          (.seq (.store (hashLocalAddress tableName offset) (.var .local name)) continuation)) =
        (let output := evaluateHOLFiniteState ready continuation;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
            (name,state.locals.lookup name))})) ∧
      ready.clock = state.clock - 1 ∧
      ready.locals = (setVarHOLFinite name (.val (.word pointer)) state).locals ∧
      ready.memory = (sourceWriteWord state (table + offset) pointer).memory ∧
      ready.memory (table + offset) = .word pointer ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer size))) ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ HeapGlobalsFrame state ready := by
  obtain ⟨allocated,_,ticks,memory,locals,postCode,addresses,_,endian,globals,decl⟩ :=
    evaluate_alloc_call_and_declaration state argument pointer size arguments code clock heapGlobal request finishBound
  let entered := setVarHOLFinite name (.val (.word pointer)) allocated
  have t : entered.locals.lookup tableName = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using tableLocal
  have p : entered.locals.lookup name = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have store := evaluate_store_word entered (table + offset) pointer _ (.var .local name)
    (eval_hashLocalAddress entered tableName table offset t) p
    (by change allocated.memaddrs (table + offset); rw [addresses]; exact domain)
  let ready := sourceWriteWord entered (table + offset) pointer
  refine ⟨ready,?_,ticks,?_,?_,?_,?_,postCode,addresses,endian,?_⟩
  · rw [decl]
    change (let output := evaluateHOLFiniteState entered (.seq (.store (hashLocalAddress tableName offset) (.var .local name)) continuation); _) = _
    rw [evaluateHOLFiniteState_seq_line780,store]
  · change (setVarHOLFinite name (.val (.word pointer)) allocated).locals = _
    simp only [setVarHOLFinite,locals]
  · change (sourceWriteWord entered (table + offset) pointer).memory = _
    simp only [sourceWriteWord,entered,setVarHOLFinite,memory]
  · simp [ready,sourceWriteWord]
  · change allocated.globals.lookup (ofString "heap_ptr") = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro watched notHeap
    change allocated.globals.lookup watched = state.globals.lookup watched
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap]

#print axioms evaluate_allocation_pointer_store_heap_frame
end InitECandidate.Runtime
