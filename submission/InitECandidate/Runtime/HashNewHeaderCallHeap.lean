import InitECandidate.Runtime.HashNewHeaderHeap
import InitECandidate.Runtime.OriginalHashNewCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original constructor call and declaration-call: argument binding,
entry clock and caller-local restoration are included in capacity+8 clocks. -/
theorem evaluate_htabNew_header_call_and_declaration_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument capacityArgument : ExpHOL 64) (table keyLength capacity : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [keyArgument,capacityArgument] =
        some [.val (.word keyLength),.val (.word capacity)])
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 8 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word table)))
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "htab_new") [keyArgument,capacityArgument]) = (none,ready) ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      state.clock ≤ ready.clock + capacity.toNat + 8 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)))) ∧
      ready.memory (table + 0) = .word keyLength ∧
      ready.memory (table + 8) = .word (allocationEnd 0 keyLength) ∧
      ready.memory (table + 16) = .word capacity ∧
      ready.memory (table + 24) = .word 0 ∧
      ready.memory (table + 32) = .word (allocationEnd table 72) ∧
      ready.memory (table + 40) = .word (htabNewValues table keyLength capacity) ∧
      ready.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      ready.memory (table + 56) = .word (htabNewOrder table keyLength capacity) ∧
      ready.memory (table + 64) = .word (htabNewOrderPos table keyLength capacity) ∧
      ∀ name continuation,
        evaluateHOLFiniteState state (.decCall name .one (ofString "htab_new") [keyArgument,capacityArgument] continuation) =
          (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word table)) ready) continuation;
           (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
             (name,state.locals.lookup name))})) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word keyLength))).update (ofString "cap",.val (.word capacity))
  let entry := callEntryStateHOLFinite state callee
  have different : ofString "cap" ≠ ofString "key_len" := by decide
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word keyLength)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,different]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,body,empty,cost,remaining,postCode,addresses,endian,heapAfter,keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField⟩ :=
    evaluate_source_htabNew_header_heap entry table keyLength capacity code (by change capacity.toNat + 7 ≤ state.clock - 1; omega)
      heap keyBound tableAligned budget keyLocal capLocal headerDomain wordDomain byteDomain
  have installed : state.code.lookup (ofString "htab_new") =
      some ([(ofString "key_len",.one),(ofString "cap",.one)],sourceFunctionBody Guest.guestFn_htab_new,.one) := by
    rw [code]; exact originalRuntimeCode_htabNew_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htab_new") (ofString "key_len") (ofString "cap")
    (sourceFunctionBody Guest.guestFn_htab_new) keyLength capacity (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.val (.word table))) .one = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_new")
    [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
    (sourceFunctionBody Guest.guestFn_htab_new) callee .one (.val (.word table)) post arguments lookup (by omega) body shapeOk
  refine ⟨{post with locals := state.locals},call,empty,?_,?_,rfl,postCode,addresses,endian,heapAfter,keyField,strideField,capField,countField,keysField,valuesField,usedField,orderField,reverseField,?_⟩
  · change state.clock ≤ post.clock + capacity.toNat + 8
    change state.clock - 1 ≤ post.clock + capacity.toNat + 7 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "htab_new") .one .one
      [keyArgument,capacityArgument] [.val (.word keyLength),.val (.word capacity)]
      (sourceFunctionBody Guest.guestFn_htab_new) continuation callee (.val (.word table)) arguments lookup
      (by omega) body remaining shapeOk shapeOk

#print axioms evaluate_htabNew_header_call_and_declaration_heap
end InitECandidate.Runtime
