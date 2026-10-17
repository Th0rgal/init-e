import InitECandidate.Runtime.HashGetValueProperty
import InitECandidate.Runtime.OriginalHashGetCode
import InitECandidate.Runtime.PanTwoWordResultLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual get-table calls and declarations transmit a predicate on occupied
values to present results, preserving memory, globals, and caller locals. -/
theorem HashTableArraysInvariant.get_value_property {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key : BitVec 64) (bits : Nat)
    (property : BitVec 64 → Prop) (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (arrays : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (entries : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → hashOccupancyRead state used slot ≠ some 0 →
      ∀ value : BitVec 64, state.memory (values + slot * 8) = .word value → property value)
    (ticks : 2 * capacity.toNat + 3 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ ready, (present = 0 ∨ present = 1) ∧
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_get") [tableArgument,keyArgument]) = (none,ready) ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 3 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.memory = state.memory ∧ ready.globals = state.globals ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ (present ≠ 0 → property value) ∧
      (∀ name continuation, evaluateHOLFiniteState state
        (.decCall name (.comb [.one,.one]) (ofString "htab_get") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.rStruct [.val (.word present),.val (.word value)]) ready) continuation;
          (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  have tableLocal : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "key" ≠ ofString "t" from by decide]
  have keyLocal : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryArrays := arrays.after_read state entry keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  obtain ⟨present,value,post,boolean,body,cost,remaining,memory,globals,postCode,domain,endian,valueProperty⟩ :=
    evaluate_source_hashGet_supported_value_property entry keyLength table keys stride capacity used values order orderPos count key bits
      property supported entryArrays tableLocal keyLocal keyAligned keyWords keyBytes entries (by change 2 * capacity.toNat + 2 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "htab_get") =
      some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_htab_get,.comb [.one,.one]) := by
    rw [arrays.code]; exact originalRuntimeCode_hashGet_lookup
  have lookup := pan_two_word_result_lookup state.code.lookup (ofString "htab_get") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_htab_get) table key (.comb [.one,.one]) (by decide) installed
  have shapeOk : shapeEqHOL (shapeOfHOLExact (.rStruct [.val (.word present),.val (.word value)])) (.comb [.one,.one]) = true := by
    simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "htab_get")
    [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_get) callee (.comb [.one,.one])
    (.rStruct [.val (.word present),.val (.word value)]) post arguments lookup (by omega) body shapeOk
  refine ⟨present,value,{post with locals := state.locals},boolean,call,?_,?_,rfl,memory,globals,postCode,domain,endian,valueProperty,?_⟩
  · change state.clock ≤ post.clock + 2 * capacity.toNat + 3
    change state.clock - 1 ≤ post.clock + 2 * capacity.toNat + 2 at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega
  · intro name continuation
    exact evaluate_decCall_return_caller_locals state post name (ofString "htab_get") (.comb [.one,.one]) (.comb [.one,.one])
      [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_htab_get) continuation callee
      (.rStruct [.val (.word present),.val (.word value)]) arguments lookup (by omega) body remaining shapeOk shapeOk

#print axioms HashTableArraysInvariant.get_value_property
end InitECandidate.Runtime
