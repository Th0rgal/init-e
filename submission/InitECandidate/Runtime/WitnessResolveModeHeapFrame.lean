import InitECandidate.Runtime.WitnessResolveModeBound
import InitECandidate.Runtime.WitnessResolveCallHeapFrame
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Whole actual resolve mode preserves the stack and hands control either to
delivery or to decoding of a concrete original-input slice. -/
theorem witness_resolve_mode_normal_heap_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer : BitVec 64)
    (ceiling inputLimit : Nat)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (heapAligned : heapPointer.toNat%8=0)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word childArray)
    (atSlot : s.locals.lookup (ofString "slot") = some (.val (.word slot)))
    (slice : RlpSliceEntry s childArray slot pointer length)
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (built : NodedbTableAt s table dbHeap total)
    (entries : HashTableValuesIn table (NodedbSliceTargets array total) s)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (tableAbove : ceiling ≤ table.toNat) (arrayAbove : ceiling ≤ array.toNat)
    (arrayEnd : array.toNat + total.toNat*16 ≤ dbHeap.toNat)
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (spanSize : length.toNat ≤ inputLength.toNat)
    (budget : resolveStepBodyCost length.toNat + 1 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode = (none,post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      ∃ nextHeap : BitVec 64,
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
        heapPointer.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat%8=0 ∧
        ∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < heapPointer.toNat → watched ≠ top+80 →
          post.memory watched=s.memory watched := by
  rw [source_witness_resolve_mode] at run
  obtain ⟨value,output,initialized,bodyRun,postEq⟩ := evaluate_dec_normal_scope s post
    (ofString "arr") .one _ witnessResolveCall run
  have evalArray : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "top"),.const 24])) = some (.val (.word childArray)) := by
    simp [evalHOLExact,evalListHOLExact,atTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,arrayReadable,arrayCell]
  rw [evalArray] at initialized
  cases initialized
  let entered := setVarHOLFinite (ofString "arr") (.val (.word childArray)) s
  have enteredBuilt : NodedbTableAt entered table dbHeap total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have enteredSlices : RlpSliceInputPrefix entered array input inputLength total.toNat := by
    intro index inside
    obtain ⟨p,n,slice⟩ := slices index inside
    exact ⟨p,n,slice.after_frame s entered array index p n input inputLength rfl rfl rfl⟩
  have enteredSlice := slice.after_frame s entered childArray slot pointer length rfl rfl rfl
  have facts := witness_resolve_call_normal_heap_frame entered output pointer length scratch frame table dbHeap array total input inputLength childArray slot top heapPointer
    ceiling inputLimit
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTop)
    atHeap heapBound heapAligned
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSlot)
    enteredSlice
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTable)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    enteredBuilt (entries.after_read rfl rfl rfl) enteredSlices tableAbove arrayAbove arrayEnd spanLo spanHi spanSize budget bodyRun
  rw [postEq]
  exact facts

#print axioms witness_resolve_mode_normal_heap_frame
end InitECandidate.Runtime
