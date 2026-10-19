import InitECandidate.Runtime.ResolveCompletedNodeBody
import InitECandidate.Runtime.WitnessResolveCallBound
import InitECandidate.Runtime.WitnessResolveTailProgress
import InitECandidate.Runtime.ResolveStepReturnedContract
import InitECandidate.Runtime.DecodeStepScratchCapacity
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString


theorem witness_resolve_call_completed_node_envelope {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength childArray slot heapPointer : BitVec 64)
    (ceiling inputLimit : Nat)
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word childArray)))
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
    (run : evaluateHOLFiniteState s witnessResolveCall = (none,post)) :
    post.locals.lookup (ofString "mode")=some (.val (.word (1#64))) ∨
      ∃ node : BitVec 64, post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
        post.locals.lookup (ofString "result")=some (.val (.word node)) ∧ CompletedNodeEnvelope post node heapPointer.toNat := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "db",.val (.word table))).update
      (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))
  let entry := callEntryStateHOLFinite s callee
  have args := eval_witness_resolve_arguments s table childArray slot pointer length atTable atArray atSlot slice
  have lookup := pan_three_word_shape_lookup s.code.lookup (ofString "_resolve_step")
    (ofString "db") (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn__resolve_step)
    (.comb [.one,.one,.one,.one]) table pointer length (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_resolveStep_lookup)
  have entryBuilt : NodedbTableAt entry table dbHeap total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have entrySlices : RlpSliceInputPrefix entry array input inputLength total.toNat := by
    intro index inside
    obtain ⟨p,n,slice⟩ := slices index inside
    exact ⟨p,n,slice.after_frame s entry array index p n input inputLength rfl rfl rfl⟩
  rw [source_witness_resolve_call] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_normal_exact_scope s post (ofString "r") (ofString "_resolve_step")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn__resolve_step) witnessResolveTail callee args lookup run
  have returned := resolve_step_body_returned_contract entry bodyPost pointer length scratch frame table dbHeap array total input inputLength
    ceiling inputLimit
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    entryBuilt (entries.after_read rfl rfl rfl) entrySlices tableAbove arrayAbove arrayEnd spanLo spanHi spanSize
    (by change resolveStepBodyCost length.toNat ≤ s.clock-1; omega) value bodyRun
  obtain ⟨flag,p,n,hash,same,flags,span⟩ := returned.1
  subst value
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__resolve_step)
  rw [bodyRun] at metadata
  have atR : (setVarHOLFinite (ofString "r")
      (.rStruct [.val (.word flag),.val (.word p),.val (.word n),.val (.word hash)])
      {bodyPost with locals := s.locals}).locals.lookup (ofString "r") =
      some (.rStruct [.val (.word flag),.val (.word p),.val (.word n),.val (.word hash)]) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have globals := witness_resolve_tail_globals_frame
    (setVarHOLFinite (ofString "r") (.rStruct [.val (.word flag),.val (.word p),.val (.word n),.val (.word hash)])
      {bodyPost with locals := s.locals}) (metadata.1.trans code)
  rw [tailRun] at globals
  let ready := setVarHOLFinite (ofString "r")
    (.rStruct [.val (.word flag),.val (.word p),.val (.word n),.val (.word hash)]) {bodyPost with locals := s.locals}
  have otherLocal (name : MlS) (different : name ≠ ofString "r") :
      post.locals.lookup name=output.locals.lookup name := by
    rw [postEq]
    exact restore_other_local _ _ name _ different
  rcases flags with completed | hit
  · subst flag
    have envelope := resolve_step_body_completed_node_envelope entry bodyPost pointer length scratch frame table heapPointer ceiling inputLimit
      (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      atHeap heapBound inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by change resolveStepParseCost length.toNat ≤ s.clock-1; simp only [resolveStepBodyCost,resolveStepParseCost] at budget ⊢; omega)
      _ p n hash rfl bodyRun
    obtain ⟨result,mode,top,_⟩ := witness_resolve_completed_tail_normal_control ready output p n hash atR
      (metadata.1.trans code) tailRun
    refine Or.inr ⟨p,(otherLocal _ (by decide)).trans mode,(otherLocal _ (by decide)).trans result,?_⟩
    apply envelope.after_globals bodyPost post p heapPointer.toNat
    rw [postEq]
    exact globals
  · subst flag
    obtain ⟨atP,atN,mode,top,_⟩ := witness_resolve_hit_tail_normal_control ready output p n hash atR
      (metadata.1.trans code) tailRun
    exact Or.inl ((otherLocal _ (by decide)).trans mode)

#print axioms witness_resolve_call_completed_node_envelope
end InitECandidate.Runtime
