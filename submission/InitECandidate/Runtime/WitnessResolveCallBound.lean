import InitECandidate.Runtime.WitnessResolveArguments
import InitECandidate.Runtime.ResolveStepUniformBodyBound
import InitECandidate.Runtime.OriginalResolveStepCode
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_witness_resolve_call {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength childArray slot : BitVec 64)
    (ceiling inputLimit : Nat)
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
    (budget : resolveStepBodyCost length.toNat + 1 ≤ s.clock) :
    RunBounded s witnessResolveCall (resolveStepBodyCost length.toNat + 1) := by
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
  have bounded := runBounded_resolve_step_body entry pointer length scratch frame table dbHeap array total input inputLength
    ceiling inputLimit
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    entryBuilt (entries.after_read rfl rfl rfl) entrySlices tableAbove arrayAbove arrayEnd
    (by change resolveStepBodyCost length.toNat ≤ s.clock-1; omega)
  have reached : Reaches s witnessResolveCall (fun ready => ready.code = originalRuntimeCode)
      (resolveStepBodyCost length.toNat + 1) witnessResolveTail := by
    rw [source_witness_resolve_call]
    apply bounded_decCall_reaches s (ofString "r") (ofString "_resolve_step")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one])
      _ _ _ _ callee (resolveStepBodyCost length.toNat) _ args lookup (by omega) bounded
    intro value post run shapes
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn__resolve_step)
    rw [run] at metadata
    exact metadata.1.trans code
  have closed := RunBounded.ofReaches (tailCost := 0) (by simpa using budget) reached
    (fun ready installed ticks => RunBounded.ofProg witness_resolve_tail_bounded installed ticks)
  simpa using closed

#print axioms runBounded_witness_resolve_call
end InitECandidate.Runtime
