import InitECandidate.Runtime.ResolveStepTailBound
import InitECandidate.Runtime.ResolveStepParseContract
import InitECandidate.Runtime.NodedbContentsAboveFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def resolveStepBodyCost (length : Nat) : Nat := resolveStepParseCost length + (nodedbGetCost + 6)

theorem resolveStepBodyCost_mono (n m : Nat) (inside : n ≤ m) :
    resolveStepBodyCost n ≤ resolveStepBodyCost m := by
  unfold resolveStepBodyCost resolveStepParseCost
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul inside (by omega)) _) _

#print axioms resolveStepBodyCost_mono

theorem runBounded_resolve_step_parse_kind {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength : BitVec 64)
    (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
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
    (budget : resolveStepBodyCost length.toNat ≤ s.clock) :
    RunBounded s (resolveStepAt 2) (resolveStepBodyCost length.toNat) := by
  rw [source_resolve_step_parse_sequence]
  have first := runBounded_resolve_step_parse_call s pointer length scratch frame ceiling inputLimit
    atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena (by unfold resolveStepBodyCost at budget; omega)
  exact RunBounded.seq first budget (by
    intro ready normal readyCode ticks
    obtain ⟨kind,key,payload,consumed,locals,starts,ends,nowrap,payloadBound,globals,memory,codeEq,domain,endian⟩ :=
      resolve_step_parse_call_normal_contract s ready pointer length scratch frame ceiling inputLimit
        atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
        scratchBelow arena (by unfold resolveStepBodyCost at budget; omega) normal
    have contents := nodedb_contents_after_above_frame s ready table dbHeap array total input inputLength ceiling
      built entries slices tableAbove arrayAbove arrayEnd domain endian codeEq memory
    exact runBounded_resolve_step_kind ready table dbHeap total kind key payload consumed contents.1
      (readyCode.trans code)
      (by rw [locals]; simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "db" by decide] using atTable)
      (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]) ticks)

/-- Complete original resolver bound: handled RLP parse, concrete hash-table
lookup, hashed-node fallback and all rejected/inaccessible-memory outcomes. -/
theorem runBounded_resolve_step_body {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame table dbHeap array total input inputLength : BitVec 64)
    (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
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
    (budget : resolveStepBodyCost length.toNat ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn__resolve_step) (resolveStepBodyCost length.toNat) := by
  change RunBounded s (resolveStepAt 0) _
  rw [source_resolve_step_entry]
  apply RunBounded.dec
  intro value initialized
  have valueEq : value = .rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))] := by
    simpa [evalHOLExact,evalListHOLExact] using initialized.symm
  subst value
  apply RunBounded.decConst
  let entered := setVarHOLFinite (ofString "e") (.val (.word (0#64)))
    (setVarHOLFinite (ofString "it")
      (.rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))]) s)
  have entryBuilt : NodedbTableAt entered table dbHeap total := by
    obtain ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv,ordered,extent⟩ := built
    exact ⟨k,sd,c,u,v,o,op,n,b,nb,cb,room,inv.transfer rfl rfl rfl rfl,ordered.transfer rfl rfl rfl,extent⟩
  have entrySlices : RlpSliceInputPrefix entered array input inputLength total.toNat := by
    intro index inside
    obtain ⟨p,n,slice⟩ := slices index inside
    exact ⟨p,n,slice.after_frame s entered array index p n input inputLength rfl rfl rfl⟩
  apply runBounded_resolve_step_parse_kind entered pointer length scratch frame table dbHeap array total input inputLength
    ceiling inputLimit
  · simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPointer
  · simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
  · simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTable
  · exact inputRange
  · exact lengthBound
  · exact limitBound
  · exact scratchGlobal
  · exact frameGlobal
  · exact code
  · exact orderedFrame
  · exact framePositive
  · exact scratchBelow
  · exact arena
  · exact entryBuilt
  · exact entries.after_read rfl rfl rfl
  · exact entrySlices
  · exact tableAbove
  · exact arrayAbove
  · exact arrayEnd
  · exact budget

#print axioms runBounded_resolve_step_parse_kind
#print axioms runBounded_resolve_step_body
end InitECandidate.Runtime
