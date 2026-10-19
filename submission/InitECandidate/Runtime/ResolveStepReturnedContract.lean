import InitECandidate.Runtime.ResolveStepUniformBodyBound
import InitECandidate.Runtime.ResolveStepReturnedKinds
import InitECandidate.Runtime.ResolveStepWorkspaceFrame
import InitECandidate.Runtime.PanLocalCallHandlerNoReturn
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem resolve_step_parse_call_no_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : s.code = originalRuntimeCode) (value : ValueHOL 64) :
    (evaluateHOLFiniteState s resolveStepParseCall).1 ≠ some (.returned value) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "p"),.var .local (ofString "n")] =
      some [.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_item")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item)
    (.comb [.one,.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpItem_lookup)
  intro equal
  have returned : evaluateHOLFiniteState s resolveStepParseCall =
      (some (.returned value),(evaluateHOLFiniteState s resolveStepParseCall).2) := Prod.ext equal rfl
  rw [source_resolve_step_parse_call] at returned
  exact evaluate_localCall_handler_no_return s _ (ofString "it") (ofString "rlp_item")
    (.comb [.one,.one,.one,.one]) _ _ (sourceFunctionBody Guest.guestFn_rlp_item)
    (.call (some (none,none)) (ofString "mpt_fail") [.const 3]) (ofString "RlpErr") (ofString "e")
    (rlpHeaderCallee pointer length) args lookup value
    (fun current => evaluate_noDirectReturn _ rfl current value) returned

theorem resolve_step_parse_kind_returned_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
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
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (spanSize : length.toNat ≤ inputLength.toNat)
    (budget : resolveStepBodyCost length.toNat ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (resolveStepAt 2) = (some (.returned value),post)) :

    ResolveStepResultSpan input inputLength value ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rw [source_resolve_step_parse_sequence] at run
  obtain ⟨ready,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (resolve_step_parse_call_no_return s pointer length atPointer atLength code) run
  obtain ⟨kind,key,payload,consumed,locals,starts,ends,nowrap,payloadBound,globals,memory,codeEq,domain,endian⟩ :=
    resolve_step_parse_call_normal_contract s ready pointer length scratch frame ceiling inputLimit
      atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena (by unfold resolveStepBodyCost at budget; omega) normal
  have contents := nodedb_contents_after_above_frame s ready table dbHeap array total input inputLength ceiling
    built entries slices tableAbove arrayAbove arrayEnd domain endian codeEq memory
  have result := resolve_step_kind_returned_result ready post pointer length table dbHeap total array
    kind key payload consumed input inputLength contents.1 contents.2.1 contents.2.2
    (by rw [locals]; simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "p" by decide] using atPointer)
    (by rw [locals]; simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "n" by decide] using atLength)
    (by rw [locals]; simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "it" ≠ ofString "db" by decide] using atTable)
    (by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE])
    spanLo spanHi inputRange spanSize (codeEq.trans code) value tailRun
  have scratchKept := resolve_step_tail_workspace_frame ready (codeEq.trans code) (ofString "scratch_ptr")
    (by simp [resolveStepWorkspace])
  have frameKept := resolve_step_tail_workspace_frame ready (codeEq.trans code) (ofString "frame_mem_ptr")
    (by simp [resolveStepWorkspace])
  rw [tailRun] at scratchKept frameKept
  exact ⟨result,scratchKept.trans ((globals _).trans scratchGlobal),frameKept.trans ((globals _).trans frameGlobal)⟩

/-- Complete actual resolver contract. Flag 1 always carries a nonwrapping
slice of the original input, including hash-database jumps; flags are 0 or 1.
Returned parser workspace is restored. No heap-allocation success is assumed. -/
theorem resolve_step_body_returned_contract {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
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
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (spanSize : length.toNat ≤ inputLength.toNat)
    (budget : resolveStepBodyCost length.toNat ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__resolve_step) = (some (.returned value),post)) :

    ResolveStepResultSpan input inputLength value ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  change evaluateHOLFiniteState s (resolveStepAt 0) = _ at run
  rw [source_resolve_step_entry] at run
  obtain ⟨it,first,initialized,firstRun,postEq⟩ := evaluate_dec_returned_scope s post (ofString "it") _ _ _ value run
  have itEq : it = .rStruct [.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64)),.val (.word (0#64))] := by
    simpa [evalHOLExact,evalListHOLExact] using initialized.symm
  subst it
  obtain ⟨error,output,initialized,childRun,firstEq⟩ := evaluate_dec_returned_scope _ first
    (ofString "e") .one (.const 0) (resolveStepAt 2) value firstRun
  have errorEq : error = .val (.word (0#64)) := by simpa [evalHOLExact] using initialized.symm
  subst error
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
  have facts := resolve_step_parse_kind_returned_contract entered output pointer length scratch frame table dbHeap
    array total input inputLength ceiling inputLimit
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPointer)
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength)
    (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTable)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    entryBuilt (entries.after_read rfl rfl rfl) entrySlices tableAbove arrayAbove arrayEnd spanLo spanHi spanSize budget value childRun
  rw [postEq,firstEq]
  exact facts

#print axioms resolve_step_parse_call_no_return
#print axioms resolve_step_parse_kind_returned_contract
#print axioms resolve_step_body_returned_contract
end InitECandidate.Runtime
