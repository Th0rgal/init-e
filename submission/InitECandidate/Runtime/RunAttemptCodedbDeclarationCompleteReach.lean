import InitECandidate.Runtime.NodedbDecodedReturnedTableExtent
import InitECandidate.Runtime.RunAttemptCodedbDeclarationReach
import InitECandidate.Runtime.NodedbDecodedReturnedTable
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem run_attempt_codedb_declaration_complete_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si heap total array input inputLength statePad pad output : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 56 64 array total input inputLength heap)
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (aligned : heap.toNat % 8 = 0) (capped : heap.toNat ≤ 33806089496)
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (inputSmall : inputLength.toNat ≤ 134217712) (outputAligned : output.toNat % 8 = 0)
    (windows : total ≠ 0 → statePad.toNat + 200 ≤ array.toNat ∧ pad.toNat + 136 ≤ array.toNat ∧
      output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → heap.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a)
    (budget : nodedbBodyCost total + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 10)
      (fun ready => ready.locals = s.locals.update (ofString "codedb",.val (.word heap)) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧ ready.be = s.be ∧
        ready.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        ready.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        ready.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        (∃ keys stride capacity used values order orderPos count : BitVec 64, ∃ bits : Nat, ∃ finalHeap : BitVec 64,
          count.toNat ≤ total.toNat ∧ capacity.toNat ≤ 536870912 ∧ count.toNat < capacity.toNat ∧
          HtabAligned 32 heap keys stride capacity used values order orderPos count bits ready ∧
          OrderInv ready capacity count used order orderPos ∧
          ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          orderPos.toNat + capacity.toNat * 8 ≤ finalHeap.toNat ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
          (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → ready.memaddrs a)) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w → ¬ MWin pad 136 w →
          ¬ MWin output 32 w → ready.memory w = s.memory w))
      (nodedbBodyCost total + 1) (runAttemptAt 11) := by
  let entry := callEntryStateHOLFinite s (nodedbBuildCallee array total)
  have countBound := linked.countBound
  have inputBound := inputSmall
  have entryCode : entry.code = originalRuntimeCode := code
  have entryHeap : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := atHeap
  have entryArena : ∀ a : BitVec 64, a.toNat % 8 = 0 → heap.toNat ≤ a.toNat →
      a.toNat < 33806089496 → entry.memaddrs a := arena
  have bounded : RunBounded entry (sourceFunctionBody Guest.guestFn_nodedb_build) (nodedbBodyCost total) := by
    by_cases empty : total = 0
    · subst empty
      have large : 45 ≤ nodedbBodyCost (0#64) := by unfold nodedbBodyCost nodedbTailCost; omega
      refine (runBounded_nodedb_empty_body entry heap entryCode ?_ entryHeap aligned capped entryArena ?_).weaken large
      · simp [entry,callEntryStateHOLFinite,nodedbBuildCallee,HolFiniteMapExact.lookup_update,FUPDATE]
      · change 45 ≤ s.clock - 1
        have zero : (0 : BitVec 64).toNat = 0 := rfl
        unfold nodedbBodyCost nodedbTailCost at budget
        rw [zero] at budget
        omega
    · obtain ⟨stateEnd,padEnd,outputEnd⟩ := windows empty
      refine runBounded_nodedb_body entry heap total array statePad pad output entryCode entryHeap aligned capped
        ?_ ?_ atState atPad atOutput (by omega) outputAligned linked.arrayEnd stateEnd padEnd outputEnd
        entryArena ?_ ?_
      · simp [entry,callEntryStateHOLFinite,nodedbBuildCallee,HolFiniteMapExact.lookup_update,FUPDATE]
      · simp (config := {decide := true}) [entry,callEntryStateHOLFinite,nodedbBuildCallee,
          HolFiniteMapExact.lookup_update,FUPDATE]
      · intro j inside
        obtain ⟨src,len,valid⟩ := linked.slices j inside
        exact ⟨src,len,valid.readable.pointerDomain,valid.readable.lengthDomain,valid.readable.pointerCell,
          valid.readable.lengthCell,(valid.length_bound s array j src len input inputLength).trans inputSmall⟩
      · change nodedbBodyCost total ≤ s.clock - 1
        omega
  have lookup : lookupCodeHOLFinite s.code.lookup (ofString "nodedb_build")
      [.val (.word array),.val (.word total)] =
      some (sourceFunctionBody Guest.guestFn_nodedb_build,nodedbBuildCallee array total,.one) := by
    rw [code]
    exact lookup_nodedb_build_callee array total
  rw [source_run_attempt_codedb_call]
  apply bounded_decCall_reaches s (ofString "codedb") (ofString "nodedb_build") .one .one
    runAttemptCodedbArguments [.val (.word array),.val (.word total)]
    (sourceFunctionBody Guest.guestFn_nodedb_build) (runAttemptAt 11) (nodedbBuildCallee array total)
    (nodedbBodyCost total) _ (eval_run_attempt_codedb_arguments s si array total input inputLength heap atSi linked)
    lookup budget bounded
  intro value bodyPost bodyRun checked
  have atTotal : entry.locals.lookup (ofString "n") = some (.val (.word total)) := by
    simp [entry,callEntryStateHOLFinite,nodedbBuildCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have atArray : entry.locals.lookup (ofString "slice_arr") = some (.val (.word array)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,nodedbBuildCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have decoded : RlpSliceInputPrefix entry array input inputLength total.toNat := by
    intro j inside
    obtain ⟨p,l,e⟩ := linked.slices j inside
    exact ⟨p,l,e.after_frame s entry array j p l input inputLength rfl rfl rfl⟩
  obtain ⟨valueEq,keys,stride,capacity,used,values,order,orderPos,count,bits,finalHeap,countBound,capBound,room,inv,ordered,atFinal,extent⟩ :=
    nodedb_decoded_returned_table_extent entry bodyPost value heap total array statePad pad output input inputLength
      entryCode atHeap aligned capped atState atPad atOutput atTotal atArray decoded linked.countBound inputSmall
      outputAligned linked.arrayEnd windows entryArena (by change nodedbBodyCost total ≤ s.clock - 1; omega) bodyRun
  obtain ⟨_,_,_,stateGlobal,padGlobal,outputGlobal,⟨h,atH,mono,al,cap,live⟩,frame⟩ :=
    nodedb_decoded_returned_frame entry bodyPost value heap total array statePad pad output input inputLength
      entryCode atHeap aligned capped atState atPad atOutput atTotal atArray decoded linked.countBound inputSmall
      outputAligned linked.arrayEnd windows entryArena (by change nodedbBodyCost total ≤ s.clock - 1; omega) bodyRun
  have same : h = finalHeap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (atH.symm.trans atFinal)))
  subst h
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_nodedb_build)
  rw [bodyRun] at metadata
  refine ⟨?_,metadata.2.1,metadata.1,metadata.2.2.1,stateGlobal,padGlobal,outputGlobal,
    ⟨keys,stride,capacity,used,values,order,orderPos,count,bits,finalHeap,countBound,capBound,room,?_,?_,
      atFinal,extent,mono,al,cap,live⟩,?_⟩
  · change s.locals.update (ofString "codedb",value) = _
    rw [valueEq]
  · exact inv.transfer rfl rfl rfl rfl
  · exact ordered.transfer rfl rfl rfl
  · exact frame

#print axioms run_attempt_codedb_declaration_complete_reaches
end InitECandidate.Runtime
