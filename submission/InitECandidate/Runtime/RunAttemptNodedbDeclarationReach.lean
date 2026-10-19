import InitECandidate.Runtime.RunAttemptNodedbCallBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.NodedbInputCost
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
/-- The actual first database declaration reaches its real continuation with
execution-derived callee evidence, or aborts within the proved body budget. -/
theorem run_attempt_nodedb_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si heap total array input inputLength statePad pad output : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 40 48 array total input inputLength heap)
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
    Reaches s (runAttemptAt 9)
      (fun ready => ∃ value : ValueHOL 64, ∃ bodyPost : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (nodedbBuildCallee array total))
          (sourceFunctionBody Guest.guestFn_nodedb_build) = (some (.returned value),bodyPost) ∧
        ready.locals = s.locals.update (ofString "nodedb",value) ∧
        ready.memory = bodyPost.memory ∧ ready.globals = bodyPost.globals ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code)
      (nodedbBodyCost total + 1) (runAttemptAt 10) := by
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
  rw [source_run_attempt_nodedb_call]
  apply bounded_decCall_reaches s (ofString "nodedb") (ofString "nodedb_build") .one .one
    runAttemptNodedbArguments [.val (.word array),.val (.word total)]
    (sourceFunctionBody Guest.guestFn_nodedb_build) (runAttemptAt 10) (nodedbBuildCallee array total)
    (nodedbBodyCost total) _ (eval_run_attempt_nodedb_arguments s si array total input inputLength heap atSi linked)
    lookup budget bounded
  intro value bodyPost bodyRun checked
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_nodedb_build)
  rw [bodyRun] at metadata
  exact ⟨value,bodyPost,bodyRun,rfl,rfl,rfl,metadata.2.1,metadata.1⟩

#print axioms run_attempt_nodedb_declaration_reaches
theorem run_attempt_nodedb_declaration_input_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si heap total array input inputLength statePad pad output : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 40 48 array total input inputLength heap)
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
    (inputLimit : Nat) (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (budget : nodedbInputCallCost inputLimit ≤ s.clock) :
    Reaches s (runAttemptAt 9)
      (fun ready => ∃ value : ValueHOL 64, ∃ bodyPost : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (nodedbBuildCallee array total))
          (sourceFunctionBody Guest.guestFn_nodedb_build) = (some (.returned value),bodyPost) ∧
        ready.locals = s.locals.update (ofString "nodedb",value) ∧
        ready.memory = bodyPost.memory ∧ ready.globals = bodyPost.globals ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code)
      (nodedbInputCallCost inputLimit) (runAttemptAt 10) := by
  have cost := nodedb_call_cost_le_input total inputLength inputLimit linked.countBound inputBound inputCap
  have reached := run_attempt_nodedb_declaration_reaches s si heap total array input inputLength statePad pad output
    atSi linked code atHeap aligned capped atState atPad atOutput inputSmall outputAligned windows arena
    (cost.trans budget)
  exact reaches_mono s (runAttemptAt 9) (runAttemptAt 10) _ _ _ _ cost (fun _ facts => facts) reached

#print axioms run_attempt_nodedb_declaration_input_reaches
end InitECandidate.Runtime
