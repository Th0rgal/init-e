import InitECandidate.Runtime.RunAttemptNodedbArguments
import InitECandidate.Runtime.NodedbDecodedCallBound
/-!
The actual `nodedb_build` call of `run_attempt`, bounded from the linked record.

`RunAttemptNodedbArguments` shows that `runAttemptAt 9` is the real
`nodedb_build` call whose two arguments are the typed pointer and count cells of
the state-database record at `si + 40` and `si + 48`.  This module feeds the
existing checked builder bounds with exactly that argument evaluation, so the
installed builder is bounded in every outcome from the decoded witness geometry
the caller already supplies:

* `runBounded_run_attempt_nodedb_call` bounds the real call program for any
  destination and continuation cost;
* `runBounded_run_attempt_nodedb_at9` bounds the actual `runAttemptAt 9`
  declaration itself, for an arbitrary continuation cost supplied by a
  `RunBounded` hypothesis on the continuation after every returned callee run.

No callee runtime bound is assumed: both reuse `runBounded_nodedb_body` (and
`runBounded_nodedb_empty_body` for a zero-entry list), whose hypotheses are the
decoded slice geometry, the aligned heap frontier arena and the global
workspace words.  The only facts taken from the record are its decoded slice
table, count bound and array end.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

/-- The real `nodedb_build` call of `run_attempt`, bounded in every outcome for
any destination, from the linked state-database record and the decoded witness
geometry. -/
theorem runBounded_run_attempt_nodedb_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si heap total array input inputLength statePad pad output : BitVec 64)
    (destination : Option (VarKind × MlS))
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
    RunBounded s (.call (some (destination,none)) (ofString "nodedb_build") runAttemptNodedbArguments)
      (nodedbBodyCost total + 1) :=
  runBounded_nodedb_decoded_call s heap total array input inputLength statePad pad output destination
    runAttemptNodedbArguments
    (eval_run_attempt_nodedb_arguments s si array total input inputLength heap atSi linked) code
    atHeap aligned capped atState atPad atOutput linked.slices linked.countBound inputSmall
    outputAligned linked.arrayEnd windows arena budget

/-- The actual `runAttemptAt 9` declaration is bounded in every outcome with an
arbitrary continuation cost, given a bound for the continuation after every
returned callee run. -/
theorem runBounded_run_attempt_nodedb_at9 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si heap total array input inputLength statePad pad output : BitVec 64)
    (tailCost : Nat)
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
    (tailBounded : ∀ value post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (nodedbBuildCallee array total))
        (sourceFunctionBody Guest.guestFn_nodedb_build) = (some (.returned value),post) →
      tailCost ≤ post.clock →
      RunBounded (setVarHOLFinite (ofString "nodedb") value {post with locals := s.locals})
        (runAttemptAt 10) tailCost)
    (budget : nodedbBodyCost total + 1 + tailCost ≤ s.clock) :
    RunBounded s (runAttemptAt 9) (nodedbBodyCost total + 1 + tailCost) := by
  rw [source_run_attempt_nodedb_call]
  apply RunBounded.decCall (values := [.val (.word array),.val (.word total)])
    (bodyCost := nodedbBodyCost total) (tailCost := tailCost)
    (eval_run_attempt_nodedb_arguments s si array total input inputLength heap atSi linked) budget
  intro body locals returnShape lookup
  have installed : s.code.lookup (ofString "nodedb_build") =
      some ([(ofString "slice_arr",.one),(ofString "n",.one)],
        sourceFunctionBody Guest.guestFn_nodedb_build,.one) := by
    rw [code]; exact originalRuntimeCode_nodedbBuild_lookup
  rw [pan_two_word_lookup s.code.lookup (ofString "nodedb_build") (ofString "slice_arr") (ofString "n")
    (sourceFunctionBody Guest.guestFn_nodedb_build) array total (by decide) installed] at lookup
  cases lookup
  refine ⟨?_,fun value post ran remaining => tailBounded value post ran remaining⟩
  let entry := callEntryStateHOLFinite s (nodedbBuildCallee array total)
  have countBound := linked.countBound
  have inputBound := inputSmall
  have entryCode : entry.code = originalRuntimeCode := code
  have entryHeap : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) := atHeap
  have entryArena : ∀ a : BitVec 64, a.toNat % 8 = 0 → heap.toNat ≤ a.toNat →
      a.toNat < 33806089496 → entry.memaddrs a := arena
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

#print axioms runBounded_run_attempt_nodedb_call
#print axioms runBounded_run_attempt_nodedb_at9
end InitECandidate.Runtime
