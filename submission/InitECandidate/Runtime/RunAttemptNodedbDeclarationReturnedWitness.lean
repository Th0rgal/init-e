import InitECandidate.Runtime.RunAttemptNodedbDeclarationReturnedFrame
import InitECandidate.Runtime.NodedbDecodedReturnedWitnessArray
/-!
The actual At9 declaration retains the record's linked witness at the builder's
real frontier.

`run_attempt_nodedb_declaration_returned_frame` lifts the returned builder frame
through the actual At9 declaration.  This module additionally transports the
witness array of the very record the declaration read (`si`, offsets 40 and 48)
to the builder's real returned frontier, derived from the original actual
declaration reach evidence and the actual body run.  No callee contract is
assumed: the only extra premises are the explicit entry geometry of the old
record window (a ceiling above the three workspace windows, the record below the
entry heap pointer) and the usual empty-list exception for the witness array.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual At9 node-database declaration returns the builder's real frontier,
its workspace globals and the caller domain and code, and keeps the record's
linked witness at that frontier. -/
theorem run_attempt_nodedb_declaration_returned_witness {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : nodedbBodyCost total + 1 ≤ s.clock)
    (ceiling : Nat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove : total.toNat = 0 ∨ ceiling ≤ array.toNat) :
    Reaches s (runAttemptAt 9)
      (fun ready => ready.locals = s.locals.update (ofString "nodedb",.val (.word heap)) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        ready.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        ready.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        ready.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        (∃ finalHeap : BitVec 64, ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
          WitnessArrayLinked ready si 40 48 array total input inputLength finalHeap ∧
          (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
            ready.memaddrs a)) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w →
          ¬ MWin pad 136 w → ¬ MWin output 32 w → ready.memory w = s.memory w))
      (nodedbBodyCost total + 1) (runAttemptAt 10) := by
  have reached := run_attempt_nodedb_declaration_reaches s si heap total array input inputLength statePad pad
    output atSi linked code atHeap aligned capped atState atPad atOutput inputSmall outputAligned windows arena budget
  apply reaches_mono s (runAttemptAt 9) (runAttemptAt 10) _ _ _ _ (Nat.le_refl _) _ reached
  intro ready facts
  obtain ⟨value,bodyPost,run,locals,memory,globals,domain,installed⟩ := facts
  let entry := callEntryStateHOLFinite s (nodedbBuildCallee array total)
  have decoded : RlpSliceInputPrefix entry array input inputLength total.toNat := by
    intro j inside
    obtain ⟨p,l,e⟩ := linked.slices j inside
    exact ⟨p,l,e.after_frame s entry array j p l input inputLength rfl rfl rfl⟩
  have entryTotal : entry.locals.lookup (ofString "n") = some (.val (.word total)) := by
    simp [entry,callEntryStateHOLFinite,nodedbBuildCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryArray : entry.locals.lookup (ofString "slice_arr") = some (.val (.word array)) := by
    simp (config := {decide := true}) [entry,callEntryStateHOLFinite,nodedbBuildCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bodyBudget : nodedbBodyCost total ≤ entry.clock := by
    change nodedbBodyCost total ≤ s.clock - 1
    omega
  have bodyMetadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_nodedb_build)
  rw [run] at bodyMetadata
  obtain ⟨valueEq,bodyDomain,bodyCode,st,padEq,outEq,_,frame⟩ :=
    nodedb_decoded_returned_frame entry bodyPost value heap total array statePad pad output input inputLength
      code atHeap aligned capped atState atPad atOutput entryTotal entryArray decoded linked.countBound inputSmall
      outputAligned linked.arrayEnd windows arena bodyBudget run
  obtain ⟨finalHeap,bodyAtHeap,bodyMono,bodyAligned,bodyBound,bodyLinked,bodyLive⟩ :=
    nodedb_decoded_returned_witness_array entry bodyPost value heap total array statePad pad output input inputLength
      code atHeap aligned capped atState atPad atOutput entryTotal entryArray decoded linked.countBound inputSmall
      outputAligned linked.arrayEnd windows arena bodyBudget run ceiling stateBelow padBelow outputBelow
      si 40 48 array total input inputLength
      (linked.after_frame s entry si 40 48 array total input inputLength heap rfl rfl) (by decide) (by decide)
      recordAbove recordBefore arrayAbove
  have readyDomain : ready.memaddrs = bodyPost.memaddrs := by
    rw [domain]
    exact bodyMetadata.2.1.symm
  refine ⟨?_,domain,installed,?_,?_,?_,?_,?_⟩
  · simpa [valueEq] using locals
  · rw [globals]
    exact st
  · rw [globals]
    exact padEq
  · rw [globals]
    exact outEq
  · refine ⟨finalHeap,?_,bodyMono,bodyAligned,bodyBound,?_,?_⟩
    · rw [globals]
      exact bodyAtHeap
    · exact bodyLinked.after_frame bodyPost ready si 40 48 array total input inputLength finalHeap readyDomain memory
    · intro a aAl lo hi
      rw [readyDomain]
      exact bodyLive a aAl lo hi
  · intro w below os op oo
    rw [memory]
    exact frame w below os op oo

#print axioms run_attempt_nodedb_declaration_returned_witness
end InitECandidate.Runtime
