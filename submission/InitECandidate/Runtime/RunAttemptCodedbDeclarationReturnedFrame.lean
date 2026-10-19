import InitECandidate.Runtime.RunAttemptCodedbDeclarationReach
import InitECandidate.Runtime.NodedbDecodedReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem run_attempt_codedb_declaration_returned_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
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
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        ready.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        ready.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        ready.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        (∃ finalHeap : BitVec 64, ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
          (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → ready.memaddrs a)) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w →
          ¬ MWin pad 136 w → ¬ MWin output 32 w → ready.memory w = s.memory w))
      (nodedbBodyCost total + 1) (runAttemptAt 11) := by
  have reached := run_attempt_codedb_declaration_reaches s si heap total array input inputLength statePad pad output
    atSi linked code atHeap aligned capped atState atPad atOutput inputSmall outputAligned windows arena budget
  apply reaches_mono s (runAttemptAt 10) (runAttemptAt 11) _ _ _ _ (Nat.le_refl _) _ reached
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
  obtain ⟨returned,bodyDomain,bodyCode,st,padEq,outEq,finalHeap,wordFrame⟩ :=
    nodedb_decoded_returned_frame entry bodyPost value heap total array statePad pad output input inputLength
      code atHeap aligned capped atState atPad atOutput entryTotal entryArray decoded linked.countBound inputSmall
      outputAligned linked.arrayEnd windows arena bodyBudget run
  refine ⟨?_,domain,installed,?_,?_,?_,?_,?_⟩
  · simpa [returned] using locals
  · rw [globals]; exact st
  · rw [globals]; exact padEq
  · rw [globals]; exact outEq
  · obtain ⟨h,atH,mono,al,cap,live⟩ := finalHeap
    refine ⟨h,?_,mono,al,cap,?_⟩
    · rw [globals]; exact atH
    · intro a aAl lo hi
      rw [domain]
      exact arena a aAl (mono.trans lo) hi
  · intro w below os op oo
    rw [memory]
    exact wordFrame w below os op oo

#print axioms run_attempt_codedb_declaration_returned_frame
end InitECandidate.Runtime
