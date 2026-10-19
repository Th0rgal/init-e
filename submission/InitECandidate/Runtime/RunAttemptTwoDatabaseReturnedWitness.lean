import InitECandidate.Runtime.RunAttemptCodedbDeclarationReturnedFrame
import InitECandidate.Runtime.RunAttemptNodedbDeclarationReturnedWitness
import InitECandidate.Runtime.RunBoundedReaches
/-!
The two actual database calls, with both record witnesses retained.

The At9 node-database declaration and the At10 code-database declaration each
return the builder's real frontier and keep the witness array of the record they
read (offsets 40/48 and 56/64 of the same stateless-input record).  Both lifts are
derived from the original actual declaration reach evidence and the actual body
run, so no callee contract is assumed; the only extra premises are the explicit
entry geometry of the old record window and the usual empty-list exceptions.

Composing them with `reaches_trans_budget` gives one actual two-call run whose
returned state keeps both linked witnesses at the final frontier.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual At10 code-database declaration returns the builder's real frontier,
its workspace globals and the caller domain and code, and keeps the record's
linked witness at that frontier. -/
theorem run_attempt_codedb_declaration_returned_witness {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (budget : nodedbBodyCost total + 1 ≤ s.clock)
    (ceiling : Nat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove : total.toNat = 0 ∨ ceiling ≤ array.toNat) :
    Reaches s (runAttemptAt 10)
      (fun ready => ready.locals = s.locals.update (ofString "codedb",.val (.word heap)) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        ready.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        ready.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        ready.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        (∃ finalHeap : BitVec 64, ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
          WitnessArrayLinked ready si 56 64 array total input inputLength finalHeap ∧
          (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
            ready.memaddrs a)) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w →
          ¬ MWin pad 136 w → ¬ MWin output 32 w → ready.memory w = s.memory w))
      (nodedbBodyCost total + 1) (runAttemptAt 11) := by
  have reached := run_attempt_codedb_declaration_reaches s si heap total array input inputLength statePad pad
    output atSi linked code atHeap aligned capped atState atPad atOutput inputSmall outputAligned windows arena budget
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
      si 56 64 array total input inputLength
      (linked.after_frame s entry si 56 64 array total input inputLength heap rfl rfl) (by decide) (by decide)
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
    · exact bodyLinked.after_frame bodyPost ready si 56 64 array total input inputLength finalHeap readyDomain memory
    · intro a aAl lo hi
      rw [readyDomain]
      exact bodyLive a aAl lo hi
  · intro w below os op oo
    rw [memory]
    exact frame w below os op oo

#print axioms run_attempt_codedb_declaration_returned_witness

/-- The actual node-database declaration followed by the actual code-database
declaration returns the builder's real frontier with both record witnesses still
linked at it. -/
theorem run_attempt_two_database_returned_witness {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si heap total₁ array₁ total₂ array₂ input inputLength statePad pad output : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked₁ : WitnessArrayLinked s si 40 48 array₁ total₁ input inputLength heap)
    (linked₂ : WitnessArrayLinked s si 56 64 array₂ total₂ input inputLength heap)
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (aligned : heap.toNat % 8 = 0) (capped : heap.toNat ≤ 33806089496)
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (inputSmall : inputLength.toNat ≤ 134217712) (outputAligned : output.toNat % 8 = 0)
    (windows₁ : total₁ ≠ 0 → statePad.toNat + 200 ≤ array₁.toNat ∧ pad.toNat + 136 ≤ array₁.toNat ∧
      output.toNat + 32 ≤ array₁.toNat)
    (windows₂ : total₂ ≠ 0 → statePad.toNat + 200 ≤ array₂.toNat ∧ pad.toNat + 136 ≤ array₂.toNat ∧
      output.toNat + 32 ≤ array₂.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → heap.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a)
    (budget : (nodedbBodyCost total₁ + 1) + (nodedbBodyCost total₂ + 1) ≤ s.clock)
    (ceiling : Nat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove₁ : total₁.toNat = 0 ∨ ceiling ≤ array₁.toNat)
    (arrayAbove₂ : total₂.toNat = 0 ∨ ceiling ≤ array₂.toNat) :
    Reaches s (runAttemptAt 9)
      (fun final => final.memaddrs = s.memaddrs ∧ final.code = s.code ∧
        final.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        final.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        final.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        (∃ finalHeap : BitVec 64, final.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
          WitnessArrayLinked final si 40 48 array₁ total₁ input inputLength finalHeap ∧
          WitnessArrayLinked final si 56 64 array₂ total₂ input inputLength finalHeap ∧
          (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
            final.memaddrs a)))
      ((nodedbBodyCost total₁ + 1) + (nodedbBodyCost total₂ + 1)) (runAttemptAt 11) := by
  have first := run_attempt_nodedb_declaration_returned_witness s si heap total₁ array₁ input inputLength
    statePad pad output atSi linked₁ code atHeap aligned capped atState atPad atOutput inputSmall outputAligned
    windows₁ arena (by omega) ceiling stateBelow padBelow outputBelow recordAbove recordBefore arrayAbove₁
  refine reaches_trans_budget s (runAttemptAt 9) (runAttemptAt 10) (runAttemptAt 11) _ _ _ _ (by omega) first ?_
  intro ready facts secondBudget
  obtain ⟨locals₁,domain₁,code₁,st₁,pad₁,out₁,⟨h₂,atH₂,mono₂,al₂,cap₂,linkedAt₁,live₂⟩,frame₁⟩ := facts
  have atSi₁ : ready.locals.lookup (ofString "si") = some (.val (.word si)) := by
    rw [locals₁]
    have different : (ofString "nodedb" == ofString "si") = false := by decide
    simp only [HolFiniteMapExact.lookup_update,FUPDATE,different]
    exact atSi
  have window₁ : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      ready.memory address = s.memory address := by
    intro address lower upper
    exact frame₁ address upper (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))
  have addressNat (offset : BitVec 64) (inside : offset.toNat < 88) :
      (si + offset).toNat = si.toNat + offset.toNat := by
    have top := heap.isLt
    rw [BitVec.toNat_add_of_lt (by omega)]
  have posAbove (offset : BitVec 64) (inside : offset.toNat < 88) : ceiling ≤ (si + offset).toNat := by
    rw [addressNat offset inside]
    omega
  have posBefore (offset : BitVec 64) (inside : offset.toNat < 88) : (si + offset).toNat < heap.toNat := by
    rw [addressNat offset inside]
    omega
  have posBefore₂ (offset : BitVec 64) (inside : offset.toNat < 88) : (si + offset).toNat < h₂.toNat := by
    rw [addressNat offset inside]
    omega
  have linked₂' : WitnessArrayLinked ready si 56 64 array₂ total₂ input inputLength h₂ :=
    linked₂.after_memory_between_or_empty s ready si 56 64 array₂ total₂ input inputLength heap h₂ ceiling
      (posAbove 56 (by decide)) (posBefore 56 (by decide))
      (posAbove 64 (by decide)) (posBefore 64 (by decide))
      arrayAbove₂ mono₂ domain₁ window₁
  have recordBefore₂ : si.toNat + 88 ≤ h₂.toNat := by omega
  have second := run_attempt_codedb_declaration_returned_witness ready si h₂ total₂ array₂ input inputLength
    statePad pad output atSi₁ linked₂' (code₁.trans code) atH₂ al₂ cap₂ st₁ pad₁ out₁ inputSmall outputAligned windows₂
    live₂ secondBudget ceiling stateBelow padBelow outputBelow recordAbove recordBefore₂ arrayAbove₂
  refine reaches_mono ready (runAttemptAt 10) (runAttemptAt 11) _ _ _ _ (Nat.le_refl _) ?_ second
  intro final q
  obtain ⟨locals₂,domain₂,code₂,st₂,pad₂,out₂,⟨h₃,atH₃,mono₃,al₃,cap₃,linkedAt₂,live₃⟩,frame₂⟩ := q
  have window₂ : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < h₂.toNat →
      final.memory address = ready.memory address := by
    intro address lower upper
    exact frame₂ address upper (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))
  have linkedFirst : WitnessArrayLinked final si 40 48 array₁ total₁ input inputLength h₃ :=
    linkedAt₁.after_memory_between_or_empty ready final si 40 48 array₁ total₁ input inputLength h₂ h₃ ceiling
      (posAbove 40 (by decide)) (posBefore₂ 40 (by decide))
      (posAbove 48 (by decide)) (posBefore₂ 48 (by decide))
      arrayAbove₁ mono₃ domain₂ window₂
  exact ⟨domain₂.trans domain₁,code₂.trans code₁,st₂,pad₂,out₂,
    ⟨h₃,atH₃,mono₂.trans mono₃,al₃,cap₃,linkedFirst,linkedAt₂,live₃⟩⟩

#print axioms run_attempt_two_database_returned_witness
end InitECandidate.Runtime
