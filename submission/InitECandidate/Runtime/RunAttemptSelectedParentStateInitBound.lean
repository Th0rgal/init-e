import InitECandidate.Runtime.StateInitCallerDatabaseBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual selected-parent/two-database prefix retains all original metadata
and now derives the original state_init callee runtime bound from real contents. -/
theorem run_attempt_selected_parent_state_init_bound_reaches {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (si heap total₁ array₁ total₂ array₂ input inputLength statePad pad output : BitVec 64)
    (parent word oldWs emptyRoot : BitVec 64) (ceiling : Nat)
    (atParent : s.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (rootWord : s.memory (parent + 32#64) = .word word)
    (rootDomain : s.memaddrs (parent + 32#64))
    (parentAbove : ceiling ≤ parent.toNat) (parentBefore : parent.toNat + 248 ≤ heap.toNat)
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
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove₁ : total₁.toNat = 0 ∨ ceiling ≤ array₁.toNat)
    (arrayAbove₂ : total₂.toNat = 0 ∨ ceiling ≤ array₂.toNat)
    (inputAddress : input=(2713731432#64)) (fixedCeiling : ceiling=2713731432)
    (inputEnd : input.toNat+inputLength.toNat≤heap.toNat)
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
    (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word (2713714688#64))))
    (atFrame : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word (2701135872#64))))
    (atWs : s.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
    (atEmpty : s.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot))) :
    Reaches s (runAttemptAt 9)
      (fun final => ∃ midHeap finalHeap : BitVec 64,
        final.locals = (s.locals.update (ofString "nodedb",.val (.word heap))).update
          (ofString "codedb",.val (.word midHeap)) ∧
        final.memaddrs = s.memaddrs ∧ final.code = s.code ∧ final.be = s.be ∧
        final.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
        final.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
        final.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
        final.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        heap.toNat ≤ midHeap.toNat ∧ midHeap.toNat ≤ finalHeap.toNat ∧
        finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
        HashTableValuesIn heap (NodedbSliceTargets array₁ total₁) final ∧
        HashTableValuesIn midHeap (NodedbSliceTargets array₂ total₂) final ∧
        NodedbTableAt final heap finalHeap total₁ ∧ NodedbTableAt final midHeap finalHeap total₂ ∧
        (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
          final.memaddrs a) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w → ¬ MWin pad 136 w →
          ¬ MWin output 32 w → final.memory w = s.memory w) ∧
        final.locals.lookup (ofString "parent") = some (.val (.word parent)) ∧
        final.memory (parent + 32#64) = .word word ∧
        final.memaddrs (parent + 32#64) ∧
        parent.toNat + 248 ≤ finalHeap.toNat ∧
        evalListHOLFinite final (h := fun a => Classical.propDecidable (final.memaddrs a))
          runAttemptStateInitArguments =
          some [.val (.word heap),.val (.word word),.val (.word midHeap)] ∧
        lookupCodeHOLFinite final.code.lookup (ofString "state_init")
          [.val (.word heap),.val (.word word),.val (.word midHeap)] =
          some (sourceFunctionBody Guest.guestFn_state_init,stateInitCallee heap word midHeap,.one) ∧
        (∀ key, key ∈ nodedbInitializerGlobals → final.globals.lookup key=s.globals.lookup key) ∧
        (stateInitSourceCeiling+1≤final.clock → RunBounded
          (callEntryStateHOLFinite final (stateInitCallee heap word midHeap))
          (sourceFunctionBody Guest.guestFn_state_init) stateInitSourceCeiling))
      ((nodedbBodyCost total₁ + 1) + (nodedbBodyCost total₂ + 1)) (runAttemptAt 11) := by
  subst input
  subst ceiling
  have reached := run_attempt_selected_parent_initialized_database_reaches s si heap total₁ array₁ total₂ array₂
    2713731432 inputLength statePad pad output parent word 2713731432 atParent rootWord rootDomain parentAbove parentBefore
    atSi linked₁ linked₂ code atHeap aligned capped atState atPad atOutput inputSmall outputAligned windows₁ windows₂ arena
    budget stateBelow padBelow outputBelow recordAbove recordBefore arrayAbove₁ arrayAbove₂
  refine reaches_mono s (runAttemptAt 9) (runAttemptAt 11) _ _ _ _ (Nat.le_refl _) ?_ reached
  intro final facts
  obtain ⟨midHeap,finalHeap,localsEq,domainEq,codeEq,beEq,stEq,padEq,outEq,heapEq,mono₁,mono₂,aligned',
    capped',entries₁,entries₂,table₁,table₂,live,frame,parentLocal,parentRoot,parentDomain,parentExtent,args,lookup,globals⟩ := facts
  refine ⟨midHeap,finalHeap,localsEq,domainEq,codeEq,beEq,stEq,padEq,outEq,heapEq,mono₁,mono₂,aligned',
    capped',entries₁,entries₂,table₁,table₂,live,frame,parentLocal,parentRoot,parentDomain,parentExtent,args,lookup,globals,?_⟩
  intro ticks
  exact runBounded_state_init_from_database_frame s final si heap array₁ total₁ inputLength statePad pad output midHeap finalHeap
    word oldWs emptyRoot linked₁ inputSmall inputEnd code codeEq domainEq fullDomain heapEq (mono₁.trans mono₂)
    aligned' capped' table₁ entries₁ arrayAbove₁ stateBelow padBelow outputBelow frame globals atScratch atFrame atWs atEmpty ticks

#print axioms run_attempt_selected_parent_state_init_bound_reaches
end InitECandidate.Runtime
