import InitECandidate.Runtime.RunAttemptTwoDatabaseInitializedGlobals
import InitECandidate.Runtime.RunAttemptStateInitArguments
import InitECandidate.Runtime.RunAttemptStateInitLookup
/-!
The selected parent survives both database builds.

`run_attempt` declares `parent := vh[nh-1]` before the two database builds; those builds allocate
their tables from the live heap, so the parent record (`parent .. parent+248`) sits below the initial
live heap, outside the keccak state, pad and output windows, and is never rewritten.  This module
keeps the selected parent and its state root word readable through the actual `runAttemptAt 9` to
`runAttemptAt 11` run, while retaining the entire metadata the existing two-database theorem
exports.  Every frame and growth fact comes from that actual theorem: no callee and no frame
callback is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- **The selected parent through both database builds.**  Given the typed `parent` local, its
state root word and domain, the record below the initial live heap and above the ceiling, the actual
two-database run keeps the whole metadata predicate and additionally keeps the typed `parent`
local, the state root word, its domain, the final live heap binding and the record's extent below
that final heap. -/
theorem run_attempt_selected_parent_initialized_database_reaches {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (si heap total₁ array₁ total₂ array₂ input inputLength statePad pad output : BitVec 64)
    (parent word : BitVec 64) (ceiling : Nat)
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
    (arrayAbove₂ : total₂.toNat = 0 ∨ ceiling ≤ array₂.toNat) :
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
        (∀ key, key ∈ nodedbInitializerGlobals → final.globals.lookup key=s.globals.lookup key))
      ((nodedbBodyCost total₁ + 1) + (nodedbBodyCost total₂ + 1)) (runAttemptAt 11) := by
  have reached := run_attempt_two_database_initialized_globals_reaches s si heap total₁ array₁ total₂ array₂ input
    inputLength statePad pad output atSi linked₁ linked₂ code atHeap aligned capped atState atPad
    atOutput inputSmall outputAligned windows₁ windows₂ arena budget ceiling stateBelow padBelow
    outputBelow recordAbove recordBefore arrayAbove₁ arrayAbove₂
  refine reaches_mono s (runAttemptAt 9) (runAttemptAt 11) _ _ _ _ (Nat.le_refl _) ?_ reached
  intro final facts
  obtain ⟨midHeap,finalHeap,localsEq,domainEq,codeEq,beEq,stEq,padEq,outEq,heapEq,mono₁,mono₂,aligned',
    capped',entries₁,entries₂,table₁,table₂,live,frame,globals⟩ := facts
  have addressEq : (parent + 32#64).toNat = parent.toNat + 32 := by
    have top := heap.isLt
    have small : (32#64).toNat < 88 := by decide
    have h32 : (32#64).toNat = 32 := by decide
    rw [BitVec.toNat_add_of_lt (by omega)]
    omega
  have above : ceiling ≤ (parent + 32#64).toNat := by
    rw [addressEq]
    omega
  have below : (parent + 32#64).toNat < heap.toNat := by
    rw [addressEq]
    omega
  refine ⟨midHeap,finalHeap,localsEq,domainEq,codeEq,beEq,stEq,padEq,outEq,heapEq,mono₁,mono₂,
    aligned',capped',entries₁,entries₂,table₁,table₂,live,frame,?_,?_,?_,?_,?_,?_,globals⟩
  · rw [localsEq]
    have codDifferent : (ofString "codedb" == ofString "parent") = false := by decide
    have nodDifferent : (ofString "nodedb" == ofString "parent") = false := by decide
    simp only [HolFiniteMapExact.lookup_update,FUPDATE,codDifferent,nodDifferent]
    exact atParent
  · exact (frame (parent + 32#64) below (mwin_below (by omega)) (mwin_below (by omega))
      (mwin_below (by omega))).trans rootWord
  · exact domainEq ▸ rootDomain
  · omega
  · have atNodes : final.locals.lookup (ofString "nodedb") = some (.val (.word heap)) := by
      rw [localsEq]
      have different : (ofString "codedb" == ofString "nodedb") = false := by decide
      simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
    have atParentFinal : final.locals.lookup (ofString "parent") = some (.val (.word parent)) := by
      rw [localsEq]
      have codDifferent : (ofString "codedb" == ofString "parent") = false := by decide
      have nodDifferent : (ofString "nodedb" == ofString "parent") = false := by decide
      simpa [HolFiniteMapExact.lookup_update,FUPDATE,codDifferent,nodDifferent] using atParent
    have atCodes : final.locals.lookup (ofString "codedb") = some (.val (.word midHeap)) := by
      rw [localsEq]
      have different : (ofString "nodedb" == ofString "codedb") = false := by decide
      simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
    exact eval_run_attempt_state_init_arguments final heap parent word midHeap atNodes atParentFinal
      atCodes (domainEq ▸ rootDomain)
      ((frame (parent + 32#64) below (mwin_below (by omega)) (mwin_below (by omega))
        (mwin_below (by omega))).trans rootWord)
  · rw [codeEq,code]
    exact lookup_state_init_callee heap word midHeap

#print axioms run_attempt_selected_parent_initialized_database_reaches
end InitECandidate.Runtime
