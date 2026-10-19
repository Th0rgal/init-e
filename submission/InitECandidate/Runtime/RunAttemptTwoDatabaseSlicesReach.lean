import InitECandidate.Runtime.RunAttemptTwoDatabaseValuesReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Original witness slices survive a protected builder frame. Empty arrays
need no unused address-separation premise. -/
theorem witness_slices_after_protected_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array total input inputLength heap statePad pad output : BitVec 64) (ceiling : Nat)
    (slices : RlpSliceInputPrefix s array input inputLength total.toNat)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ heap.toNat)
    (above : total.toNat = 0 ∨ ceiling ≤ array.toNat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling) (domain : post.memaddrs = s.memaddrs)
    (frame : ∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w → ¬ MWin pad 136 w →
      ¬ MWin output 32 w → post.memory w = s.memory w) :
    RlpSliceInputPrefix post array input inputLength total.toNat := by
  rcases above with empty | above
  · intro index inside
    omega
  · apply RlpSliceInputPrefix.after_memory_between s post array total input inputLength heap ceiling slices above
      arrayEnd domain
    intro address upper lower
    exact frame address upper (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))

/-- Both original witness slice arrays remain available alongside the actual
constructed tables and value-membership facts at the state-init call. -/
theorem run_attempt_two_database_slices_input_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (inputLimit : Nat) (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (budget : 2 * nodedbInputCallCost inputLimit ≤ s.clock)
    (ceiling : Nat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove₁ : total₁.toNat = 0 ∨ ceiling ≤ array₁.toNat)
    (arrayAbove₂ : total₂.toNat = 0 ∨ ceiling ≤ array₂.toNat) :
    Reaches s (runAttemptAt 9)
      (fun final => (∃ midHeap finalHeap : BitVec 64,
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
        (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → final.memaddrs a) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w → ¬ MWin pad 136 w →
          ¬ MWin output 32 w → final.memory w = s.memory w)) ∧
        RlpSliceInputPrefix final array₁ input inputLength total₁.toNat ∧
        RlpSliceInputPrefix final array₂ input inputLength total₂.toNat)
      (2 * nodedbInputCallCost inputLimit) (runAttemptAt 11) := by
  have reached := run_attempt_two_database_values_input_reaches s si heap total₁ array₁ total₂ array₂ input
    inputLength statePad pad output atSi linked₁ linked₂ code atHeap aligned capped atState atPad atOutput
    inputSmall outputAligned windows₁ windows₂ arena inputLimit inputBound inputCap budget ceiling
    stateBelow padBelow outputBelow recordAbove recordBefore arrayAbove₁ arrayAbove₂
  refine reaches_mono s (runAttemptAt 9) (runAttemptAt 11) _ _ _ _ (Nat.le_refl _) ?_ reached
  intro final facts
  have retained := facts
  obtain ⟨midHeap,finalHeap,locals,domain,installed,endian,st,pa,out,hp,mono₁,mono₂,al,cap,
    entries₁,entries₂,table₁,table₂,arenaFinal,frame⟩ := facts
  exact ⟨retained,
    witness_slices_after_protected_frame s final array₁ total₁ input inputLength heap statePad pad output ceiling
      linked₁.slices linked₁.arrayEnd arrayAbove₁ stateBelow padBelow outputBelow domain frame,
    witness_slices_after_protected_frame s final array₂ total₂ input inputLength heap statePad pad output ceiling
      linked₂.slices linked₂.arrayEnd arrayAbove₂ stateBelow padBelow outputBelow domain frame⟩

#print axioms witness_slices_after_protected_frame
#print axioms run_attempt_two_database_slices_input_reaches
end InitECandidate.Runtime
