import InitECandidate.Runtime.RunAttemptTwoDatabaseTablesReach
import InitECandidate.Runtime.RunAttemptNodedbDeclarationValuesReach
import InitECandidate.Runtime.RunAttemptCodedbDeclarationValuesReach
import InitECandidate.Runtime.NodedbValuesInFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem run_attempt_two_database_values_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
        (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → final.memaddrs a) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w → ¬ MWin pad 136 w →
          ¬ MWin output 32 w → final.memory w = s.memory w))
      ((nodedbBodyCost total₁ + 1) + (nodedbBodyCost total₂ + 1)) (runAttemptAt 11) := by
  have first := run_attempt_nodedb_declaration_values_reaches s si heap total₁ array₁ input inputLength
    statePad pad output atSi linked₁ code atHeap aligned capped atState atPad atOutput inputSmall outputAligned
    windows₁ arena (by omega)
  refine reaches_trans_budget s (runAttemptAt 9) (runAttemptAt 10) (runAttemptAt 11) _ _ _ _ budget first ?_
  intro ready facts secondBudget
  obtain ⟨locals₁,domain₁,code₁,endian₁,st₁,pad₁,out₁,entries₁,
    ⟨k₁,sd₁,c₁,u₁,v₁,o₁,op₁,n₁,b₁,h₂,count₁,capBound₁,room₁,inv₁,order₁,atH₂,extent₁,mono₂,al₂,cap₂,live₂⟩,frame₁⟩ := facts
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
  have second := run_attempt_codedb_declaration_values_reaches ready si h₂ total₂ array₂ input inputLength
    statePad pad output atSi₁ linked₂' (code₁.trans code) atH₂ al₂ cap₂ st₁ pad₁ out₁ inputSmall outputAligned windows₂
    live₂ secondBudget
  refine reaches_mono ready (runAttemptAt 10) (runAttemptAt 11) _ _ _ _ (Nat.le_refl _) ?_ second
  intro final facts₂
  obtain ⟨locals₂,domain₂,code₂,endian₂,st₂,pad₂,out₂,entries₂,
    ⟨k₂,sd₂,c₂,u₂,v₂,o₂,op₂,n₂,b₂,h₃,count₂,capBound₂,room₂,inv₂,order₂,atH₃,extent₂,mono₃,al₃,cap₃,live₃⟩,frame₂⟩ := facts₂
  have old := nodedb_old_table_after_protected_frame ready final 32 heap k₁ sd₁ c₁ u₁ v₁ o₁ op₁ n₁ h₂
    statePad pad output b₁ inv₁ order₁ extent₁ (by omega) (by omega) (by omega) domain₂ endian₂ code₂ frame₂
  refine ⟨h₂,h₃,?_,domain₂.trans domain₁,code₂.trans code₁,endian₂.trans endian₁,st₂,pad₂,out₂,atH₃,
    mono₂,mono₃,al₃,cap₃,?_,entries₂,?_,?_,live₃,?_⟩
  · rw [locals₂,locals₁]
  · apply entries₁.after_table_frame ready final (NodedbSliceTargets array₁ total₁) 32 heap k₁ sd₁ c₁ u₁ v₁
      o₁ op₁ n₁ b₁ inv₁ domain₂ endian₂
    intro w lower upper
    exact frame₂ w (by omega) (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))
  · exact ⟨k₁,sd₁,c₁,u₁,v₁,o₁,op₁,n₁,b₁,count₁,capBound₁,room₁,old.1,old.2,by omega⟩
  · exact ⟨k₂,sd₂,c₂,u₂,v₂,o₂,op₂,n₂,b₂,count₂,capBound₂,room₂,inv₂,order₂,extent₂⟩
  · intro w below os op oo
    exact (frame₂ w (by omega) os op oo).trans (frame₁ w below os op oo)

#print axioms run_attempt_two_database_values_reaches
theorem run_attempt_two_database_values_input_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
        (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → final.memaddrs a) ∧
        (∀ w : BitVec 64, w.toNat < heap.toNat → ¬ MWin statePad 200 w → ¬ MWin pad 136 w →
          ¬ MWin output 32 w → final.memory w = s.memory w))
      (2 * nodedbInputCallCost inputLimit) (runAttemptAt 11) := by
  have cost₁ := nodedb_call_cost_le_input total₁ inputLength inputLimit linked₁.countBound inputBound inputCap
  have cost₂ := nodedb_call_cost_le_input total₂ inputLength inputLimit linked₂.countBound inputBound inputCap
  have reached := run_attempt_two_database_values_reaches s si heap total₁ array₁ total₂ array₂ input inputLength
    statePad pad output atSi linked₁ linked₂ code atHeap aligned capped atState atPad atOutput inputSmall outputAligned
    windows₁ windows₂ arena (by omega) ceiling stateBelow padBelow outputBelow recordAbove recordBefore
    arrayAbove₁ arrayAbove₂
  exact reaches_mono s (runAttemptAt 9) (runAttemptAt 11) _ _ _ _ (by omega) (fun _ h => h) reached

#print axioms run_attempt_two_database_values_input_reaches
end InitECandidate.Runtime
