import InitECandidate.Runtime.HeaderBytesChainContentFrame
import InitECandidate.Runtime.DecodeHeaderEarlyBytesReach
import InitECandidate.Runtime.HeaderDecoderFragmentReach
/-!
Generating the word an actual bytes-field chain writes.

The chain theorem below selects one target record offset that the actual list
writes exactly once and proves, by induction over the list, that the finished chain
holds the word produced by that assignment at `record + target`, together with the
chain frame.  No word is assumed at the target beforehand, so this is generation of
the state root word, not preservation.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- An actual bytes-field chain that writes `target` exactly once returns with the
word it parsed for that field still readable at `record + target`. -/
theorem header_bytes_chain_written_content {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (steps : List (BitVec 64 × BitVec 64 × Nat)) (continuation : ProgHOL 64) (target : Nat)
    (validSteps : ∀ item ∈ steps, item.1.toNat < count.toNat ∧ item.2.2 < 248)
    (once : (steps.filter (fun item => item.2.2 == target)).length = 1)
    (targetBound : target < 248)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : steps.length * (headerRlpFieldCost inputLimit + 1) ≤ s.clock) :
    Reaches s (headerBytesChain steps continuation)
      (fun post => ∃ word : BitVec 64, post.memory (record + BitVec.ofNat 64 target) = .word word ∧
        post.memaddrs (record + BitVec.ofNat 64 target) ∧
        HeaderBytesFrame s post array count input inputLength record ceiling)
      (steps.length * (headerRlpFieldCost inputLimit + 1)) continuation := by
  have targetAbove : ceiling ≤ (record + BitVec.ofNat 64 target).toNat := by
    have targetNat : (BitVec.ofNat 64 target).toNat = target :=
      Nat.mod_eq_of_lt (Nat.lt_trans targetBound (by decide : 248 < 2 ^ 64))
    have sumNat : (record + BitVec.ofNat 64 target).toNat = record.toNat + target := by
      rw [BitVec.toNat_add,targetNat]
      exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
    rw [sumNat]
    omega
  induction steps generalizing s with
  | nil =>
    simp only [List.filter_nil,List.length_nil] at once
    exact absurd once (by decide)
  | cons item rest ih =>
    obtain ⟨index,width,offset⟩ := item
    have valid := validSteps (index,width,offset) (by simp)
    have offsetSmall : offset < 248 := valid.2
    have restValid : ∀ item ∈ rest, item.1.toNat < count.toNat ∧ item.2.2 < 248 :=
      fun item member => validSteps item (by simp [member])
    have restAbove : ceiling ≤ (record + BitVec.ofNat 64 target).toNat := targetAbove
    have costEq : ((index,width,offset) :: rest).length * (headerRlpFieldCost inputLimit + 1) =
        (headerRlpFieldCost inputLimit + 1) + rest.length * (headerRlpFieldCost inputLimit + 1) := by
      simp only [List.length_cons,Nat.succ_mul]
      omega
    rw [costEq] at budget ⊢
    change Reaches s (headerBytesStep index width offset (headerBytesChain rest continuation)) _ _ _
    by_cases writes : offset = target
    · have offsetPreserved : offset = target := writes
      have restFilter : (rest.filter (fun item => item.2.2 == target)).length = 0 := by
        have h := once
        simp only [List.filter_cons] at h
        rw [if_pos (by subst writes; exact beq_iff_eq.mpr rfl)] at h
        simp only [List.length_cons] at h
        omega
      have notWritten : ∀ item ∈ rest, item.2.2 ≠ target := by
        intro item member same
        have memF : item ∈ rest.filter (fun item => item.2.2 == target) :=
          List.mem_filter.mpr ⟨member,by simp [same]⟩
        have hnil : rest.filter (fun item => item.2.2 == target) = [] := by
          cases hf : rest.filter (fun item => item.2.2 == target) with
          | nil => rfl
          | cons x xs => rw [hf] at restFilter; simp at restFilter
        rw [hnil] at memF
        simp at memF
      have first := header_bytes_step_content_frame s array count input inputLength scratch frame record ceiling
        inputLimit index width offset (headerBytesChain rest continuation) valid.2 atArray atRecord before recordFits
        table valid.1 above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
        scratchBelow arena (by omega)
      refine reaches_trans_budget s _ (headerBytesChain rest continuation) continuation _ _ _ _ (by omega) first ?_
      intro parsed facts restBudget
      obtain ⟨written,locals,domainWord,contentWord,tableParsed,domain,installed,globals,memory⟩ := facts
      have atArrayParsed : parsed.locals.lookup (ofString "arr") = some (.val (.word array)) := by
        rw [locals]
        simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
      have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
        rw [locals]
        simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
      have scratchKept : parsed.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) :=
        (globals (ofString "scratch_ptr")).trans scratchGlobal
      have frameKept : parsed.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) :=
        (globals (ofString "frame_mem_ptr")).trans frameGlobal
      have storedParsed : parsed.memory (record + BitVec.ofNat 64 target) = .word written := by
        rw [← offsetPreserved]
        exact contentWord
      have tail := header_bytes_chain_content_frame parsed array count input inputLength scratch frame record
        ceiling inputLimit rest continuation target written restValid notWritten restAbove targetBound storedParsed
        atArrayParsed atRecordParsed before recordFits tableParsed above fits inputBound limitBound scratchKept
        frameKept (installed.trans code) orderedFrame framePositive scratchBelow
        (fun address lo hi => domain ▸ arena address lo hi) restBudget
      refine reaches_mono parsed _ continuation _ _ _ _ (le_refl _) ?_ tail
      intro post kept
      obtain ⟨keptWord,keptFrame⟩ := kept
      have writtenMem : parsed.memaddrs (record + BitVec.ofNat 64 target) := by
        rw [← offsetPreserved]
        exact domainWord
      refine ⟨written,keptWord,keptFrame.domain ▸ writtenMem,keptFrame.table,?_,
        keptFrame.domain.trans domain,keptFrame.code.trans installed,?_,?_⟩
      · intro name different
        rw [keptFrame.locals name different,locals]
        by_cases h : ofString "f" = name
        · exact absurd h.symm different
        · simp [HolFiniteMapExact.lookup_update,FUPDATE,h]
      · intro global
        rw [keptFrame.globals global]
        exact globals global
      · intro address lo hi
        have separate : address ≠ record + BitVec.ofNat 64 offset := by
          intro same
          have offsetNat : (BitVec.ofNat 64 offset).toNat = offset :=
            Nat.mod_eq_of_lt (Nat.lt_trans valid.2 (by decide : 248 < 2 ^ 64))
          have sumO : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
            rw [BitVec.toNat_add,offsetNat]
            exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
          rw [same,sumO] at hi
          omega
        exact (keptFrame.memory address lo hi).trans (memory address lo separate)
    · have noWriteHead : (offset == target) = false := by
        cases hb : (offset == target) with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hb) writes
      have restFilter : (rest.filter (fun item => item.2.2 == target)).length = 1 := by
        have h := once
        simp only [List.filter_cons] at h
        rw [if_neg (by rw [noWriteHead]; decide)] at h
        exact h
      have headNot : offset ≠ target := writes
      have first := header_bytes_step_content_frame s array count input inputLength scratch frame record ceiling
        inputLimit index width offset (headerBytesChain rest continuation) valid.2 atArray atRecord before recordFits
        table valid.1 above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
        scratchBelow arena (by omega)
      refine reaches_trans_budget s _ (headerBytesChain rest continuation) continuation _ _ _ _ (by omega) first ?_
      intro parsed facts restBudget
      obtain ⟨written,locals,domainWord,contentWord,tableParsed,domain,installed,globals,memory⟩ := facts
      have atArrayParsed : parsed.locals.lookup (ofString "arr") = some (.val (.word array)) := by
        rw [locals]
        simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
      have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
        rw [locals]
        simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
      have scratchKept : parsed.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) :=
        (globals (ofString "scratch_ptr")).trans scratchGlobal
      have frameKept : parsed.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) :=
        (globals (ofString "frame_mem_ptr")).trans frameGlobal
      have tail := ih parsed restValid restFilter atArrayParsed atRecordParsed tableParsed scratchKept
        frameKept (installed.trans code) (fun address lo hi => domain ▸ arena address lo hi) restBudget
      refine reaches_mono parsed _ continuation _ _ _ _ (le_refl _) ?_ tail
      intro post kept
      obtain ⟨word,keptWord,keptMem,keptFrame⟩ := kept
      have separate : (record + BitVec.ofNat 64 target) ≠ (record + BitVec.ofNat 64 offset) := by
        intro same
        have targetNat : (BitVec.ofNat 64 target).toNat = target :=
          Nat.mod_eq_of_lt (Nat.lt_trans targetBound (by decide : 248 < 2 ^ 64))
        have offsetNat : (BitVec.ofNat 64 offset).toNat = offset :=
          Nat.mod_eq_of_lt (Nat.lt_trans valid.2 (by decide : 248 < 2 ^ 64))
        have both := congrArg BitVec.toNat same
        rw [BitVec.toNat_add,BitVec.toNat_add,targetNat,offsetNat] at both
        have sumT : (record.toNat + target) % 2 ^ 64 = record.toNat + target :=
          Nat.mod_eq_of_lt (by have h := recordFits; omega)
        have sumO : (record.toNat + offset) % 2 ^ 64 = record.toNat + offset :=
          Nat.mod_eq_of_lt (by have h := recordFits; omega)
        rw [sumT,sumO] at both
        have sameOffset : offset = target := by omega
        exact headNot sameOffset
      refine ⟨word,keptWord,keptMem,keptFrame.table,?_,keptFrame.domain.trans domain,
        keptFrame.code.trans installed,?_,?_⟩
      · intro name different
        rw [keptFrame.locals name different,locals]
        by_cases h : ofString "f" = name
        · exact absurd h.symm different
        · simp [HolFiniteMapExact.lookup_update,FUPDATE,h]
      · intro global
        rw [keptFrame.globals global]
        exact globals global
      · intro address lo hi
        have distinctBelow : address ≠ record + BitVec.ofNat 64 offset := by
          intro same
          have offsetNat : (BitVec.ofNat 64 offset).toNat = offset :=
            Nat.mod_eq_of_lt (Nat.lt_trans offsetSmall (by decide : 248 < 2 ^ 64))
          have sumO : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
            rw [BitVec.toNat_add,offsetNat]
            exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
          rw [same,sumO] at hi
          omega
        exact (keptFrame.memory address lo hi).trans (memory address lo distinctBelow)

#print axioms header_bytes_chain_written_content
end InitECandidate.Runtime
