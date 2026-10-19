import InitECandidate.Runtime.HeaderBytesStepContentFrame
import InitECandidate.Runtime.RunBoundedReaches
/-!
A word stored in the header record survives the actual bytes-field chain.

Each actual bytes-field step changes exactly the eight bytes of its own record
destination, so any word at an offset no step of the chain writes (for instance the
state root word at offset 32 when only the later fields are decoded) is still
there when the whole finite chain finishes, together with the usual chain frame.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- A word already stored at an offset the actual chain never writes survives the
whole chain, with the chain's own frame. -/
theorem header_bytes_chain_content_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (steps : List (BitVec 64 × BitVec 64 × Nat)) (continuation : ProgHOL 64)
    (preserved : Nat) (word : BitVec 64)
    (validSteps : ∀ item ∈ steps, item.1.toNat < count.toNat ∧ item.2.2 < 248)
    (notWritten : ∀ item ∈ steps, item.2.2 ≠ preserved)
    (preservedAbove : ceiling ≤ (record + BitVec.ofNat 64 preserved).toNat)
    (preservedBound : preserved < 248)
    (stored : s.memory (record + BitVec.ofNat 64 preserved) = .word word)
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
      (fun post => post.memory (record + BitVec.ofNat 64 preserved) = .word word ∧
        HeaderBytesFrame s post array count input inputLength record ceiling)
      (steps.length * (headerRlpFieldCost inputLimit + 1)) continuation := by
  induction steps generalizing s with
  | nil =>
    exact Or.inl ⟨s,⟨stored,⟨table,fun _ _ => rfl,rfl,rfl,fun _ => rfl,fun _ _ _ => rfl⟩⟩,by simp,le_refl _,
      scoped_refl _⟩
  | cons item rest ih =>
    obtain ⟨index,width,offset⟩ := item
    have valid := validSteps (index,width,offset) (by simp)
    have offsetPreserved : offset ≠ preserved := notWritten (index,width,offset) (by simp)
    have restValid : ∀ item ∈ rest, item.1.toNat < count.toNat ∧ item.2.2 < 248 :=
      fun item member => validSteps item (by simp [member])
    have restNotWritten : ∀ item ∈ rest, item.2.2 ≠ preserved :=
      fun item member => notWritten item (by simp [member])
    have costEq : ((index,width,offset) :: rest).length * (headerRlpFieldCost inputLimit + 1) =
        (headerRlpFieldCost inputLimit + 1) + rest.length * (headerRlpFieldCost inputLimit + 1) := by
      simp only [List.length_cons,Nat.succ_mul]
      omega
    rw [costEq] at budget ⊢
    change Reaches s (headerBytesStep index width offset (headerBytesChain rest continuation)) _ _ _
    have first := header_bytes_step_content_frame s array count input inputLength scratch frame record ceiling inputLimit
      index width offset (headerBytesChain rest continuation) valid.2 atArray atRecord before recordFits table valid.1
      above fits inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      (by omega)
    refine reaches_trans_budget s _ (headerBytesChain rest continuation) continuation _ _ _ _ (by omega) first ?_
    intro parsed facts restBudget
    obtain ⟨written,locals,writtenDomain,writtenWord,tableParsed,domain,installed,globals,memory⟩ := facts
    have atArrayParsed : parsed.locals.lookup (ofString "arr") = some (.val (.word array)) := by
      rw [locals]
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
    have atRecordParsed : parsed.locals.lookup (ofString "h") = some (.val (.word record)) := by
      rw [locals]
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord
    have natP : (BitVec.ofNat 64 preserved).toNat = preserved :=
      Nat.mod_eq_of_lt (Nat.lt_trans preservedBound (by decide : 248 < 2 ^ 64))
    have natO : (BitVec.ofNat 64 offset).toNat = offset :=
      Nat.mod_eq_of_lt (Nat.lt_trans valid.2 (by decide : 248 < 2 ^ 64))
    have distinct : (record + BitVec.ofNat 64 preserved) ≠ (record + BitVec.ofNat 64 offset) := by
      intro same
      have both := congrArg BitVec.toNat same
      rw [BitVec.toNat_add,BitVec.toNat_add,natP,natO] at both
      have smallP : (record.toNat + preserved) % 2 ^ 64 = record.toNat + preserved :=
        Nat.mod_eq_of_lt (by have h := recordFits; omega)
      have smallO : (record.toNat + offset) % 2 ^ 64 = record.toNat + offset :=
        Nat.mod_eq_of_lt (by have h := recordFits; have v := valid.2; omega)
      rw [smallP,smallO] at both
      have sameOffset : offset = preserved := by omega
      exact offsetPreserved sameOffset
    have storedParsed : parsed.memory (record + BitVec.ofNat 64 preserved) = .word word := by
      rw [memory (record + BitVec.ofNat 64 preserved) preservedAbove distinct]
      exact stored
    have scratchKept : parsed.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) :=
      (globals (ofString "scratch_ptr")).trans scratchGlobal
    have frameKept : parsed.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) :=
      (globals (ofString "frame_mem_ptr")).trans frameGlobal
    have rest := ih parsed restValid restNotWritten storedParsed atArrayParsed atRecordParsed tableParsed
      scratchKept frameKept (installed.trans code) (fun a lo hi => domain ▸ arena a lo hi) restBudget
    have destAbove : ∀ address : BitVec 64, address.toNat < record.toNat →
        address ≠ record + BitVec.ofNat 64 offset := by
      intro address below same
      have fits1 : record.toNat + 248 < 2 ^ 64 := recordFits
      have fits2 : offset < 248 := valid.2
      have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
      have fitsSum : record.toNat + offset < 2 ^ 64 := by omega
      have destNat : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
        rw [BitVec.toNat_add,offsetNat]
        exact Nat.mod_eq_of_lt fitsSum
      rw [same,destNat] at below
      omega
    apply reaches_mono parsed _ continuation _ _ _ _ (le_refl _) _ rest
    intro post kept
    obtain ⟨keptWord,keptFrame⟩ := kept
    refine ⟨keptWord,keptFrame.table,?_,keptFrame.domain.trans domain,keptFrame.code.trans installed,?_,?_⟩
    · intro name different
      rw [keptFrame.locals name different, locals]
      by_cases h : ofString "f" = name
      · exact absurd h.symm different
      · simp [HolFiniteMapExact.lookup_update,FUPDATE,h]
    · intro name
      rw [keptFrame.globals name]
      exact globals name
    · intro address lo hi
      exact (keptFrame.memory address lo hi).trans (memory address lo (destAbove address hi))

#print axioms header_bytes_chain_content_frame
end InitECandidate.Runtime
