import InitECandidate.Runtime.DecodeHeaderEarlyBytesReach
import InitECandidate.Runtime.HeaderBytesChainContentFrame
/-!
The actual decoder tail after the state root store keeps that word.

The frozen body stores the 32-byte state root word at record offset 32 as the third
field of the early bytes chain and then decodes the four following fields at offsets
40, 48 and 56.  None of those assignments touches offset 32, so the actual program
fragment after the store still returns the state root word, readable, at
`record + 32`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual fields decoded after the state root, at their record offsets. -/
def decodeHeaderAfterStateRoot : List (BitVec 64 × BitVec 64 × Nat) :=
  [(4#64,32#64,40),(5#64,32#64,48),(6#64,256#64,56)]

theorem source_decode_header_after_state_root :
    decodeHeaderAfterStateRoot = [(4#64,32#64,40),(5#64,32#64,48),(6#64,256#64,56)] := rfl

/-- Starting once the state root word is readable at `record + 32`, the actual
remaining field assignments of the early bytes chain keep it there. -/
theorem decode_header_state_root_suffix_preserved {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (word : BitVec 64) (countBound : 7 ≤ count.toNat)
    (stored : s.memory (record + BitVec.ofNat 64 32) = .word word)
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
    (budget : decodeHeaderAfterStateRoot.length * (headerRlpFieldCost inputLimit + 1) ≤ s.clock) :
    Reaches s (headerBytesChain decodeHeaderAfterStateRoot (decodeHeaderAt 23))
      (fun post => post.memory (record + BitVec.ofNat 64 32) = .word word ∧
        HeaderBytesFrame s post array count input inputLength record ceiling)
      (decodeHeaderAfterStateRoot.length * (headerRlpFieldCost inputLimit + 1)) (decodeHeaderAt 23) := by
  have valid : ∀ item ∈ decodeHeaderAfterStateRoot,
      item.1.toNat < count.toNat ∧ item.2.2 < 248 := by
    intro item member
    obtain ⟨index,width,offset⟩ := item
    have facts : index.toNat ≤ 6 ∧ offset < 248 := by
      simp only [decodeHeaderAfterStateRoot,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> decide
    obtain ⟨small,off⟩ := facts
    exact ⟨Nat.lt_of_le_of_lt small (Nat.lt_of_lt_of_le (by decide : 6 < 7) countBound),off⟩
  have notWritten : ∀ item ∈ decodeHeaderAfterStateRoot, item.2.2 ≠ 32 := by
    intro item member
    obtain ⟨index,width,offset⟩ := item
    have different : offset ≠ 32 := by
      simp only [decodeHeaderAfterStateRoot,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ | ⟨_,_,rfl⟩ <;> decide
    exact different
  have offsetNat : (BitVec.ofNat 64 32).toNat = 32 := Nat.mod_eq_of_lt (by decide)
  have sumNat : (record + BitVec.ofNat 64 32).toNat = record.toNat + 32 := by
    rw [BitVec.toNat_add,offsetNat]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have preservedAbove : ceiling ≤ (record + BitVec.ofNat 64 32).toNat := by
    rw [sumNat]
    have := above
    omega
  refine reaches_mono s _ (decodeHeaderAt 23) _ _ _ _ (le_refl _) ?_ (header_bytes_chain_content_frame s array
    count input inputLength scratch frame record ceiling inputLimit decodeHeaderAfterStateRoot (decodeHeaderAt 23)
    32 word valid notWritten preservedAbove (by decide) stored atArray atRecord before recordFits table above fits
    inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget)
  intro post kept
  obtain ⟨keptWord,keptFrame⟩ := kept
  exact ⟨keptWord,keptFrame⟩

#print axioms source_decode_header_after_state_root
#print axioms decode_header_state_root_suffix_preserved
end InitECandidate.Runtime
