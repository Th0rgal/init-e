import InitECandidate.Runtime.HeaderWordFieldChainReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def decodeHeaderEarlyWords : List (BitVec 64 × Nat) :=
  [(9,104),(10,112)]

theorem source_decode_header_early_words : decodeHeaderAt 27 =
    headerWordFieldChain decodeHeaderEarlyWords (decodeHeaderAt 31) := rfl

/-- The actual two word-field assignments and stores reach the timestamp
parser within two uniform numeric-field budgets, retaining the real slice table. -/
theorem decode_header_early_words_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (countBound : 11 ≤ count.toNat)
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
    (budget : 2 * (headerRlpFieldCost inputLimit + 35) ≤ s.clock) :
    Reaches s (decodeHeaderAt 27)
      (fun post => HeaderWordFieldFrame s post array count input inputLength record ceiling)
      (2 * (headerRlpFieldCost inputLimit + 35)) (decodeHeaderAt 31) := by
  rw [source_decode_header_early_words]
  have valid : ∀ item ∈ decodeHeaderEarlyWords, item.1.toNat < count.toNat ∧ item.2 < 248 := by
    intro item member
    simp only [decodeHeaderEarlyWords,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp <;> omega
  exact header_word_field_chain_reaches s array count input inputLength scratch frame record ceiling inputLimit
    decodeHeaderEarlyWords (decodeHeaderAt 31) valid atArray atRecord before recordFits table above fits inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget

#print axioms source_decode_header_early_words
#print axioms decode_header_early_words_reaches
end InitECandidate.Runtime
