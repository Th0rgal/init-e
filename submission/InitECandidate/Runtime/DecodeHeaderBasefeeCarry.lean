import InitECandidate.Runtime.DecodeHeaderBasefeeContentFrame
/-!
The actual base-fee phase carries the whole decoder context.

`decode_header_basefee_content_frame` already keeps the readable slice table and the
parser's locals frame, and it keeps every word at or above the ceiling outside the four
limb destinations at offsets 160 to 184.  The state root at record offset 32 is one of
those words, so the phase `decodeHeaderAt 42 -> 44` also delivers the `arr`/`h` locals
and the state root word that the uniform carry predicate of the header decoder needs.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual base-fee phase `decodeHeaderAt 42 -> 44` keeps the state root word at
record offset 32 together with the readable slice table and the decoder's `arr`/`h`
locals. -/
theorem decode_header_basefee_ready {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record word : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (before : array.toNat + count.toNat * 16 ≤ record.toNat)
    (recordFits : record.toNat + 248 < 2^64)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (countBound : 16 ≤ count.toNat) (above : ceiling ≤ array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 35 ≤ s.clock)
    (stored : s.memory (record + 32#64) = .word word) :
    Reaches s (decodeHeaderAt 42)
      (fun ready => ready.memory (record + 32#64) = .word word ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        ready.locals.lookup (ofString "h") = some (.val (.word record)))
      (headerRlpFieldCost inputLimit + 35) (decodeHeaderAt 44) := by
  have targetNat : (BitVec.ofNat 64 32).toNat = 32 := Nat.mod_eq_of_lt (by decide)
  have rootSum : (record + BitVec.ofNat 64 32).toNat = record.toNat + 32 := by
    rw [BitVec.toNat_add,targetNat]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have hundredSixtyNat : (BitVec.ofNat 64 160).toNat = 160 := Nat.mod_eq_of_lt (by decide)
  have destinationSum : (record + BitVec.ofNat 64 160).toNat = record.toNat + 160 := by
    rw [BitVec.toNat_add,hundredSixtyNat]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have sourceSum (k : BitVec 64) (small : k.toNat ≤ 24) :
      ((record + BitVec.ofNat 64 160) + k).toNat = record.toNat + 160 + k.toNat := by
    rw [BitVec.toNat_add,destinationSum]
    exact Nat.mod_eq_of_lt (by have h := recordFits; omega)
  have apart (k : BitVec 64) (small : k.toNat ≤ 24) :
      record + BitVec.ofNat 64 32 ≠ (record + BitVec.ofNat 64 160) + k := by
    intro same
    have both := congrArg BitVec.toNat same
    rw [rootSum,sourceSum k small] at both
    omega
  have zeroApart : record + BitVec.ofNat 64 32 ≠ record + BitVec.ofNat 64 160 := by
    intro same
    have both := congrArg BitVec.toNat same
    rw [rootSum,destinationSum] at both
    omega
  have rootAbove : ceiling ≤ (record + BitVec.ofNat 64 32).toNat := by
    rw [rootSum]
    omega
  apply reaches_mono s (decodeHeaderAt 42) (decodeHeaderAt 44) _ _
    (headerRlpFieldCost inputLimit + 35) (headerRlpFieldCost inputLimit + 35) (le_refl _) ?_
    (decode_header_basefee_content_frame s array count input inputLength scratch frame record ceiling inputLimit
      atArray atRecord before recordFits table countBound above fits inputBound limitBound scratchGlobal frameGlobal
      code orderedFrame framePositive scratchBelow arena budget)
  intro ready facts
  obtain ⟨first,second,third,fourth,locals,tableReady,domain,installed,globals,memory⟩ := facts
  refine ⟨?_,domain,installed,globals,tableReady,?_,?_⟩
  · rw [memory (record + 32#64) rootAbove zeroApart (apart (8#64) (by decide))
      (apart (16#64) (by decide)) (apart (24#64) (by decide))]
    exact stored
  · rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
  · rw [locals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atRecord

#print axioms decode_header_basefee_ready
end InitECandidate.Runtime
