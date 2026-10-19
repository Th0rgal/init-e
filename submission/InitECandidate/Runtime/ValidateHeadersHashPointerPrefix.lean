import InitECandidate.Runtime.ValidateHeadersHashNormalFrame
import InitECandidate.Runtime.HeaderPointerPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The actual successful hash call preserves the initialized header-pointer buffer
when the buffer lies in its proved untouched window. -/
theorem validate_headers_hash_pointer_prefix {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count index pointer length input inputLength hashes keccakState keccakPad upper : BitVec 64) (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (inside : index.toNat < count.toNat)
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (above : ceiling ≤ array.toNat) (before : array.toNat + count.toNat * 16 ≤ upper.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit ≤ 134217712)
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (code : s.code = originalRuntimeCode) (budget : inputLimit * 20 + 125 ≤ s.clock)
    (outsideState : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → ¬ MWin keccakState 200 address)
    (outsidePad : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → ¬ MWin keccakPad 136 address)
    (outsideOutput : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat → ¬ MWin (hashes + index * 32) 32 address)
    (run : evaluateHOLFiniteState s validateHeadersHashCall = (none,post))
    (hs : BitVec 64) (initialized : HeaderPointerPrefix s hs (index.toNat + 1))
    (bufferAbove : ceiling ≤ hs.toNat)
    (bufferBefore : hs.toNat + (index.toNat + 1) * 8 ≤ upper.toNat) :
    HeaderPointerPrefix post hs (index.toNat + 1) := by
  obtain ⟨_,_,_,domain,_,memory⟩ := validate_headers_hash_normal_frame s post array count index pointer length
    input inputLength hashes keccakState keccakPad upper ceiling inputLimit atArray atIndex atHashes inside
    entry table above before inputBound limitBound stateGlobal padGlobal code budget outsideState outsidePad outsideOutput run
  apply initialized.after_frame s post hs (index.toNat + 1) domain
  intro slot small
  have top := upper.isLt
  have mulNat : (slot * (8#64)).toNat = slot.toNat * 8 := by
    rw [BitVec.toNat_mul_of_lt (by change slot.toNat * 8 < 2^64; omega)]
    rfl
  have addrNat : (hs + slot * (8#64)).toNat = hs.toNat + slot.toNat * 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [mulNat]; omega),mulNat]
  exact memory _ (by rw [addrNat]; omega) (by rw [addrNat]; omega)

#print axioms validate_headers_hash_pointer_prefix
end InitECandidate.Runtime
