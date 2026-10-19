import InitECandidate.Runtime.ValidateHeadersFirstTailBound
import InitECandidate.Runtime.ValidateHeadersStoreNormalFrame
import InitECandidate.Runtime.ValidateHeadersHashPointerPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem validation_seq_normal_parts {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.seq a b) = (none,post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none,mid) ∧ evaluateHOLFiniteState mid b = (none,post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases first : evaluateHOLFiniteState s a with
  | mk result mid =>
    rw [first] at run
    cases result with
    | none => exact ⟨mid,rfl,run⟩
    | some r => simp at run

/-- The actual store/hash/increment tail extends the initialized pointer buffer.
The full pointer buffer lies before the hash output region. -/
theorem validate_headers_first_tail_pointer_prefix {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count index input inputLength hs hashes header keccakState keccakPad : BitVec 64) (inputLimit ceiling : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (atHeader : s.locals.lookup (ofString "h") = some (.val (.word header)))
    (inside : index.toNat < count.toNat)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (tableBefore : array.toNat + count.toNat * 16 ≤ hs.toNat)
    (hsBufferBound : hs.toNat + count.toNat * 8 + 8 ≤ 33806089496)
    (hashBufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496)
    (hashAligned : hashes.toNat % 8 = 0)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit ≤ 134217712)
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (code : s.code = originalRuntimeCode) (budget : inputLimit * 20 + 125 ≤ s.clock)
    (tableAbove : ceiling ≤ array.toNat) (hsBeforeHashes : hs.toNat ≤ hashes.toNat)
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (initialized : HeaderPointerPrefix s hs index.toNat)
    (hsAbove : ceiling ≤ hs.toNat)
    (bufferBeforeHashes : hs.toNat + count.toNat * 8 ≤ hashes.toNat)
    (run : evaluateHOLFiniteState s validateHeadersFirstTail = (none,post)) :
    HeaderPointerPrefix post hs (index.toNat + 1) := by
  rw [source_validate_headers_first_tail] at run
  obtain ⟨stored,storeRun,restRun⟩ := validation_seq_normal_parts run
  obtain ⟨hashed,hashRun,incrementRun⟩ := validation_seq_normal_parts restRun
  obtain ⟨storedTable,storedLocals,storedGlobals,storedDomain,storedCode,storedMemory⟩ :=
    validate_headers_header_store_normal_frame s stored array count input inputLength hs index header code atHs atIndex atHeader (by omega) table tableBefore storeRun
  have storeBound := RunBounded.ofProg (ProgBounded.straight validateHeadersHeaderStore rfl) code (by omega : 0 ≤ s.clock)
  have storeClock : s.clock ≤ stored.clock := by
    have spent := storeBound.1
    rw [storeRun] at spent
    simpa using spent
  obtain ⟨pointer,length,entry⟩ := storedTable index inside
  have geometry := validate_headers_hash_geometry hashes index count keccakState keccakPad hs ceiling inside hashBufferBound hashAligned stateBelow padBelow hsBeforeHashes
  obtain ⟨hashedTable,hashedLocals,hashedGlobals,hashedDomain,hashedCode,hashedMemory⟩ :=
    validate_headers_hash_normal_frame stored hashed array count index pointer length input inputLength hashes keccakState keccakPad hs ceiling inputLimit
      (by rw [storedLocals]; exact atArray) (by rw [storedLocals]; exact atIndex) (by rw [storedLocals]; exact atHashes)
      inside entry storedTable tableAbove tableBefore inputBound limitBound
      (by rw [storedGlobals]; exact stateGlobal) (by rw [storedGlobals]; exact padGlobal)
      (storedCode.trans code) (by omega)
      (fun address lo hi => (geometry.2.2 address lo hi).1)
      (fun address lo hi => (geometry.2.2 address lo hi).2.1)
      (fun address lo hi => (geometry.2.2 address lo hi).2.2) hashRun
  have increment := evaluate_validate_headers_increment hashed index (by rw [hashedLocals,storedLocals]; exact atIndex)
  rw [incrementRun] at increment
  have postEq := (Prod.mk.inj increment).2
  have storedPrefix := headerPointerPrefix_store s stored hs index header initialized (by omega)
    atHs atIndex atHeader storeRun
  have geometryFull := validate_headers_hash_geometry hashes index count keccakState keccakPad hashes ceiling
    inside hashBufferBound hashAligned stateBelow padBelow (le_refl _)
  have hashedPrefix := validate_headers_hash_pointer_prefix stored hashed array count index pointer length
    input inputLength hashes keccakState keccakPad hashes ceiling inputLimit
    (by rw [storedLocals]; exact atArray) (by rw [storedLocals]; exact atIndex)
    (by rw [storedLocals]; exact atHashes) inside entry storedTable tableAbove (by omega) inputBound limitBound
    (by rw [storedGlobals]; exact stateGlobal) (by rw [storedGlobals]; exact padGlobal)
    (storedCode.trans code) (by omega)
    (fun address lo hi => (geometryFull.2.2 address lo hi).1)
    (fun address lo hi => (geometryFull.2.2 address lo hi).2.1)
    (fun address lo hi => (geometryFull.2.2 address lo hi).2.2) hashRun hs storedPrefix hsAbove (by omega)
  rw [postEq]
  exact hashedPrefix.after_frame hashed _ hs (index.toNat + 1) rfl (fun _ _ => rfl)

#print axioms validate_headers_first_tail_pointer_prefix
end InitECandidate.Runtime
