import InitECandidate.Runtime.ValidateHeadersHeaderStoreReach
import InitECandidate.Runtime.ValidateHeadersHashGeometry
import InitECandidate.Runtime.ValidateHeadersIncrement
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- The complete actual post-decode iteration tail (header pointer store,
Keccak call and increment) is bounded using the real retained witness table. -/
theorem runBounded_validate_headers_first_tail {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count index input inputLength hs hashes header keccakState keccakPad : BitVec 64) (inputLimit : Nat)
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
    (code : s.code = originalRuntimeCode) (budget : inputLimit * 20 + 125 ≤ s.clock) :
    RunBounded s validateHeadersFirstTail (inputLimit * 20 + 125) := by
  have stored := validate_headers_header_store_reaches s array count input inputLength hs index header
    (.seq validateHeadersHashCall validateHeadersIncrement) code atHs atIndex atHeader (by omega) table tableBefore
  rw [source_validate_headers_first_tail]
  rw [← Nat.zero_add (inputLimit * 20 + 125)]
  apply RunBounded.ofReaches (prefixCost := 0) (tailCost := inputLimit * 20 + 125) (by omega) stored
  intro next facts remaining
  obtain ⟨tableNext,locals,globals,domain,installed,memory⟩ := facts
  obtain ⟨pointer,length,entry⟩ := tableNext index inside
  have atArrayNext : next.locals.lookup (ofString "arr") = some (.val (.word array)) := by rw [locals]; exact atArray
  have atIndexNext : next.locals.lookup (ofString "i") = some (.val (.word index)) := by rw [locals]; exact atIndex
  have atHashesNext : next.locals.lookup (ofString "hashes") = some (.val (.word hashes)) := by rw [locals]; exact atHashes
  have stateNext : next.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)) := by rw [globals]; exact stateGlobal
  have padNext : next.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)) := by rw [globals]; exact padGlobal
  have productNat : (index * 32).toNat = index.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change index.toNat * 32 < 2^64; omega)]
    rfl
  have outputNat : (hashes + index * 32).toNat = hashes.toNat + index.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [productNat]; omega),productNat]
  have outputAligned : (hashes + index * 32).toNat % 8 = 0 := by
    rw [outputNat]
    simp [Nat.add_mod,Nat.mul_mod,hashAligned]
  have hashBound := runBounded_validate_headers_hash_call next array index pointer length input inputLength hashes keccakState keccakPad inputLimit
    atArrayNext atIndexNext atHashesNext entry inputBound limitBound stateNext padNext outputAligned (installed.trans code) remaining
  apply RunBounded.seq (a := inputLimit * 20 + 125) (b := 0) hashBound (by omega)
  intro hashed normal codeKept rest
  exact RunBounded.ofProg (ProgBounded.straight _ rfl) (codeKept.trans (installed.trans code)) (by omega)

#print axioms runBounded_validate_headers_first_tail
end InitECandidate.Runtime
