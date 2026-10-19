import InitECandidate.Runtime.ValidateHeadersFirstTailSource
import InitECandidate.Runtime.KeccakFullCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_validate_headers_hash_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength hashes : BitVec 64)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength) :
    evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) validateHeadersHashArguments =
      some [.val (.word pointer),.val (.word length),.val (.word (hashes + index * 32))] := by
  have sourceDomain := entry.readable.pointerDomain
  have sizeDomain := entry.readable.lengthDomain
  have sourceCell := entry.readable.pointerCell
  have sizeCell := entry.readable.lengthCell
  rw [evalListHOLFinite_eq_toExact]
  simp [validateHeadersHashArguments,validateHeadersDecodeArguments,headerRlpFieldArguments,validateHeadersHashOutput,
    evalListHOLExact,evalHOLExact,atArray,atIndex,atHashes,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,sourceDomain,sizeDomain,sourceCell,sizeCell]
  have sizeDomainRight : s.memaddrs (array + (index * (16#64) + (8#64))) := by
    simpa only [BitVec.add_assoc] using sizeDomain
  simp [sourceDomain,sizeDomainRight,sourceCell,sizeCell,← BitVec.add_assoc]
  rw [if_pos sizeDomainRight]

/-- The actual loop hash call is bounded by the original input limit, using
its real readable witness slice and aligned output slot. -/
theorem runBounded_validate_headers_hash_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength hashes keccakState keccakPad : BitVec 64) (inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit ≤ 134217712)
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (outputAligned : (hashes + index * 32).toNat % 8 = 0) (code : s.code = originalRuntimeCode)
    (budget : inputLimit * 20 + 125 ≤ s.clock) :
    RunBounded s validateHeadersHashCall (inputLimit * 20 + 125) := by
  have lengthBound := (entry.length_bound s array index pointer length input inputLength).trans inputBound
  have args := eval_validate_headers_hash_arguments s array index pointer length input inputLength hashes atArray atIndex atHashes entry
  exact (runBounded_keccak_full_call s keccakState keccakPad pointer length (hashes + index * 32) none validateHeadersHashArguments
    stateGlobal padGlobal args (by omega) outputAligned code (by omega)).weaken (by omega)

#print axioms eval_validate_headers_hash_arguments
#print axioms runBounded_validate_headers_hash_call
end InitECandidate.Runtime
