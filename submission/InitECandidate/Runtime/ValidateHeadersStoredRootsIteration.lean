import InitECandidate.Runtime.ValidateHeadersStoredRootsStep
import InitECandidate.Runtime.ValidateHeadersStoredRootsGeometry
/-!
The actual validation tail keeps the stored parent records, with the separation derived.

`validate_headers_first_tail_stored_roots_geometry` is the composed iteration step: it takes the
tail's own premises, derives the per-address separation with
`validate_headers_stored_roots_separation` (pointer buffer cells) and
`validate_headers_stored_root_separation` (record root words), and concludes that the actual tail
run keeps `ValidateHeadersStoredRoots` for every slot below the index.  The two separation lemmas
do the whole job; no per-address callback is left in the statement - only the concrete layout
(`hs + count * 8 ≤ hashes` for the pointer buffer, `keccakState + 200`, `keccakPad + 136 ≤ hs` for
the workspace) and the live frontier bound.  The floor of every stored record is the hash
buffer's end `hashes + count * 32 + 32`, which is the same number in every iteration.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- One actual validation tail keeps every stored parent record, with the separation of each
stored cell and each root word derived from the concrete buffer layout. -/
theorem validate_headers_first_tail_stored_roots_geometry {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (array count index input inputLength hs hashes header keccakState keccakPad : BitVec 64)
    (inputLimit ceiling filled frontier : Nat)
    (roots : ValidateHeadersStoredRoots s hs filled frontier (hashes.toNat + count.toNat * 32 + 32))
    (domain : post.memaddrs = s.memaddrs)
    (inside : index.toNat < count.toNat) (slotBound : filled ≤ count.toNat)
    (older : filled ≤ index.toNat)
    (bufferBeforeHashes : hs.toNat + count.toNat * 8 ≤ hashes.toNat)
    (stateBeforeHs : keccakState.toNat + 200 ≤ hs.toNat)
    (padBeforeHs : keccakPad.toNat + 136 ≤ hs.toNat)
    (hsBufferBound : hs.toNat + count.toNat * 8 + 8 ≤ 33806089496)
    (hashBufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496)
    (hashAligned : hashes.toNat % 8 = 0)
    (frontierBound : frontier ≤ 33806089496)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (atHs : s.locals.lookup (ofString "hs") = some (.val (.word hs)))
    (atHashes : s.locals.lookup (ofString "hashes") = some (.val (.word hashes)))
    (atHeader : s.locals.lookup (ofString "h") = some (.val (.word header)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (tableBefore : array.toNat + count.toNat * 16 ≤ hs.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit ≤ 134217712)
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (code : s.code = originalRuntimeCode) (budget : inputLimit * 20 + 125 ≤ s.clock)
    (tableAbove : ceiling ≤ array.toNat) (hsBeforeHashes : hs.toNat ≤ hashes.toNat)
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (run : evaluateHOLFiniteState s validateHeadersFirstTail = (none,post)) :
    ValidateHeadersStoredRoots post hs filled frontier (hashes.toNat + count.toNat * 32 + 32) := by
  have stateBelowFloor : keccakState.toNat + 200 ≤ hashes.toNat + count.toNat * 32 + 32 := by omega
  have padBelowFloor : keccakPad.toNat + 136 ≤ hashes.toNat + count.toNat * 32 + 32 := by omega
  refine validate_headers_first_tail_stored_roots s post array count index input inputLength hs
    hashes header keccakState keccakPad inputLimit ceiling filled frontier
    (hashes.toNat + count.toNat * 32 + 32) roots domain older ?_ ?_ atArray atIndex atHs atHashes
    atHeader inside table tableBefore hsBufferBound hashBufferBound hashAligned inputBound limitBound
    stateGlobal padGlobal code budget tableAbove hsBeforeHashes stateBelow padBelow run
  · intro slot within
    exact validate_headers_stored_roots_separation s hs hashes index count keccakState keccakPad
      filled inside bufferBeforeHashes stateBeforeHs padBeforeHs hsBufferBound hashAligned
      hashBufferBound slot within slotBound older
  · intro slot within prior cell
    obtain ⟨record,word,cellKept,rootKept,rootHere,extent,above⟩ := roots slot within
    have sameRecord : prior = record := by
      exact HolWordLab.word.inj (cell.symm.trans cellKept)
    subst prior
    exact validate_headers_stored_root_separation (F := F) hs hashes index count keccakState keccakPad
      record frontier inside above extent frontierBound stateBelowFloor padBelowFloor bufferBeforeHashes
      hashBufferBound

#print axioms validate_headers_first_tail_stored_roots_geometry
end InitECandidate.Runtime
