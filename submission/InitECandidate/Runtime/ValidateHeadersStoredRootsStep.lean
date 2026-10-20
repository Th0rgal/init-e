import InitECandidate.Runtime.ValidateHeadersStoredRoots
import InitECandidate.Runtime.ValidateHeadersFirstTailSingleWord
/-!
One actual validation iteration keeps every already-stored parent record.

Step 1 of the extended iteration: the real tail (`hs[i] = h; keccak256(...); i = i + 1`) keeps
`ValidateHeadersStoredRoots` for the slots below the current index.  Each old slot is handled
with the checked single-word tail frame `validate_headers_first_tail_single_word`: its stored
pointer cell `hs + slot * 8` and its root cell `header + 32` are each watched on their own, with
`¬ MWin` on the keccak state, the pad and the hash output slot.  The `separated` premise is
where geometry enters - it is the per-record separation from the record's own allocation lower
bound, so the moving live frontier is never used to separate old records from the buffers.

Step 2 (`validateHeadersStoredRoots_store`, already checked) extends the component with the
new record that `parent_record_carry` returns for this iteration.

`domain` is the memory domain of the tail run, which
`validate_headers_first_tail_normal_frame` provides together with the locals update.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- The actual validation tail keeps every stored parent record below the current index. -/
theorem validate_headers_first_tail_stored_roots {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count index input inputLength hs hashes header keccakState keccakPad : BitVec 64)
    (inputLimit ceiling filled frontier floor : Nat)
    (roots : ValidateHeadersStoredRoots s hs filled frontier floor)
    (domain : post.memaddrs = s.memaddrs)
    (older : filled ≤ index.toNat)
    (cellSeparated : ∀ slot : BitVec 64, slot.toNat < filled →
      (hs + index * 8 ≠ hs + slot * (8#64) ∧ ¬ MWin keccakState 200 (hs + slot * (8#64)) ∧
        ¬ MWin keccakPad 136 (hs + slot * (8#64)) ∧
        ¬ MWin (hashes + index * 32) 32 (hs + slot * (8#64))))
    (separated : ∀ slot : BitVec 64, slot.toNat < filled → ∀ prior : BitVec 64,
      s.memory (hs + slot * (8#64)) = .word prior →
      (hs + index * 8 ≠ prior + 32#64 ∧ ¬ MWin keccakState 200 (prior + 32#64) ∧
        ¬ MWin keccakPad 136 (prior + 32#64) ∧
        ¬ MWin (hashes + index * 32) 32 (prior + 32#64)))
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
    (run : evaluateHOLFiniteState s validateHeadersFirstTail = (none,post)) :
    ValidateHeadersStoredRoots post hs filled frontier floor := by
  have frame : ∀ watched : BitVec 64, watched ≠ hs + index * 8 →
      ¬ MWin keccakState 200 watched → ¬ MWin keccakPad 136 watched →
      ¬ MWin (hashes + index * 32) 32 watched → post.memory watched = s.memory watched := by
    intro watched separate stateOutside padOutside outputOutside
    exact (validate_headers_first_tail_single_word s post array count index input inputLength hs
      hashes header keccakState keccakPad watched inputLimit ceiling atArray atIndex atHs atHashes
      atHeader inside table tableBefore hsBufferBound hashBufferBound hashAligned inputBound
      limitBound stateGlobal padGlobal code budget tableAbove hsBeforeHashes stateBelow padBelow
      (fun same => separate same.symm) stateOutside padOutside outputOutside run).1
  intro slot within
  obtain ⟨prior,root,cell,rootCell,rootDomain,extent,above⟩ := roots slot within
  obtain ⟨cellSeparate,cellState,cellPad,cellOutput⟩ := cellSeparated slot within
  obtain ⟨separate,stateOutside,padOutside,outputOutside⟩ := separated slot within prior cell
  refine ⟨prior,root,?_,?_,?_,extent,above⟩
  · exact (frame _ (fun same => cellSeparate same.symm) cellState cellPad cellOutput).trans cell
  · exact (frame _ (fun same => separate same.symm) stateOutside padOutside outputOutside).trans rootCell
  · rw [domain]; exact rootDomain

#print axioms validate_headers_first_tail_stored_roots
end InitECandidate.Runtime
