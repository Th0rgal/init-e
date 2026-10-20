import InitECandidate.Runtime.ValidateHeadersFirstTailNormalFrame
import InitECandidate.Runtime.KeccakFullCallWindow
import InitECandidate.Runtime.ValidateHeadersStoreContent
/-!
The actual validation tail leaves the decoded record in the pointer buffer.

The component `ValidateHeadersStoredRoots` reads slot `i` back on the next iteration, so the tail
must not only keep the older cells, it must *write* the current record there and keep it while it
runs `keccak256` and the increment.  The tail is the actual sequence
`hs[i] = h; keccak256(...); i = i + 1`:

* the store writes the record pointer to `hs + i * 8` (`validate_headers_store_content`);
* the real `keccak256` call keeps every word outside `keccak_st`, `keccak_pad` and the 32-byte
  output slot (`keccak_full_call_window`), and the store target is outside all three because it
  sits above the state and pad and below the output slot
  (`validate_headers_tail_store_outside`);
* the increment is a local assignment, so it keeps memory.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

private theorem store_cell_seq_parts {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.seq a b) = (none,post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none,mid) ∧ evaluateHOLFiniteState mid b = (none,post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases first : evaluateHOLFiniteState s a with
  | mk result mid =>
    rw [first] at run
    cases result with
    | none => exact ⟨mid,rfl,run⟩
    | some r => simp at run

/-- The actual validation tail stores the decoded parent record at `hs + i * 8` and leaves it
there, provided the store target is outside the keccak state, pad and output windows. -/
theorem validate_headers_first_tail_store_cell {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count index input inputLength hs hashes header keccakState keccakPad : BitVec 64)
    (inputLimit ceiling : Nat)
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
    (outsideState : ¬ MWin keccakState 200 (hs + index * (8#64)))
    (outsidePad : ¬ MWin keccakPad 136 (hs + index * (8#64)))
    (outsideOutput : ¬ MWin (hashes + index * 32) 32 (hs + index * (8#64)))
    (run : evaluateHOLFiniteState s validateHeadersFirstTail = (none,post)) :
    post.memory (hs + index * (8#64)) = .word header := by
  rw [source_validate_headers_first_tail] at run
  obtain ⟨stored,storeRun,restRun⟩ := store_cell_seq_parts run
  obtain ⟨hashed,hashRun,incrementRun⟩ := store_cell_seq_parts restRun
  obtain ⟨storedTable,storedLocals,storedGlobals,storedDomain,storedCode,_⟩ :=
    validate_headers_header_store_normal_frame s stored array count input inputLength hs index header code atHs
      atIndex atHeader (by omega) table tableBefore storeRun
  obtain ⟨cellDomain,cellContent⟩ :=
    validate_headers_store_content s stored hs index header atHs atIndex atHeader storeRun
  have storeBound := RunBounded.ofProg (ProgBounded.straight validateHeadersHeaderStore rfl) code
    (by omega : 0 ≤ s.clock)
  have storeClock : s.clock ≤ stored.clock := by
    have spent := storeBound.1
    rw [storeRun] at spent
    simpa using spent
  obtain ⟨pointer,length,entry⟩ := storedTable index inside
  have lengthBound : length.toNat ≤ inputLimit :=
    (entry.length_bound stored array index pointer length input inputLength).trans inputBound
  have args := eval_validate_headers_hash_arguments stored array index pointer length input inputLength hashes
    (by rw [storedLocals]; exact atArray) (by rw [storedLocals]; exact atIndex)
    (by rw [storedLocals]; exact atHashes) entry
  have hashedWord := keccak_full_call_window stored keccakState keccakPad pointer length
    (hashes + index * 32) (hs + index * (8#64)) validateHeadersHashArguments
    (by rw [storedGlobals]; exact stateGlobal) (by rw [storedGlobals]; exact padGlobal) args
    (by omega)
    (storedCode.trans code) (by omega) outsideState outsidePad outsideOutput
  have hTwo : (evaluateHOLFiniteState stored (.call (some (none,none)) (ofString "keccak256")
      validateHeadersHashArguments)).2 = hashed := by
    simpa only [validateHeadersHashCall] using (congrArg Prod.snd hashRun)
  rw [hTwo] at hashedWord
  have hashedLocals : hashed.locals = stored.locals := by
    have locals := evaluate_discard_call_success_locals stored (ofString "keccak256") validateHeadersHashArguments
      (by change (evaluateHOLFiniteState stored validateHeadersHashCall).1 = none; rw [hashRun])
    change (evaluateHOLFiniteState stored validateHeadersHashCall).2.locals = stored.locals at locals
    rw [hashRun] at locals
    exact locals
  have increase := evaluate_validate_headers_increment hashed index (by rw [hashedLocals,storedLocals]; exact atIndex)
  rw [incrementRun] at increase
  have postEq := (Prod.mk.inj increase).2
  rw [postEq]
  change hashed.memory (hs + index * (8#64)) = .word header
  exact hashedWord.1.trans cellContent

#print axioms validate_headers_first_tail_store_cell
end InitECandidate.Runtime
