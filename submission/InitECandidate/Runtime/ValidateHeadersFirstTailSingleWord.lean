import InitECandidate.Runtime.ValidateHeadersFirstTailNormalFrame
import InitECandidate.Runtime.KeccakFullCallWindow
/-!
The actual tail run keeps one watched memory word.

The tail is the actual sequence `hs[i] = h; keccak256(...); i = i + 1`.  A stored parent
record's root word sits at `record + 32`, which is inside the heap, so the lead's
`[ceiling, hs)` window cannot see it.  This module proves the per-address frame instead:

* the store keeps every word but `hs + i * 8` (`evaluate_wordStore_memory_frame`);
* the real `keccak256` call keeps every word outside `keccak_st`, `keccak_pad` and the
  32-byte output slot (`keccak_full_call_window`), and keeps the globals;
* the increment is a local assignment, so it keeps memory as well.

Nothing about the buffers is asked for an interval: each record root address is checked on its
own with `¬ MWin` on the state, the pad and the output slot, exactly as the user asked.  The
geometric discharge of those three facts and of the store-address separation is
`validate_headers_tail_root_outside`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

private theorem tail_seq_parts {F : Type} {s post : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (run : evaluateHOLFiniteState s (.seq a b) = (none,post)) :
    ∃ mid, evaluateHOLFiniteState s a = (none,mid) ∧ evaluateHOLFiniteState mid b = (none,post) := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases first : evaluateHOLFiniteState s a with
  | mk result mid =>
    rw [first] at run
    cases result with
    | none => exact ⟨mid,rfl,run⟩
    | some r => simp at run

/-- The actual validation tail keeps the watched word and the globals, provided the watched
address is not the pointer store slot and is outside the keccak state, pad and output slot. -/
theorem validate_headers_first_tail_single_word {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count index input inputLength hs hashes header keccakState keccakPad watched : BitVec 64)
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
    (separate : hs + index * 8 ≠ watched)
    (outsideState : ¬ MWin keccakState 200 watched) (outsidePad : ¬ MWin keccakPad 136 watched)
    (outsideOutput : ¬ MWin (hashes + index * 32) 32 watched)
    (run : evaluateHOLFiniteState s validateHeadersFirstTail = (none,post)) :
    post.memory watched = s.memory watched ∧ post.globals = s.globals := by
  rw [source_validate_headers_first_tail] at run
  obtain ⟨stored,storeRun,restRun⟩ := tail_seq_parts run
  obtain ⟨hashed,hashRun,incrementRun⟩ := tail_seq_parts restRun
  obtain ⟨storedTable,storedLocals,storedGlobals,storedDomain,storedCode,_⟩ :=
    validate_headers_header_store_normal_frame s stored array count input inputLength hs index header code atHs
      atIndex atHeader (by omega) table tableBefore storeRun
  have storedWord : stored.memory watched = s.memory watched := by
    have frame := evaluate_wordStore_memory_frame s
      (.op .add [.var .local (ofString "hs"),.panop .mul [.var .local (ofString "i"),.const 8]])
      (.var .local (ofString "h")) (hs + index * 8) watched
      (by simp [evalHOLExact,evalListHOLExact,atHs,atIndex,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord])
      (by intro parsed evaluated; exact ⟨header,by simpa [evalHOLExact,atHeader] using evaluated.symm⟩)
      (fun same => separate same.symm)
    change (evaluateHOLFiniteState s validateHeadersHeaderStore).2.memory _ = _ at frame
    rw [storeRun] at frame
    exact frame
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
    (hashes + index * 32) watched validateHeadersHashArguments
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
  refine ⟨?_,?_⟩
  · rw [postEq]
    change hashed.memory watched = s.memory watched
    exact hashedWord.1.trans storedWord
  · rw [postEq]
    change hashed.globals = s.globals
    exact hashedWord.2.trans storedGlobals

#print axioms validate_headers_first_tail_single_word

/-- The geometry of one stored parent record: when its record starts at or above the live
frontier `frontier`, the pointer buffer and the hash buffer end below that frontier, the keccak
state and pad end below the ceiling, and the ceiling is below the frontier, then the record's
root word is outside the keccak state, the pad, the output slot and the pointer store slot. -/
theorem validate_headers_tail_root_outside {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hs hashes index count keccakState keccakPad record frontier : BitVec 64) (ceiling : Nat)
    (inside : index.toNat < count.toNat)
    (bufferBelow : hs.toNat + count.toNat * 8 ≤ frontier.toNat)
    (hashBelow : hashes.toNat + count.toNat * 32 + 32 ≤ frontier.toNat)
    (recordAbove : frontier.toNat ≤ record.toNat)
    (recordBound : record.toNat + 248 ≤ 33806089496)
    (ceilingBelow : ceiling ≤ frontier.toNat)
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (hashAligned : hashes.toNat % 8 = 0) :
    ¬ MWin keccakState 200 (record + 32#64) ∧ ¬ MWin keccakPad 136 (record + 32#64) ∧
      ¬ MWin (hashes + index * 32) 32 (record + 32#64) ∧ hs + index * 8 ≠ record + 32#64 := by
  have rootAddr : (record + 32#64).toNat = record.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt (by change record.toNat + 32 < 2^64; omega)]
    rfl
  have rootAbove : frontier.toNat ≤ (record + 32#64).toNat := by rw [rootAddr]; omega
  have hashEnd : (hashes + index * 32).toNat + 32 ≤ (record + 32#64).toNat := by
    have productNat : (index * 32).toNat = index.toNat * 32 := by
      rw [BitVec.toNat_mul_of_lt (by change index.toNat * 32 < 2^64; omega)]
      rfl
    rw [rootAddr,BitVec.toNat_add_of_lt (by
      have : hashes.toNat < 2^64 := hashes.isLt
      omega)]
    rw [productNat]
    omega
  have storeBelow : (hs + index * 8).toNat < (record + 32#64).toNat := by
    have productNat : (index * 8).toNat = index.toNat * 8 := by
      rw [BitVec.toNat_mul_of_lt (by change index.toNat * 8 < 2^64; omega)]
      rfl
    rw [rootAddr,BitVec.toNat_add_of_lt (by
      have : hs.toNat < 2^64 := hs.isLt
      omega)]
    rw [productNat]
    omega
  refine ⟨mwin_below (D := keccakState) (N := 200) (w := record + 32#64) (by rw [rootAddr]; omega),
    mwin_below (D := keccakPad) (N := 136) (w := record + 32#64) (by rw [rootAddr]; omega),
    mwin_below (D := hashes + index * 32) (N := 32) (w := record + 32#64) hashEnd,?_⟩
  intro same
  have storeAddr : (hs + index * 8).toNat = hs.toNat + index.toNat * 8 := by
    have productNat : (index * 8).toNat = index.toNat * 8 := by
      rw [BitVec.toNat_mul_of_lt (by change index.toNat * 8 < 2^64; omega)]
      rfl
    rw [BitVec.toNat_add_of_lt (by rw [productNat]; have : hs.toNat < 2^64 := hs.isLt; omega),productNat]
  have levels := congrArg BitVec.toNat same
  rw [storeAddr,rootAddr] at levels
  omega

#print axioms validate_headers_tail_root_outside
end InitECandidate.Runtime
