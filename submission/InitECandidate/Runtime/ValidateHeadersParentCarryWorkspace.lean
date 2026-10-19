import InitECandidate.Runtime.ValidateHeadersParentReaches
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
import InitECandidate.Runtime.WorkspaceGlobalsKeep
/-!
What the loop's decode call leaves available to the continuation besides the record.

`parentRecordCarry` pins the returned record, its generated state root word, the memory domain,
the code, the frame globals and the words of `[ceiling, heapStart)`.  The validation tail that
runs inside the same call also reads the caller's locals (`arr`, `i`, `hs`, `hashes`, and the
bound `h`), the two keccak workspace globals and the slice-witness table.  None of these are
assumed here: the locals and the table are restored by the frozen call semantics, so they are
derived, and the workspace globals are derived from the checked keeps-analysis of the installed
header decoder body.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- A slice-witness table survives any run that keeps the domain and the words of one window
containing the whole table.  This is the transport the actual header-decode call supports: it
reports its memory outside the region it allocates. -/
theorem RlpSliceInputPrefix.after_window {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count input inputLength heap : BitVec 64) (ceiling : Nat)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (domain : post.memaddrs = state.memaddrs)
    (window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < heap.toNat →
      post.memory address = state.memory address)
    (arrayAbove : ceiling ≤ array.toNat) (arrayBefore : array.toNat + count.toNat * 16 ≤ heap.toNat) :
    RlpSliceInputPrefix post array input inputLength count.toNat := by
  have fits : array.toNat + count.toNat * 16 ≤ 2^64 := Nat.le_trans arrayBefore (Nat.le_of_lt heap.isLt)
  intro slot inside
  obtain ⟨pointer,length,entry⟩ := valid slot inside
  have cell0 := rlpSlice_cell_toNat array slot count 0 inside (by decide) fits
  have cell8 := rlpSlice_cell_toNat array slot count 8 inside (by decide) fits
  simp only [BitVec.add_zero,Nat.add_zero] at cell0
  have low0 : ceiling ≤ (array + slot * 16#64).toNat := by rw [cell0]; omega
  have high0 : (array + slot * 16#64).toNat < heap.toNat := by rw [cell0]; omega
  have low8 : ceiling ≤ (array + slot * 16#64 + 8#64).toNat := by rw [cell8]; omega
  have high8 : (array + slot * 16#64 + 8#64).toNat < heap.toNat := by rw [cell8]; omega
  exact ⟨pointer,length,RlpSliceInputEntry.after_frame state post array slot pointer length input inputLength
    entry domain (window _ low0 high0) (window _ low8 high8)⟩

#print axioms RlpSliceInputPrefix.after_window

/-- The frozen call semantics restores every caller local except the one the call binds. -/
theorem parent_record_carry_locals {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (heapStart pointer length : BitVec 64) (ceiling : Nat)
    (older outerInput outerLength olderCount : BitVec 64)
    (carried : parentRecordCarry s next heapStart pointer length ceiling older outerInput outerLength olderCount)
    (name : MlS) (different : name ≠ ofString "h") :
    next.locals.lookup name = s.locals.lookup name := by
  obtain ⟨_,_,_,_,_,_,_,_,_,nextEq,_,_,_,_,_,_,_,_,_,_,_,_⟩ := carried
  rw [nextEq]
  simp [validateHeadersContinuation,setVarHOLFinite,FUPDATE,Ne.symm different]

#print axioms parent_record_carry_locals

/-- The header decoder body is installed and inside the reviewed set, so it keeps the keccak
workspace globals at every fuel and outcome; the call therefore hands the tail the caller's
keccak state and pad pointers. -/
theorem parent_record_carry_workspace {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (heapStart pointer length : BitVec 64) (ceiling : Nat)
    (older outerInput outerLength olderCount : BitVec 64) (code : s.code = originalRuntimeCode)
    (carried : parentRecordCarry s next heapStart pointer length ceiling older outerInput outerLength olderCount)
    (name : MlS) (member : List.Mem name (parserWorkspaceGlobals : List MlS)) :
    next.globals.lookup name = s.globals.lookup name := by
  obtain ⟨value,post,_,record,_,run,_,_,_,nextEq,_,_,_,_,_,_,_,_,_,_,_,_⟩ := carried
  have sameCode : (callEntryStateHOLFinite s (rlpHeaderCallee pointer length)).code = s.code := rfl
  have entryCode : (callEntryStateHOLFinite s (rlpHeaderCallee pointer length)).code = originalRuntimeCode :=
    sameCode.trans code
  have bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s (rlpHeaderCallee pointer length))
      (sourceFunctionBody Guest.guestFn_decode_header) = (some (.returned value),post) := by
    simpa only [source_decode_header_body] using run
  have kept := header_decoder_keeps_parser_workspace
    (callEntryStateHOLFinite s (rlpHeaderCallee pointer length)) name member entryCode
  rw [bodyRun] at kept
  have sameGlobals : (callEntryStateHOLFinite s (rlpHeaderCallee pointer length)).globals = s.globals := rfl
  rw [sameGlobals] at kept
  rw [nextEq]
  simpa only [validateHeadersContinuation,setVarHOLFinite] using kept

#print axioms parent_record_carry_workspace

/-- The caller's slice-witness table is untouched by the decode call: it lies in the window
`[ceiling, heapStart)` the call reports as unchanged. -/
theorem parent_record_carry_table {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (heapStart pointer length : BitVec 64) (ceiling : Nat)
    (older outerInput outerLength olderCount : BitVec 64)
    (array count input inputLength : BitVec 64)
    (carried : parentRecordCarry s next heapStart pointer length ceiling older outerInput outerLength olderCount)
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (tableAbove : ceiling ≤ array.toNat) (tableBefore : array.toNat + count.toNat * 16 ≤ heapStart.toNat) :
    RlpSliceInputPrefix next array input inputLength count.toNat := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,domain,_,_,_,_,_,_,window,_⟩ := carried
  exact RlpSliceInputPrefix.after_window s next array count input inputLength heapStart ceiling table
    domain window tableAbove tableBefore

#print axioms parent_record_carry_table
end InitECandidate.Runtime
