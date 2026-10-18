import InitECandidate.Runtime.AuthorizationsItemCheckIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsInnerSlicesHeapIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsInnerSlicesHeapBound
import InitECandidate.Runtime.AuthorizationsItemCheckSource
import InitECandidate.Runtime.TrapBodyClock
import InitECandidate.Runtime.AuthorizationsInnerSlicesSource
import InitECandidate.Runtime.AuthorizationsEntryCheckHeapBound
import InitECandidate.Runtime.RlpSlicesBodyRuntimeContract
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.BlobHashesDeclarationBound
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful item-kind checking, inner slicing and record processing preserve the outer slice array. -/
theorem authorization_item_check_normal_heap_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (record records index kind pointer length total input inputLength scratch frame array outerArray outerCount outerInput outerLength : BitVec 64) (ceiling inputLimit : Nat)
    (recordAddress : record = records + index * 120#64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (itemLocal : state.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word total)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (inputStarts : input.toNat ≤ pointer.toNat)
    (inputEnds : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (recordBeforeArray : record.toNat + 120 ≤ array.toNat) (recordFits : record.toNat + 120 < 2^64)
    (budget : authorizationInnerSlicesCost length.toNat inputLength.toNat ≤ state.clock)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64) (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (run : evaluateHOLFiniteState state authorizationItemCheck = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
  let guard : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
    (.raise (ofString "TxErr") (.const 20)) .skip
  by_cases listKind : kind = 1#64
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1)) = some (.val (.word 0)) := by
      simp [evalHOLExact,itemLocal,Compiler.Encoders.Asm.wordCmpHOL,listKind]
    have passed : evaluateHOLFiniteState state guard = (none,state) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
        (.raise (ofString "TxErr") (.const 20)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] =
        some [.val (.word pointer),.val (.word length)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,itemLocal]
    rw [source_authorization_item_check,evaluateHOLFiniteState_seq_line780,passed] at run
    exact authorization_inner_slices_normal_heap_independent_outer_prefix state final record records index pointer length input inputLength scratch frame array
      outerArray outerCount outerInput outerLength ceiling inputLimit recordAddress recordsLocal indexLocal args noWrap lengthBound inputBound limitBound inputStarts inputEnds
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
      inputBeforeFrame inputBeforeArray arrayAbove recordBeforeArray recordFits budget outerValid outerFits outerAbove outerBeforeRecord run
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1)) = some (.val (.word 1)) := by
      simp [evalHOLExact,itemLocal,Compiler.Encoders.Asm.wordCmpHOL] <;> simp_all
    have failed : evaluateHOLFiniteState state guard =
        evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 20)) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
        (.raise (ofString "TxErr") (.const 20)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 20)
    have safe := evaluate_raise_no_timeout state (ofString "TxErr") (.const 20)
    have clock := clockPreserving_raise (σ := F) (ofString "TxErr") (.const 20) state
    rw [source_authorization_item_check,evaluateHOLFiniteState_seq_line780,failed] at run
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 20)) with
    | mk result post =>
      rw [raised] at terminal safe clock run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        cases run

#print axioms authorization_item_check_normal_heap_independent_outer_prefix
end InitECandidate.Runtime
