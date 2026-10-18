import InitECandidate.Runtime.AccessListItemCheckBound
import InitECandidate.Runtime.AccessListInnerSlicesIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_item_check_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (kind pointer length total input inputLength scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
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
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (reserve : array.toNat + length.toNat * 16 + 7 + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : accessInnerSlicesCost length.toNat inputLength.toNat ≤ state.clock)
    (outerArray outerCount outerInput outerLength records outerIndex : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBeforeFrame : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (outerBeforeArray : outerArray.toNat + outerCount.toNat * 16 ≤ array.toNat)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ (records + outerIndex * 24#64).toNat)
    (recordFits : (records + outerIndex * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessItemCheck = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
  let guard : ProgHOL 64 := .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
    (.raise (ofString "TxErr") (.const 19)) .skip
  by_cases listKind : kind = 1#64
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1)) = some (.val (.word 0)) := by
      simp [evalHOLExact,itemLocal,Compiler.Encoders.Asm.wordCmpHOL,listKind]
    have passed : evaluateHOLFiniteState state guard = (none,state) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
        (.raise (ofString "TxErr") (.const 19)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] =
        some [.val (.word pointer),.val (.word length)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,itemLocal]
    rw [source_access_item_check,evaluateHOLFiniteState_seq_line780,passed] at run
    exact access_inner_slices_independent_outer_prefix state final pointer length input inputLength scratch frame array
      ceiling inputLimit args noWrap lengthBound inputBound limitBound inputStarts inputEnds scratchGlobal frameGlobal code
      orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray
      arrayBeforeFrame wholeInputBeforeArray reserve budget outerArray outerCount outerInput outerLength records outerIndex outerValid outerBeforeFrame outerBeforeArray recordsLocal binding outerBeforeRecord recordFits run
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1)) = some (.val (.word 1)) := by
      simp [evalHOLExact,itemLocal,Compiler.Encoders.Asm.wordCmpHOL] <;> simp_all
    have failed : evaluateHOLFiniteState state guard =
        evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 19)) := by
      rw [show guard = .ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "it"))) (.const 1))
        (.raise (ofString "TxErr") (.const 19)) .skip from rfl,evaluateHOLFiniteState_ite,condition]
      simp
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 19)
    have safe := evaluate_raise_no_timeout state (ofString "TxErr") (.const 19)
    have clock := clockPreserving_raise (σ := F) (ofString "TxErr") (.const 19) state
    rw [source_access_item_check,evaluateHOLFiniteState_seq_line780,failed] at run
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 19)) with
    | mk result post =>
      rw [raised] at terminal safe clock run
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        cases run

#print axioms access_item_check_independent_outer_prefix
end InitECandidate.Runtime
