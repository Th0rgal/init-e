import InitECandidate.Runtime.TransactionTypeBranchAbove
import InitECandidate.Runtime.NoDirectReturn
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_parse_returned_heap_input_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (array count input inputLength : BitVec 64)
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (above : ceiling ≤ array.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 9) = (some (.returned value),post)) :
    ∃ middle, evaluateHOLFiniteState state transactionTypeParseBranch = (none,middle) ∧
      evaluateHOLFiniteState middle (transactionAt 10) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat := by
  have noReturn := evaluate_noDirectReturn transactionTypeParseBranch (by
    simp only [transactionTypeParseBranch,transactionAt,authorizationNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl) state value
  rw [source_transaction_type_parse,evaluateHOLFiniteState_seq_line780] at run
  cases parsed : evaluateHOLFiniteState state transactionTypeParseBranch with
  | mk result middle =>
    rw [parsed] at run noReturn
    cases result with
    | none =>
      have retained := transaction_type_branch_normal_heap_input_prefix state middle pointer length scratch frame ceiling inputLimit
        pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
        scratchBelow arena budget array count input inputLength valid fits above parsed
      exact ⟨middle,rfl,run,retained⟩
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)

#print axioms transaction_type_parse_returned_heap_input_prefix
end InitECandidate.Runtime
