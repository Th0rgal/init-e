import InitECandidate.Runtime.TransactionFeeBranchOuterFrame
import InitECandidate.Runtime.NoDirectReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_fee_returned_outer_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx : BitVec 64)
    (array index input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (insideNext : (index + 1).toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : 2 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) ≤ state.clock)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 112 + 24 < array.toNat)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (transactionAt 22) = (some (.returned value),post)) :
    ∃ (middle : PanSemStateFiniteExact 64 F) (advance : BitVec 64),
      evaluateHOLFiniteState middle (transactionAt 23) = (some (.returned value),post) ∧
      RlpSliceInputPrefix middle array input inputLength count.toNat ∧
      RlpSliceInputPrefix middle outerArray outerInput outerLength outerCount.toNat ∧
      (∀ watched, middle.globals.lookup watched = state.globals.lookup watched) ∧
      (∀ name, name ≠ ofString "k" → name ≠ ofString "v" → middle.locals.lookup name = state.locals.lookup name) ∧
      middle.code = state.code ∧ middle.memaddrs = state.memaddrs ∧ middle.clock ≤ state.clock ∧
      (advance = 1 ∨ advance = 2) ∧ middle.locals.lookup (ofString "k") = some (.val (.word (index + advance))) := by
  have noReturn := evaluate_noDirectReturn transactionFeeBranch (by rfl) state value
  have metadata := evaluateHOLFiniteState_metadata state transactionFeeBranch
  have clock := evaluateHOLFiniteState_clock_le state transactionFeeBranch
  rw [source_transaction_fee,evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionFeeBranch with
  | mk result middle =>
    rw [branchRun] at run noReturn metadata clock
    cases result with
    | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      obtain ⟨slices,outer,globals,advance,advanceBound,indexPost⟩ := transaction_fee_branch_normal_outer_frame state middle tx
        array index input inputLength scratch frame count ceiling inputLimit arrayLocal indexLocal valid inside insideNext
        inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayBelow txLocal before
        outerArray outerCount outerInput outerLength outerValid outerBelow beforeTx branchRun
      refine ⟨middle,advance,run,slices,outer,globals,?_,metadata.1,metadata.2.1,clock,advanceBound,indexPost⟩
      intro name notIndex notValue
      exact transaction_fee_branch_other_local state middle name notIndex notValue branchRun

#print axioms transaction_fee_returned_outer_contract
end InitECandidate.Runtime
