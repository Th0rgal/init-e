import InitECandidate.Runtime.TransactionToBranchFrame
import InitECandidate.Runtime.TransactionToBranchValue
import InitECandidate.Runtime.TransactionWordHeaderPrefix
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem transaction_to_field_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame count : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (headerBefore : tx.toNat + 152 < array.toNat)
    (run : evaluateHOLFiniteState state transactionToField = (none,post)) :
    (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      RlpSliceInputPrefix post array input inputLength count.toNat := by
  unfold transactionToField at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionToBranch with
  | mk result middle =>
    rw [branchRun] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      have kept := transaction_to_branch_normal_frame state middle array index input inputLength scratch frame count ceiling inputLimit
        arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayBelow branchRun
      obtain ⟨word,valueLocal⟩ := transaction_to_branch_word state middle array index arrayLocal indexLocal code branchRun
      have txSame : middle.locals.lookup (ofString "tx") = state.locals.lookup (ofString "tx") := by
        apply evaluate_normalLocalFrame (ofString "tx") transactionToBranch _ state middle branchRun
        simp [transactionToBranch,normalLocalFrameSyntax,show ofString "w" ≠ ofString "tx" by decide]
      have stored := transaction_word_header_prefix middle tx 152 array count input inputLength word (ofString "w")
        (txSame.trans txLocal) valueLocal kept.2 (by change tx.toNat + 152 < array.toNat; exact headerBefore)
        (Nat.le_trans arrayBelow (Nat.le_of_lt frame.isLt))
      change evaluateHOLFiniteState middle transactionToStore = (none,post) at run
      change RlpSliceInputPrefix (evaluateHOLFiniteState middle transactionToStore).2 array input inputLength count.toNat at stored
      rw [run] at stored
      refine ⟨?_,stored⟩
      intro watched
      have globals := evaluate_avoidsGlobalAssignment watched transactionToStore (by rfl) middle
      rw [run] at globals
      exact globals.trans (kept.1 watched)

#print axioms transaction_to_field_normal_frame
end InitECandidate.Runtime
