import InitECandidate.Runtime.TransactionNonceBranchFrame
import InitECandidate.Runtime.TransactionNonceBranchValue
import InitECandidate.Runtime.TransactionU256HeaderPrefix
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem transaction_nonce_field_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (tx : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (headerBefore : tx.toNat + 16 + 24 < array.toNat)
    (run : evaluateHOLFiniteState state transactionNonceField = (none,post)) :
    (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
      RlpSliceInputPrefix post array input inputLength count.toNat := by
  unfold transactionNonceField at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases branchRun : evaluateHOLFiniteState state transactionNonceBranch with
  | mk result middle =>
    rw [branchRun] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      have kept := transaction_nonce_branch_normal_frame state middle array index input inputLength scratch frame count ceiling inputLimit
        arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget arrayBelow branchRun
      obtain ⟨first,second,third,fourth,valueLocal⟩ := transaction_nonce_branch_four_words state middle array index arrayLocal indexLocal code branchRun
      have txSame : middle.locals.lookup (ofString "tx") = state.locals.lookup (ofString "tx") := by
        apply evaluate_normalLocalFrame (ofString "tx") transactionNonceBranch _ state middle branchRun
        simp [transactionNonceBranch,transactionNonceWiden,normalLocalFrameSyntax,show ofString "w" ≠ ofString "tx" by decide,show ofString "v" ≠ ofString "tx" by decide]
      have stored := transaction_u256_header_input_prefix middle tx 16 array count input inputLength
        (.rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)])
        (txSame.trans txLocal) valueLocal (by simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]) kept.2
        (by change tx.toNat + 16 + 24 < array.toNat; exact headerBefore)
        (Nat.le_trans arrayBelow (Nat.le_of_lt frame.isLt))
      change evaluateHOLFiniteState middle transactionNonceStore = (none,post) at run
      change RlpSliceInputPrefix (evaluateHOLFiniteState middle transactionNonceStore).2 array input inputLength count.toNat at stored
      rw [run] at stored
      refine ⟨?_,stored⟩
      intro watched
      have globals := evaluate_avoidsGlobalAssignment watched transactionNonceStore (by rfl) middle
      rw [run] at globals
      exact globals.trans (kept.1 watched)

#print axioms transaction_nonce_field_normal_frame
end InitECandidate.Runtime
