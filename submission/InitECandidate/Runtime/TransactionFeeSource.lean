import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.NormalLocalAddCalls
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionFeeArguments (shift : BitVec 64) : List (ExpHOL 64) :=
  [.var .local (ofString "arr"),if shift = 0 then .var .local (ofString "k") else .op .add [.var .local (ofString "k"),.const shift],.const 0]
def transactionFeeStore (offset : BitVec 64) : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "tx"),.const offset]) (.var .local (ofString "v"))
def transactionFeeCall (shift : BitVec 64) : ProgHOL 64 :=
  .call (some (some (.local,ofString "v"),none)) (ofString "tx_scalar_u256") (transactionFeeArguments shift)
def transactionFeeAdvance (amount : BitVec 64) : ProgHOL 64 :=
  .assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const amount])
def transactionFeeLegacy : ProgHOL 64 :=
  .seq (transactionFeeCall 0) (.seq (transactionFeeStore 48) (transactionFeeAdvance 1))
def transactionFeeDynamic : ProgHOL 64 :=
  .seq (transactionFeeCall 0) (.seq (transactionFeeStore 80)
    (.seq (transactionFeeCall 1) (.seq (transactionFeeStore 112) (transactionFeeAdvance 2))))
def transactionFeeBranch : ProgHOL 64 :=
  .ite (.cmp .notLower (.const 1) (.var .local (ofString "t"))) transactionFeeLegacy transactionFeeDynamic

theorem source_transaction_fee : transactionAt 22 = .seq transactionFeeBranch (transactionAt 23) := by
  simp only [transactionFeeBranch,transactionFeeLegacy,transactionFeeDynamic,transactionFeeCall,transactionFeeStore,
    transactionFeeAdvance,transactionFeeArguments]
  simp only [show (0 : BitVec 64) = 0 from rfl,if_true,show (1 : BitVec 64) ≠ 0 by decide,if_false]
  simp only [transactionAt,authorizationNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem transactionFeeLegacy_adds_one : NormalLocalAdd (ofString "k") 1 transactionFeeLegacy := by
  unfold transactionFeeLegacy transactionFeeCall transactionFeeStore transactionFeeAdvance
  apply normalLocalAdd_localCall _ _ _ _ _ _ (by decide)
  apply normalLocalAdd_seq _ _ _ _ (by rfl)
  exact normalLocalAdd_assign _ 1

theorem transactionFeeDynamic_adds_two : NormalLocalAdd (ofString "k") 2 transactionFeeDynamic := by
  unfold transactionFeeDynamic transactionFeeCall transactionFeeStore transactionFeeAdvance
  apply normalLocalAdd_localCall _ _ _ _ _ _ (by decide)
  apply normalLocalAdd_seq _ _ _ _ (by rfl)
  apply normalLocalAdd_localCall _ _ _ _ _ _ (by decide)
  apply normalLocalAdd_seq _ _ _ _ (by rfl)
  exact normalLocalAdd_assign _ 2

theorem transaction_fee_branch_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (notIndex : key ≠ ofString "k") (notValue : key ≠ ofString "v")
    (run : evaluateHOLFiniteState state transactionFeeBranch = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  apply evaluate_normalLocalFrame key transactionFeeBranch _ state post run
  simp [transactionFeeBranch,transactionFeeLegacy,transactionFeeDynamic,transactionFeeCall,transactionFeeStore,
    transactionFeeAdvance,normalLocalFrameSyntax,Ne.symm notIndex,Ne.symm notValue]

#print axioms source_transaction_fee
#print axioms transactionFeeLegacy_adds_one
#print axioms transactionFeeDynamic_adds_two
#print axioms transaction_fee_branch_other_local
end InitECandidate.Runtime
