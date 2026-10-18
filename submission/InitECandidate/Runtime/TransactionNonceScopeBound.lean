import InitECandidate.Runtime.TransactionNonceSuffixBound
import InitECandidate.Runtime.TransactionWitnessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_transaction_nonce_scope : transactionAt 18 =
    .dec (ofString "v") (.comb [.one,.one,.one,.one])
      (.rstruct [.const 0,.const 0,.const 0,.const 0]) (transactionAt 19) := by
  simp only [transactionAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem transaction_nonce_scope_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + 14 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionNonceSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 18)
    state.clock ≤ evaluated.2.clock + transactionNonceSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let value : ValueHOL 64 := .rStruct [.val (.word 0),.val (.word 0),.val (.word 0),.val (.word 0)]
  let next := valid.enterScope (ofString "v") value (by decide) (by decide) (by decide) (by decide)
  have bounded := transaction_nonce_suffix_bounded _ array count tx kind input inputLength scratch frame ceiling inputLimit
    next fields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore reserve budget
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.rstruct [.const 0,.const 0,.const 0,.const 0]) = some value := by
    simp [value,evalHOLExact,evalListHOLExact]
  have checked : shapeEqHOL (.comb [.one,.one,.one,.one]) (shapeOfHOLExact value) = true := by
    simp [value,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
  rw [source_transaction_nonce_scope,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  dsimp only
  rw [checked]
  exact bounded

#print axioms source_transaction_nonce_scope
#print axioms transaction_nonce_scope_bounded
end InitECandidate.Runtime
