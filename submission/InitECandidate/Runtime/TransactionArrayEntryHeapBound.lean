import InitECandidate.Runtime.TransactionArrayScopeBound
import InitECandidate.Runtime.TransactionFieldCountEntryHeapBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_array_entry_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count expected tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness (setVarHOLFinite (ofString "k") (.val (.word 0)) (setVarHOLFinite (ofString "arr") (.val (.word array)) state)) array count tx kind input inputLength scratch frame ceiling)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (fields : (if kind = 0#64 then (0 : BitVec 64) else 1).toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + (if 1#64 < kind then 10 else 9) ≤ expected.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionChainIdSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 13)
    state.clock ≤ evaluated.2.clock + transactionChainIdSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.rfield 0 (.var .local (ofString "lst"))) = some (.val (.word array)) := by
    simp [evalHOLExact,listLocal]
  have bounded := transaction_field_count_entry_heap_bounded _ array count expected tx kind input inputLength scratch frame ceiling inputLimit
    valid (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "arr" ≠ ofString "lst" by decide] using listLocal)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "arr" ≠ ofString "nfields" by decide] using expectedLocal)
    fields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore budget
  rw [source_transaction_array_scope,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  have checked : shapeEqHOL .one (shapeOfHOLExact (.val (.word array))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  dsimp only
  rw [checked]
  exact bounded

#print axioms source_transaction_array_scope
#print axioms transaction_array_entry_heap_bounded
end InitECandidate.Runtime
