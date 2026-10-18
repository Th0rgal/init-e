import InitECandidate.Runtime.TransactionIndexScopeHeapKindBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_index_entry_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness (setVarHOLFinite (ofString "k") (.val (.word 0)) state) array count tx kind input inputLength scratch frame ceiling)
    (fields : (if kind = 0#64 then (0 : BitVec 64) else 1).toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + (if 1#64 < kind then 10 else 9) ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayAbove : ceiling ≤ array.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (budget : transactionChainIdSuffixCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 15)
    state.clock ≤ evaluated.2.clock + transactionChainIdSuffixCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let value : ValueHOL 64 := .val (.word 0)
  have indexZero : valid.index = 0 := by
    have binding : some (ValueHOL.val (HolWordLab.word (0 : BitVec 64))) = some (.val (.word valid.index)) := by
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using valid.indexLocal
    exact (HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj binding))).symm
  have bounded := transaction_word_scope_heap_bounded_by_kind _ array count tx kind input inputLength scratch frame ceiling inputLimit
    valid (by rw [indexZero]; exact fields) inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayAbove inputBeforeFrame headerBefore budget
  have initial : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.const 0) = some value := by
    simp [value,evalHOLExact]
  have checked : shapeEqHOL .one (shapeOfHOLExact value) = true := by
    simp [value,shapeOfHOLExact,shapeEqHOL]
  rw [source_transaction_index_scope,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [initial]
  dsimp only
  rw [checked]
  exact bounded

#print axioms source_transaction_index_scope
#print axioms transaction_index_entry_heap_bounded
end InitECandidate.Runtime
