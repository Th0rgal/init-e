import InitECandidate.Runtime.TransactionDecodeWitness
import InitECandidate.Runtime.TransactionWordFieldFrame
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful scalar field leaves the decoder index and heap unchanged. -/
theorem transaction_decode_witness_after_word {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (offset maximum errorCode : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word array),.val (.word valid.index),.val (.word maximum),.val (.word errorCode)])
    (inside : valid.index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + offset.toNat < array.toNat)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92643 ≤ state.clock)
    (run : evaluateHOLFiniteState state (transactionWordField offset arguments) = (none,post)) :
    ∃ next : TransactionDecodeWitness post array count tx kind input inputLength scratch frame ceiling,
      next.index = valid.index ∧ next.heap = valid.heap := by
  have kept := transaction_word_field_normal_frame state post array valid.index maximum errorCode input inputLength scratch frame count ceiling inputLimit
    arguments args valid.slices inside inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.code orderedFrame framePositive scratchBelow valid.arena
    budget arrayBelow tx offset valid.txLocal headerBefore run
  have locals : ∀ key, key ≠ ofString "w" → post.locals.lookup key = state.locals.lookup key := by
    intro key different
    apply evaluate_normalLocalFrame key (transactionWordField offset arguments) _ state post run
    simp [transactionWordField,normalLocalFrameSyntax,Ne.symm different]
  have metadata := evaluateHOLFiniteState_metadata state (transactionWordField offset arguments)
  rw [run] at metadata
  refine ⟨⟨valid.index,valid.heap,(locals _ (by decide)).trans valid.arrayLocal,
    (locals _ (by decide)).trans valid.txLocal,(locals _ (by decide)).trans valid.typeLocal,
    (locals _ (by decide)).trans valid.indexLocal,valid.indexBound,kept.2,
    (kept.1 _).trans valid.scratchGlobal,(kept.1 _).trans valid.frameGlobal,(kept.1 _).trans valid.heapGlobal,
    metadata.1.trans valid.code,?_,?_,valid.heapBound,valid.heapAligned,valid.inputBeforeHeap,valid.arrayBeforeHeap⟩,rfl,rfl⟩
  · intro address low high
    rw [metadata.2.1]
    exact valid.arena address low high
  · intro address low high
    rw [metadata.2.1]
    exact valid.heapArena address low high

#print axioms transaction_decode_witness_after_word
end InitECandidate.Runtime
