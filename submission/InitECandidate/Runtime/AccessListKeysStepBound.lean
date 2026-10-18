import InitECandidate.Runtime.TxFixedBytesAccessKeysCopyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual access-list key iteration loads its slice, checks fixed width, copies
32 bytes and increments the index within a common input-dependent budget. -/
theorem evaluate_access_keys_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count index buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]))
    (bufferLocal : state.locals.lookup (ofString "keys") = some (.val (.word buffer)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessKeysStep
    state.clock ≤ evaluated.2.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "slots")),.var .local (ofString "j"),.const 32] =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,indexLocal]
  have bound := evaluate_txFixedBytes_access_keys_copy_bounded state _ buffer bufferLocal array index 32 input inputLength scratch frame
    count.toNat ceiling inputLimit args indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena budget
  have source : accessKeysStep = .decCall (ofString "k") .one (ofString "tx_fixed_bytes")
      [.rfield 0 (.var .local (ofString "slots")),.var .local (ofString "j"),.const 32] accessKeysCopy := by
    exact source_access_keys_step
  rw [source]
  exact bound

#print axioms evaluate_access_keys_step_bounded
end InitECandidate.Runtime
