import InitECandidate.Runtime.BlobHashesLoopReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_blobHashes_initialized_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (bufferLocal : state.locals.lookup (ofString "buf") = some (.val (.word buffer)))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : count.toNat *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state blobHashesInitialized
    state.clock ≤ evaluated.2.clock + count.toNat *
        (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let initial := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have atList : initial.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "lst" by decide] using listLocal
  have atBuffer : initial.locals.lookup (ofString "buf") = some (.val (.word buffer)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "buf" by decide] using bufferLocal
  have atIndex : initial.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initialSlices : RlpSliceInputPrefix initial array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,entry⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame state initial array slot p n input inputLength entry rfl rfl rfl⟩
  let valid : BlobHashesLoopWitness initial array count buffer input inputLength scratch frame ceiling :=
    ⟨0,atList,atBuffer,atIndex,by simp,initialSlices,scratchGlobal,frameGlobal,code,arena⟩
  have bound := evaluate_blobHashes_loop_and_return_bounded initial array count buffer input inputLength scratch frame ceiling inputLimit
    valid inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits
    (by change (count.toNat - 0) * _ ≤ state.clock; simpa only [Nat.sub_zero] using budget)
  rw [source_blobHashes_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState initial blobHashesLoopAndReturn with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_blobHashes_initialized_bounded
end InitECandidate.Runtime
