import InitECandidate.Runtime.BlobHashesLoopReturnIndependentOuterPrefix
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem blobHashes_initialized_returned_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBeforeFrame : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (watchedBeforeBuffer : watchedArray.toNat + watchedCount.toNat * 16 ≤ buffer.toNat)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state blobHashesInitialized = (some (.returned value),post)) :
    RlpSliceInputPrefix post watchedArray watchedInput watchedLength watchedCount.toNat := by
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
  rw [source_blobHashes_initialized] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state post (ofString "i") (.const 0) 0 blobHashesLoopAndReturn
    (some (.returned value)) (by rfl) run
  have initialWatched : RlpSliceInputPrefix initial watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := watchedValid slot inside
    exact ⟨p,n,item.after_frame state initial watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have retained := blobHashes_loop_returned_independent_outer_prefix initial output array count buffer input inputLength scratch frame ceiling inputLimit
    valid inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits
    watchedArray watchedCount watchedInput watchedLength initialWatched watchedBeforeFrame watchedBeforeBuffer
    (by change (count.toNat - 0) * _ ≤ state.clock; simpa only [Nat.sub_zero] using budget) value bodyRun
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩

#print axioms blobHashes_initialized_returned_independent_outer_prefix
end InitECandidate.Runtime
