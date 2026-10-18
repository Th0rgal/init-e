import InitECandidate.Runtime.AccessListKeysInitializationBound
import InitECandidate.Runtime.AccessListKeysLoopRecordProgress
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_keys_initialized_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]))
    (bufferLocal : state.locals.lookup (ofString "keys") = some (.val (.word buffer)))
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
    (outerIndex : BitVec 64)
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (run : evaluateHOLFiniteState state accessKeysInitialization = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (outerIndex + 1))) ∧
      post.locals.lookup (ofString "lst") = state.locals.lookup (ofString "lst") ∧
      post.locals.lookup (ofString "recs") = state.locals.lookup (ofString "recs") := by
  let initial := setVarHOLFinite (ofString "j") (.val (.word (0 : BitVec 64))) state
  have atList : initial.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "slots" by decide] using listLocal
  have atBuffer : initial.locals.lookup (ofString "keys") = some (.val (.word buffer)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "keys" by decide] using bufferLocal
  have atIndex : initial.locals.lookup (ofString "j") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have initialSlices : RlpSliceInputPrefix initial array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,entry⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame state initial array slot p n input inputLength entry rfl rfl rfl⟩
  let valid : AccessKeysLoopWitness initial array count buffer input inputLength scratch frame ceiling :=
    ⟨0,atList,atBuffer,atIndex,by simp,initialSlices,scratchGlobal,frameGlobal,code,arena⟩
  rw [source_access_keys_initialized] at run
  obtain ⟨value,output,initialized,tail,restored⟩ := evaluate_dec_normal_scope state post (ofString "j") .one (.const 0) accessKeysLoopAndRecord run
  have equal : value = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using initialized.symm
  subst value
  have initialIndex : initial.locals.lookup (ofString "i") = some (.val (.word outerIndex)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "i" by decide] using binding
  have ticks : (count.toNat - valid.index.toNat) * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ initial.clock := by
    change (count.toNat - 0) * _ ≤ state.clock
    simpa only [Nat.sub_zero] using budget
  have advanced := access_keys_loop_and_record_progress initial output array count buffer input inputLength scratch frame ceiling inputLimit valid
    inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits ticks outerIndex initialIndex tail
  have kept := access_keys_loop_and_record_locals initial output array count buffer input inputLength scratch frame ceiling inputLimit valid
    inputBound limitBound orderedFrame framePositive scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits ticks tail
  rw [restored]
  refine ⟨?_,?_,?_⟩
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "j",state.locals.lookup (ofString "j"))).lookup (ofString "i") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact advanced
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "j",state.locals.lookup (ofString "j"))).lookup (ofString "lst") = _
    rw [restore_other_local _ _ _ _ (by decide),kept.1]
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "lst" by decide]
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "j",state.locals.lookup (ofString "j"))).lookup (ofString "recs") = _
    rw [restore_other_local _ _ _ _ (by decide),kept.2]
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "recs" by decide]

#print axioms access_keys_initialized_progress
end InitECandidate.Runtime
