import InitECandidate.Runtime.AccessListKeysInitializationBound
import InitECandidate.Runtime.AccessListKeysLoopRecordHeapIndependentOuterPrefix
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_keys_initialized_heap_independent_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : count.toNat *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (outerArray outerCount outerInput outerLength records outerIndex address : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeBuffer : outerArray.toNat + outerCount.toNat * 16 ≤ buffer.toNat)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (addressLocal : state.locals.lookup (ofString "addr") = some (.val (.word address)))
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ (records + outerIndex * 24#64).toNat)
    (recordFits : (records + outerIndex * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessKeysInitialization = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
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
  have initialOuter : RlpSliceInputPrefix initial outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,entry⟩ := outerValid slot inside
    exact ⟨p,n,entry.after_frame state initial outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have initialRecords : initial.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "recs" by decide] using recordsLocal
  have initialAddress : initial.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "j" ≠ ofString "addr" by decide] using addressLocal
  have kept := access_keys_loop_and_record_normal_heap_independent_outer_prefix initial output array count buffer input inputLength scratch frame ceiling inputLimit
    outerArray outerCount outerInput outerLength initialOuter outerAbove outerBeforeBuffer valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove arrayBeforeBuffer aligned fits ticks records outerIndex address initialRecords initialIndex initialAddress
    outerBeforeRecord recordFits tail
  rw [restored]
  intro slot inside
  obtain ⟨p,n,entry⟩ := kept slot inside
  exact ⟨p,n,entry.after_frame output _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms access_keys_initialized_heap_independent_outer_prefix
end InitECandidate.Runtime
