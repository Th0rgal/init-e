import InitECandidate.Runtime.HtrBytesVectorCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.HtabDelBound
import InitECandidate.Runtime.HtrBytesVectorLongMemory
import InitECandidate.Runtime.HtrBytesVectorShortMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrBytesVector_short_not_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state htrBytesVectorShort = (none,post)) : False := by
  unfold htrBytesVectorShort at run
  obtain ⟨middle,_,tail⟩ := seq_normal_parts run
  obtain ⟨finished,_,returned⟩ := seq_normal_parts tail
  exact evaluate_return_terminal finished (.const 0) (by rw [returned])

#print axioms htrBytesVector_short_not_normal

theorem htrBytesVector_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p n heap out watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atLength : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrBytesVectorBodyCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htr_bytes_vector) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have check : evaluateHOLFiniteState state htrBytesVectorCheck =
      if n.toNat ≤ 32 then evaluateHOLFiniteState state htrBytesVectorShort else (none,state) := by
    unfold htrBytesVectorCheck
    rw [evaluateHOLFiniteState_ite]
    by_cases short : n.toNat ≤ 32
    all_goals simp [evalHOLExact,atLength,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,short,evaluateHOLFiniteState_skip]
  rw [source_htrBytesVector_body,evaluateHOLFiniteState_seq_line780,check] at run
  by_cases short : n.toNat ≤ 32
  · rw [if_pos short] at run
    cases shortRun : evaluateHOLFiniteState state htrBytesVectorShort with
    | mk result middle =>
      rw [shortRun] at run
      cases result with
      | none => exact False.elim (htrBytesVector_short_not_normal state middle shortRun)
      | some stopped =>
        obtain ⟨same,rfl⟩ := Prod.mk.inj run
        change some stopped = some (.returned value) at same
        cases same
        exact htrBytesVector_short_returned_memory state middle p n out watched value atInput atLength atOut short
          outAligned outFits outOutside code ((Nat.le_add_right _ _).trans budget) shortRun
  · rw [if_neg short] at run
    exact htrBytesVectorLong_body_returned_memory state post pointer accelerator zeroHashes p n heap out watched value
      atPointer atAccel atLength atZero atInput hh atOut outAligned outFits outOutside small heapAligned heapFits heapBefore
      accelAligned accelFits pointerFits accelOutside pointerOutside code ((Nat.le_add_left _ _).trans budget) run

#print axioms htrBytesVector_body_returned_memory
theorem htrBytesVector_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer accelerator zeroHashes p n heap out watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word p),.val (.word n),.val (.word out)])
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrBytesVectorBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_bytes_vector") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "htr_bytes_vector") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bytes_vector,.one) := by
    rw [code]; exact originalRuntimeCode_htrBytesVector_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htr_bytes_vector")
    (ofString "p") (ofString "n") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_bytes_vector) p n out
    (by decide) (by decide) (by decide) installed
  obtain ⟨returned,output,bodyRun,_,scope⟩ := evaluate_discardCall_normal_result state post (ofString "htr_bytes_vector")
    .one arguments _ _ _ args lookup run
  let entry := callEntryStateHOLFinite state
    (((HolFiniteMapExact.empty.update (ofString "p",.val (.word p))).update (ofString "n",.val (.word n))).update
      (ofString "out",.val (.word out)))
  rw [scope]
  exact htrBytesVector_body_returned_memory entry output pointer accelerator zeroHashes p n heap out watched returned
    atPointer atAccel
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) atZero
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) hh
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    outAligned outFits outOutside small heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside code (by change htrBytesVectorBodyCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget) bodyRun

#print axioms htrBytesVector_call_normal_memory
end InitECandidate.Runtime
