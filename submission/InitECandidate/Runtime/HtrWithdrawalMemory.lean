import InitECandidate.Runtime.HtrWithdrawalBodyMemory
import InitECandidate.Runtime.HtrWithdrawalCallBound
import InitECandidate.Runtime.PanDiscardCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrWithdrawal_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer accelerator zeroHashes w heap out watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word w),.val (.word out)])
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrWithdrawalBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_withdrawal") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "htr_withdrawal") =
      some ([(ofString "w",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_htr_withdrawal,.one) := by
    rw [code]
    exact originalRuntimeCode_htrWithdrawal_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "htr_withdrawal") (ofString "w") (ofString "out")
    (sourceFunctionBody Guest.guestFn_htr_withdrawal) w out (by decide) installed
  obtain ⟨value,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "htr_withdrawal")
    .one arguments _ _ _ args lookup run
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "w",.val (.word w))).update (ofString "out",.val (.word out)))
  rw [sourceFunctionBody_eq_structural] at bodyRun
  rw [postEq]
  exact htrWithdrawal_body_returned_memory entry output pointer accelerator zeroHashes w heap out watched value
    atPointer atAccel atZero
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) hh
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    outAligned outFits outOutside heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside code (by change htrWithdrawalBodyCost ≤ state.clock - 1; exact Nat.le_sub_of_add_le budget) bodyRun

#print axioms htrWithdrawal_call_normal_memory
end InitECandidate.Runtime
