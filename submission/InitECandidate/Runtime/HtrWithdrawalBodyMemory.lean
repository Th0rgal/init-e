import InitECandidate.Runtime.HtrWithdrawalAllocationMemory
import InitECandidate.Runtime.HeapMarkCall
import InitECandidate.Runtime.HtrWithdrawalBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

theorem htrWithdrawal_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes w heap out watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atInput : state.locals.lookup (ofString "w") = some (.val (.word w)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrWithdrawalBodyCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrWithdrawalAt 0) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have enough : 1 ≤ state.clock := (Nat.le_add_right 1 _).trans budget
  obtain ⟨marked,_,clock,memory,globals,locals,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap code hh (by omega)
  change evaluateHOLFiniteState state (htrWithdrawalAt 0) = _ at run
  rw [source_htrWithdrawal_mark,declaration] at run
  let next := setVarHOLFinite (ofString "mark") (.val (.word heap)) marked
  change (let output := evaluateHOLFiniteState next (htrWithdrawalAt 1);
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) =
      (some (.returned value),post) at run
  cases tailRun : evaluateHOLFiniteState next (htrWithdrawalAt 1) with
  | mk result inner =>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    change result = some (.returned value) at resultEq
    subst result
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have remaining : htrWithdrawalAllocationCost ≤ next.clock := by
      change _ ≤ marked.clock
      unfold htrWithdrawalBodyCost at budget
      omega
    have frame := htrWithdrawal_allocation_returned_memory next inner pointer accelerator zeroHashes w heap out heap watched value
      ((keep _ (by decide)).trans atInput)
      (by change marked.globals.lookup _ = _; rw [globals]; exact atPointer)
      (by change marked.globals.lookup _ = _; rw [globals]; exact atAccel)
      (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by change marked.globals.lookup _ = _; rw [globals]; exact atZero)
      (by change marked.globals.lookup _ = _; rw [globals]; exact hh)
      ((keep _ (by decide)).trans atOut)
      outAligned outFits outOutside heapAligned heapFits heapBefore accelAligned accelFits pointerFits
      accelOutside pointerOutside (installed.trans code) remaining tailRun
    rw [← postEq]
    exact frame.trans (congrFun memory watched)

#print axioms htrWithdrawal_body_returned_memory
end InitECandidate.Runtime
