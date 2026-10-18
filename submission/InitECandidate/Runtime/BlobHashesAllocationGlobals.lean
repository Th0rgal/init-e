import InitECandidate.Runtime.BlobHashesInitializationGlobals
import InitECandidate.Runtime.AllocationReturnedGuard
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem blobHashes_allocation_returned_globals {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (slices : RlpSliceInputPrefix state array input inputLength count.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word buffer)))
    (heapBound : buffer.toNat ≤ 33806089496) (countBound : count.toNat * 32 < 2^64)
    (budget : count.toNat *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state blobHashesAfterSlices = (some (.returned value),final)) :
    final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let argument : ExpHOL 64 := .panop .mul [.rfield 1 (.var .local (ofString "lst")),.const 32]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 32))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,panOpHOL,valueIsWord,valueWord]
  rw [source_blobHashes_allocation] at run
  have request := alloc_declaration_returned_request state final argument buffer (count * 32) (ofString "buf") .one
    blobHashesInitialized value args code heap run
  obtain ⟨ready,_,clock,memory,locals,readyCode,domain,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state argument buffer
    (count * 32) args code (by omega) heap request (allocationEnd_within_heap buffer (count * 32) heapBound request)
  let entered := setVarHOLFinite (ofString "buf") (.val (.word buffer)) ready
  have atList : entered.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "buf" ≠ ofString "lst" by decide] using listLocal
  have atBuffer : entered.locals.lookup (ofString "buf") = some (.val (.word buffer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredSlices : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entered array slot p n input inputLength item domain (congrFun memory _) (congrFun memory _)⟩
  have atScratch : entered.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide] using scratchGlobal
  have atFrame : entered.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
    change ready.globals.lookup _ = _
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide] using frameGlobal
  have enteredArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → entered.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain]
    exact arena address lower upper
  have interval := allocationGuard_sum_bound buffer (count * 32) heapBound request
  have product : (count * 32).toNat = count.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 32 < 2^64; exact countBound)]
    rfl
  rw [product] at interval
  change evaluateHOLFiniteState state (.decCall (ofString "buf") .one (ofString "alloc") [argument] blobHashesInitialized) = _ at run
  rw [decl] at run
  cases tailRun : evaluateHOLFiniteState entered blobHashesInitialized with
  | mk result output =>
    rw [tailRun] at run
    have same : result = some (.returned value) := (Prod.mk.inj run).1
    subst result
    have retained := blobHashes_initialized_returned_globals entered output array count buffer input inputLength scratch frame ceiling inputLimit
      atList atBuffer enteredSlices atScratch atFrame (readyCode.trans code) enteredArena inputBound limitBound orderedFrame framePositive
      scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned (Nat.le_trans interval (by decide))
      (by
        change count.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ ready.clock
        rw [clock]
        exact Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) budget))
      value tailRun
    have restored := (Prod.mk.inj run).2
    rw [← restored]
    exact retained

#print axioms blobHashes_allocation_returned_globals
end InitECandidate.Runtime
