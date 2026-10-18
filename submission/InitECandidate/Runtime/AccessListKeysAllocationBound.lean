import InitECandidate.Runtime.AccessListKeysInitializationBound
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_access_keys_allocation : accessKeysAllocation =
    .decCall (ofString "keys") .one (ofString "alloc")
      [.panop .mul [.rfield 1 (.var .local (ofString "slots")),.const 32]] accessKeysInitialization := by
  simp only [accessKeysAllocation,accessKeysInitialization,accessAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_access_keys_allocation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (listLocal : state.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]))
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
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessKeysAllocation
    state.clock ≤ evaluated.2.clock + (count.toNat *
        (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let argument : ExpHOL 64 := .panop .mul [.rfield 1 (.var .local (ofString "slots")),.const 32]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 32))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,panOpHOL,valueIsWord,valueWord]
  by_cases request : count * 32 ≤ (33806089496 : BitVec 64) - buffer
  · obtain ⟨ready,_,clock,memory,locals,readyCode,domain,_,_,globals,decl⟩ := evaluate_alloc_call_and_declaration state argument buffer
      (count * 32) args code (by omega) heap request (allocationEnd_within_heap buffer (count * 32) heapBound request)
    let entered := setVarHOLFinite (ofString "keys") (.val (.word buffer)) ready
    have atList : entered.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
        show ofString "keys" ≠ ofString "slots" by decide] using listLocal
    have atBuffer : entered.locals.lookup (ofString "keys") = some (.val (.word buffer)) := by
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
    have bound := evaluate_access_keys_initialized_bounded entered array count buffer input inputLength scratch frame ceiling inputLimit
      atList atBuffer enteredSlices atScratch atFrame (readyCode.trans code) enteredArena inputBound limitBound orderedFrame framePositive
      scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned (Nat.le_trans interval (by decide))
      (by
        change count.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ ready.clock
        rw [clock]
        exact Nat.le_sub_of_add_le (Nat.le_trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _) budget))
    rw [source_access_keys_allocation]
    change (let evaluated := evaluateHOLFiniteState state (.decCall (ofString "keys") .one (ofString "alloc") [argument] accessKeysInitialization); _) ∧ _
    rw [decl]
    cases run : evaluateHOLFiniteState entered accessKeysInitialization with
    | mk result post =>
      rw [run] at bound
      dsimp only at bound ⊢
      have enteredClock : entered.clock = ready.clock := rfl
      exact ⟨by omega,by omega,bound.2.2⟩
  · have rejected : ((33806089496 : BitVec 64) - buffer).toNat < (count * 32).toNat := by
      have bad : ¬(count * 32).toNat ≤ ((33806089496 : BitVec 64) - buffer).toNat := fun h => request (BitVec.le_def.mpr h)
      omega
    have failure := evaluate_alloc_request_failure_declaration state argument buffer (count * 32)
      (ofString "keys") .one accessKeysInitialization args code heap rejected
    have safe := evaluate_alloc_request_failure_declaration_no_timeout state argument buffer (count * 32)
      (ofString "keys") .one accessKeysInitialization args code heap rejected (by omega)
    rw [source_access_keys_allocation]
    change (let evaluated := evaluateHOLFiniteState state (.decCall (ofString "keys") .one (ofString "alloc") [argument] accessKeysInitialization); _) ∧ _
    dsimp only [argument] at failure safe ⊢
    exact ⟨by omega,by omega,safe⟩

#print axioms evaluate_access_keys_allocation_bounded
end InitECandidate.Runtime
