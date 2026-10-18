import InitECandidate.Runtime.AccessListAllocationBound
import InitECandidate.Runtime.AllocationReturnedGuard
import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned access-list record allocation has enough real heap capacity for
its actual count, independently of any conservative frame or future reserve. -/
theorem access_returned_allocation_capacity {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count records : BitVec 64) (value : ValueHOL 64)
    (listLocal : state.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word records)))
    (code : state.code = originalRuntimeCode)
    (within : records.toNat ≤ 33806089496) (aligned : records.toNat % 8 = 0)
    (countBound : count.toNat * 24 < 2^64)
    (run : evaluateHOLFiniteState state accessAfterSlices = (some (.returned value),final)) :
    records.toNat + count.toNat * 24 ≤ 33806089496 ∧
      (allocationEnd records (count * 24)).toNat = records.toNat + count.toNat * 24 ∧
      (allocationEnd records (count * 24)).toNat ≤ 33806089496 := by
  let argument : ExpHOL 64 := .panop .mul [.rfield 1 (.var .local (ofString "lst")),.const 24]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 24))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,listLocal,panOpHOL,valueIsWord,valueWord]
  rw [source_access_allocation] at run
  have request := alloc_declaration_returned_request state final argument records (count * 24) (ofString "recs") .one
    accessInitialized value args code heap run
  have product : (count * 24).toNat = count.toNat * 24 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 24 < 2^64; exact countBound)]
    rfl
  have interval := allocationGuard_sum_bound records (count * 24) within request
  rw [product] at interval
  have endpoint : (allocationEnd records (count * 24)).toNat = records.toNat + count.toNat * 24 := by
    rw [allocationEnd_aligned_toNat records (count * 24) (by rw [product]; exact interval) aligned
      (by rw [product]; omega),product]
  exact ⟨interval,endpoint,by rw [endpoint]; exact interval⟩

#print axioms access_returned_allocation_capacity
end InitECandidate.Runtime
