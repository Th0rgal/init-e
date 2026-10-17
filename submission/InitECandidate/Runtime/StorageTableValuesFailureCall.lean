import InitECandidate.Runtime.HashNewBodyValuesFailure
import InitECandidate.Runtime.StorageTableFailedBodyCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The literal storage constructor exits in five clocks if its header and keys succeed
but its 64-byte values request is rejected. Assignment targets are irrelevant. -/
theorem evaluate_storage_table_values_failure_call {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (destination : Option (VarKind × MlS))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keysRequest : (256 : BitVec 64) ≤ (33806089496 : BitVec 64) - allocationEnd pointer 72)
    (keysFinish : (allocationEnd (allocationEnd pointer 72) 256).toNat ≤ 33806089496)
    (domain0 : state.memaddrs (pointer + 0)) (domain8 : state.memaddrs (pointer + 8))
    (domain16 : state.memaddrs (pointer + 16)) (domain24 : state.memaddrs (pointer + 24))
    (domain32 : state.memaddrs (pointer + 32))
    (valuesRejected : ((33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer 72) 256).toNat < 64)
    (ticks : 5 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [.const 32,.const 8]);
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      output.2.clock = state.clock - 5 := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32 : BitVec 64)))).update (ofString "cap",.val (.word (8 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cap" ≠ ofString "key_len" from by decide]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word (8 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have keySize : (8 : BitVec 64) * allocationEnd 0 (32 : BitVec 64) = 256 := by decide
  have valueSize : ((8 : BitVec 64) * 8).toNat = 64 := by decide
  have domains : ∀ offset ∈ ([0,8,16,24,32] : List Nat), entry.memaddrs (pointer + BitVec.ofNat 64 offset) := by
    intro offset member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact domain0
    · exact domain8
    · exact domain16
    · exact domain24
    · exact domain32
  have failure := evaluate_htabNew_body_values_failure entry pointer 32 8 code (by change 4 ≤ state.clock - 1; omega)
    heap headerRequest headerFinish (by rw [keySize]; exact keysRequest) (by rw [keySize]; exact keysFinish)
    keyLocal capLocal domains (by rw [keySize,valueSize]; exact valuesRejected)
  exact evaluate_storage_table_failed_body_call state destination 4 code failure ticks

#print axioms evaluate_storage_table_values_failure_call
end InitECandidate.Runtime
