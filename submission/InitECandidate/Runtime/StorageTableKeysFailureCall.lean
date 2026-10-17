import InitECandidate.Runtime.HashNewBodyKeysFailure
import InitECandidate.Runtime.StorageTableFailedBodyCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The literal storage constructor exits in four clocks if its header succeeds
but its256-byte keys request is rejected. Assignment targets are irrelevant. -/
theorem evaluate_storage_table_keys_failure_call {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (destination : Option (VarKind × MlS))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (domain0 : state.memaddrs (pointer + 0)) (domain8 : state.memaddrs (pointer + 8))
    (domain16 : state.memaddrs (pointer + 16)) (domain24 : state.memaddrs (pointer + 24))
    (keysRejected : ((33806089496 : BitVec 64) - allocationEnd pointer 72).toNat < 256)
    (ticks : 4 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "htab_new") [.const 32,.const 8]);
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      output.2.clock = state.clock - 4 := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "key_len",.val (.word (32 : BitVec 64)))).update (ofString "cap",.val (.word (8 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have keyLocal : entry.locals.lookup (ofString "key_len") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "cap" ≠ ofString "key_len" from by decide]
  have capLocal : entry.locals.lookup (ofString "cap") = some (.val (.word (8 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have keySize : ((8 : BitVec 64) * allocationEnd 0 (32 : BitVec 64)).toNat = 256 := by decide
  have failure := evaluate_htabNew_body_keys_failure entry pointer 32 8 code (by change 3 ≤ state.clock - 1; omega)
    heap headerRequest headerFinish keyLocal capLocal domain0 domain8 domain16 domain24 (by rw [keySize]; exact keysRejected)
  exact evaluate_storage_table_failed_body_call state destination 3 code failure ticks

#print axioms evaluate_storage_table_keys_failure_call
end InitECandidate.Runtime
