import InitECandidate.Runtime.TransactionRegistryAllocation
import InitECandidate.Runtime.TransactionRegistryHeap
import InitECandidate.Runtime.TransactionRegistryValueStore
import InitECandidate.Runtime.RollbackAllocationCopySeparation
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.StoreFourWords
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual alloc(32), st v,value prefix of the storage helpers consumes
one clock and reaches its continuation with a fresh value pointer and the
complete registry invariant. Allocation separation is derived from the world. -/
theorem TransactionRegistryWorld.allocate_storage_value {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer a b c d : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (space : pointer.toNat + 32 ≤ 33806089496) (clock : state.clock ≠ 0) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state
      (.decCall (ofString "v") .one (ofString "alloc") [.const 32]
        (.seq (.store (.var .local (ofString "v")) (.var .local (ofString "value"))) continuation)) =
      (let output := evaluateHOLFiniteState post continuation;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "v",state.locals.lookup (ofString "v"))}))) ∧
      TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count post ∧ post.clock = state.clock - 1 ∧
      post.locals.lookup (ofString "v") = some (.val (.word pointer)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd pointer 32))) ∧
      post.locals = (setVarHOLFinite (ofString "v") (.val (.word pointer)) state).locals ∧
      post.memory pointer = .word a ∧ post.memory (pointer + 8) = .word b ∧
      post.memory (pointer + 16) = .word c ∧ post.memory (pointer + 24) = .word d := by
  have pointerLe : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr (by change pointer.toNat ≤ 33806089496; omega)
  have gap : ((33806089496 : BitVec 64) - pointer).toNat = 33806089496 - pointer.toNat := by
    rw [BitVec.toNat_sub_of_le pointerLe]; rfl
  have request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer := by
    apply BitVec.le_def.mpr
    rw [gap]
    change 32 ≤ _
    omega
  have finish := allocationEnd_within_heap pointer 32 (by omega) request
  obtain ⟨allocated,_,midValid,ticks,memory,locals,heapNext,declaration⟩ := valid.allocate state widths tables fieldPointer ts journal snapshot count pointer 32
    (.const 32) rfl clock heap (by omega) request finish
  let entered := setVarHOLFinite (ofString "v") (.val (.word pointer)) allocated
  have enteredValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count entered := midValid.after_read rfl rfl rfl rfl rfl
  have atV : entered.locals.lookup (ofString "v") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atValue : entered.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,show ofString "v" ≠ ofString "value" from by decide] using valueLocal
  have domain : ∀ offset : Nat, offset < 32 → entered.memaddrs (pointer + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := Nat.mod_eq_of_lt (by omega)
    have address : (pointer + BitVec.ofNat 64 offset).toNat = pointer.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    exact enteredValid.journalWorld.heapDomain _ (by omega)
  have store := evaluate_store_four_words entered pointer a b c d (.var .local (ofString "v")) (.var .local (ofString "value"))
    atV atValue (by simpa using domain 0 (by decide)) (domain 8 (by decide)) (domain 16 (by decide)) (domain 24 (by decide))
  have enteredMemory : entered.memory = state.memory := memory
  have outside := valid.journalWorld.world.copy_separation_after_memory pointer heap enteredMemory
  have facts := valid.heap_facts pointer heap
  have postValid := enteredValid.after_four_words pointer a b c d space facts.2 outside
  let post := journalRecordPost32 entered pointer a b c d
  have readback := journalRecordPost32_fields entered pointer a b c d
  have callerLocals : post.locals = (setVarHOLFinite (ofString "v") (.val (.word pointer)) state).locals := by
    simp only [post,journalRecordPost32,sourceWriteWord,entered,setVarHOLFinite,locals]
  refine ⟨post,?_,postValid,ticks,atV,heapNext,callerLocals,readback.1,readback.2.1,readback.2.2.1,readback.2.2.2⟩
  intro continuation
  rw [declaration]
  change (let output := evaluateHOLFiniteState entered (.seq (.store (.var .local (ofString "v")) (.var .local (ofString "value"))) continuation); _) = _
  rw [evaluateHOLFiniteState_seq_line780,store]

#print axioms TransactionRegistryWorld.allocate_storage_value
end InitECandidate.Runtime
