import InitECandidate.Runtime.TransactionRuntimeWorld
import InitECandidate.Runtime.RollbackWorldLogicalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Read-only helpers, clock changes and temporary locals preserve the complete
transaction invariant; no snapshot local is required in the executing state. -/
theorem TransactionRuntimeWorld.after_read {F : Type}
    {widths : BitVec 64 → BitVec 64} {fieldPointer ts journal snapshot count : BitVec 64}
    {before after : PanSemStateFiniteExact 64 F}
    (valid : TransactionRuntimeWorld widths fieldPointer ts journal snapshot count before)
    (memory : after.memory = before.memory) (globals : after.globals = before.globals)
    (code : after.code = before.code) (domain : after.memaddrs = before.memaddrs) (endian : after.be = before.be) :
    TransactionRuntimeWorld widths fieldPointer ts journal snapshot count after := by
  have world : JournalRuntimeWorld widths (stateFreshTxRegistryAfter fieldPointer stateFreshTxAllTables ∅) journal snapshot count after := by
    refine ⟨valid.journalWorld.world.after_logical_frame memory globals code domain endian,
      valid.journalWorld.separated.after_read memory globals code domain endian,
      valid.journalWorld.journalBound,valid.journalWorld.journalAligned,valid.journalWorld.journalHeaders,?_,?_,?_,valid.journalWorld.supported⟩
    · intro address upper
      rw [domain]
      exact valid.journalWorld.heapDomain address upper
    · rw [globals]; exact valid.journalWorld.capacity
    · exact code.trans valid.journalWorld.code
  exact ⟨world,valid.fields.after_memory memory,by rw [globals]; exact valid.tsGlobal,
    valid.tsBound,valid.journalBeforeTs,valid.tableHeaders⟩

#print axioms TransactionRuntimeWorld.after_read
end InitECandidate.Runtime
