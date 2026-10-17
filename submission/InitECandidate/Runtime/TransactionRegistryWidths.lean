import InitECandidate.Runtime.TransactionRegistryWorld
import InitECandidate.Runtime.RollbackWorldHeaderFrontier
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Width maps need agree only on live registered table identities. Every
saved undo record refers to such an identity, so its key extent is retained. -/
theorem RollbackWorld.congr_widths {F : Type}
    {widths nextWidths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (agree : ∀ table ∈ tables, nextWidths table = widths table) :
    RollbackWorld nextWidths tables journal snapshot count state := by
  refine ⟨world.counter,world.snapshotLocal,world.journalGlobal,world.capacity,?_,world.references,?_,world.layout⟩
  · refine ⟨world.records.1,?_⟩
    intro index inside table key tableCell keyCell
    rw [agree table (world.references index inside table tableCell)]
    exact world.records.2 index inside table key tableCell keyCell
  · intro table member
    unfold RollbackTableReady
    rw [agree table member]
    exact world.ready table member

theorem RollbackPhysicalSeparated.congr_widths {F : Type}
    {widths nextWidths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {state : PanSemStateFiniteExact 64 F}
    (apart : RollbackPhysicalSeparated widths tables state)
    (agree : ∀ table ∈ tables, nextWidths table = widths table) :
    RollbackPhysicalSeparated nextWidths tables state := by
  intro table member other otherMember different address inside otherInside
  have first : rollbackTableFootprint widths table state address := by
    simpa only [rollbackTableFootprint,agree table member] using inside
  have second : rollbackTableFootprint widths other state address := by
    simpa only [rollbackTableFootprint,agree other otherMember] using otherInside
  exact apart table member other otherMember different address first second

/-- Changing widths away from the registry leaves the complete transaction
invariant in exactly the same executing state. -/
theorem TransactionRegistryWorld.congr_widths {F : Type}
    {widths nextWidths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (agree : ∀ table ∈ tables, nextWidths table = widths table) :
    TransactionRegistryWorld nextWidths tables fieldPointer ts journal snapshot count state := by
  refine ⟨⟨valid.journalWorld.world.congr_widths agree,valid.journalWorld.separated.congr_widths agree,
    valid.journalWorld.journalBound,valid.journalWorld.journalAligned,valid.journalWorld.journalHeaders,valid.journalWorld.heapDomain,
    valid.journalWorld.capacity,valid.journalWorld.code,?_⟩,valid.fields,valid.tsGlobal,valid.tsBound,valid.journalBeforeTs,
    valid.fieldRegistry,valid.tableHeaders⟩
  intro table member
  rw [agree table member]
  exact valid.journalWorld.supported table member

def withTableWidth (widths : BitVec 64 → BitVec 64) (pointer width table : BitVec 64) : BitVec 64 :=
  if table = pointer then width else widths table

/-- No registered header is the heap frontier: live table headers occupy at
least72 bytes below it. Thus a future constructor can choose its key width. -/
theorem TransactionRegistryWorld.with_fresh_width {F : Type}
    {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {fieldPointer ts journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (pointer width : BitVec 64)
    (heap : state.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr") = some (.val (.word pointer))) :
    TransactionRegistryWorld (withTableWidth widths pointer width) tables fieldPointer ts journal snapshot count state := by
  apply valid.congr_widths
  intro table member
  have bound := valid.journalWorld.world.registered_header_before_frontier pointer table member heap
  have different : table ≠ pointer := by intro same; rw [same] at bound; omega
  simp only [withTableWidth,if_neg different]

#print axioms RollbackWorld.congr_widths
#print axioms RollbackPhysicalSeparated.congr_widths
#print axioms TransactionRegistryWorld.congr_widths
#print axioms TransactionRegistryWorld.with_fresh_width
end InitECandidate.Runtime
