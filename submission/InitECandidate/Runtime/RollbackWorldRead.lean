import InitECandidate.Runtime.RollbackWorldFrame
import InitECandidate.Runtime.RollbackPhysicalSeparated
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Read-only calls and local scopes retain the world when the saved snapshot
binding is restored, regardless of the other temporary local variables. -/
theorem RollbackWorld.after_read {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {before after : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count before)
    (memory : after.memory = before.memory) (globals : after.globals = before.globals)
    (code : after.code = before.code) (domain : after.memaddrs = before.memaddrs) (endian : after.be = before.be)
    (snapshotLocal : after.locals.lookup (ofString "snap") = before.locals.lookup (ofString "snap")) :
    RollbackWorld widths tables journal snapshot count after := by
  exact world.after_frame (Nat.le_refl _)
    (by rw [globals]; exact world.counter) (snapshotLocal.trans world.snapshotLocal)
    (by rw [globals]; exact world.journalGlobal) domain
    (by intro index inside offset member; exact congrFun memory _)
    (fun table member => (world.ready table member).after_read memory globals code domain endian)

/-- Physical separation ignores temporary locals and source clock changes. -/
theorem RollbackPhysicalSeparated.after_read {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {before after : PanSemStateFiniteExact 64 F}
    (separated : RollbackPhysicalSeparated widths tables before)
    (memory : after.memory = before.memory) (globals : after.globals = before.globals)
    (code : after.code = before.code) (domain : after.memaddrs = before.memaddrs) (endian : after.be = before.be) :
    RollbackPhysicalSeparated widths tables after := by
  apply separated.of_footprint_subset
  intro table member address inside
  obtain ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,ready,region⟩ := inside
  exact ⟨pointer,keys,stride,capacity,used,values,order,orderPos,items,bits,
    ready.after_read after before (widths table) table keys stride capacity used values order orderPos items bits pointer
      memory.symm globals.symm code.symm domain.symm endian.symm,region⟩

#print axioms RollbackWorld.after_read
#print axioms RollbackPhysicalSeparated.after_read
end InitECandidate.Runtime
