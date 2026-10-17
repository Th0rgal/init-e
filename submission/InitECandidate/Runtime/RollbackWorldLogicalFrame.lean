import InitECandidate.Runtime.RollbackWorldRead
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Return and scope cleanup may replace caller locals; reinstalling the
logical snapshot retains the world when all nonlocal invariants are framed. -/
theorem RollbackWorld.after_logical_frame {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {before after : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count before)
    (memory : after.memory = before.memory) (globals : after.globals = before.globals)
    (code : after.code = before.code) (domain : after.memaddrs = before.memaddrs) (endian : after.be = before.be) :
    RollbackWorld widths tables journal snapshot count (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) after) := by
  apply world.after_read (after := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) after) memory globals code domain endian
  simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using world.snapshotLocal.symm

#print axioms RollbackWorld.after_logical_frame
end InitECandidate.Runtime
