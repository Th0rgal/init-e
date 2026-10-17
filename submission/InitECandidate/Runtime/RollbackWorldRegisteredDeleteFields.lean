import InitECandidate.Runtime.RollbackWorldRegisteredDeleteFrame
import InitECandidate.Runtime.StateFreshTxFieldsRecordFrame
import InitECandidate.Runtime.HashTableDeleteCallRecordFrameSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Registered deletion derives its geometry and uniform cost from the world,
retaining the complete separated table family for the next operation. -/
theorem RollbackWorld.registered_delete_bounded_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ts fieldPointer : BitVec 64)
    (fields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (ticks : 2 ^ 42 ≤ state.clock)
    (tableArgument keyArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot count post ∧ RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + 2 ^ 42 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧ StateFreshTxFields ts fieldPointer stateFreshTxAllTables post := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  obtain ⟨post,run,nextWorld,nextSep,cost,remaining⟩ := RollbackWorld.delete_call_preserves_separation state widths tables
    table pointer keys stride capacity used values order reverse items key bits supported ready small large tableArgument keyArgument args aligned words bytes (by omega)
    journal snapshot count world member separated
  have usedBefore := ready.live.arrays.usedBefore
  have orderBefore := ready.live.arrays.orderBefore
  have endBound := ready.live.arrays.endBound
  have headerValues := ready.live.arrays.headerValues
  have valuesBefore := ready.live.arrays.valuesBefore
  have start : (ts + (8 : BitVec 64)).toNat = ts.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change ts.toNat + 8 < 2 ^ 64; omega)]
    rfl
  obtain ⟨checked,checkedRun,_,recordFrame,_,_,_,globals,_,_,_⟩ :=
    ready.delete_call_supported_with_record_frame state (widths table) table pointer keys stride capacity used values order reverse items key bits supported
      tableArgument keyArgument args aligned words bytes (by omega) (ts + 8) 2 (by omega) (Or.inr (by omega))
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  refine ⟨post,run,nextWorld,nextSep,by omega,remaining,by rw [same]; exact globals,?_⟩
  rw [same]
  exact fields.after_two_record_frame recordFrame

#print axioms RollbackWorld.registered_delete_bounded_fields
end InitECandidate.Runtime
