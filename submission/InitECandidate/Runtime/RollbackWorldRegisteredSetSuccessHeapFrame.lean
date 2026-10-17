import InitECandidate.Runtime.HashSetAllPlansSuccessHeapFrame
import InitECandidate.Runtime.RollbackWorldRegisteredSetBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful actual registered set calls preserve every non-heap global,
including journal capacity, without assuming that growth allocation is safe. -/
theorem RollbackWorld.registered_set_success_heap_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (ticks : 2 ^ 72 + 1 ≤ state.clock)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).1 = none) :
    HeapGlobalsFrame state (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument])).2 := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,small,large⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have ceiling := hashSetRegistryCost_le_ceiling capacity (widths table) items capacityBound supported (Nat.le_of_lt ready.live.arrays.room)
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "value" ≠ ofString "t" from by decide,show ofString "key" ≠ ofString "t" from by decide]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "value" ≠ ofString "key" from by decide]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryReady := ready.after_read state entry (widths table) table keys stride capacity used values order reverse items bits pointer rfl rfl rfl rfl rfl
  have preserves : ∀ returnedValue, (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).1 = some (.returned returnedValue) →
      HeapGlobalsFrame entry (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set)).2 := by
    intro returnedValue returned
    exact entryReady.set_body_all_plans_success_heap_frame entry (widths table) table pointer keys stride capacity used values order reverse items key value bits supported small large
      (by change hashSetRegistryCost capacity (widths table) items ≤ state.clock - 1; omega) heapDomain t k v aligned words bytes returnedValue returned
  have installed : state.code.lookup (ofString "htab_set") = some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_htab_set,.one) := by
    rw [ready.live.arrays.code]; exact originalRuntimeCode_hashSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "htab_set") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_htab_set) table key value (by decide) (by decide) (by decide) installed
  simp only [evaluateHOLFiniteState_call,args] at success ⊢
  rw [lookup] at success ⊢
  dsimp only at success ⊢
  have clock : state.clock ≠ 0 := by omega
  simp only [if_neg clock] at success ⊢
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_htab_set) with
  | mk result post =>
      rw [bodyRun] at success preserves
      cases result with
      | none => cases success
      | some result =>
          cases result with
          | returned returnedValue =>
              dsimp only at success ⊢
              split at success
              · rename_i goodShape
                simp only [goodShape,if_true]
                exact preserves returnedValue rfl
              · cases success
          | _ => cases success

#print axioms RollbackWorld.registered_set_success_heap_frame
end InitECandidate.Runtime
