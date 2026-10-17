import InitECandidate.Runtime.RollbackWorldJournalDeleteAfterGetSuccess
import InitECandidate.Runtime.JournalDeleteLookupSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful return from the full original jset body appends one record
and preserves the separated rollback world on the actual exit state. -/
theorem RollbackWorld.jdel_body_success {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key : BitVec 64) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 ≤ state.clock)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).1 = some (.returned returnedValue)) :
    ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧
      RollbackWorld widths tables journal snapshot next
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2) ∧
      RollbackPhysicalSeparated widths tables (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2 := by
  obtain ⟨pointer,keys,stride,capacity,used,values,order,reverse,items,bits,ready,_,_⟩ := world.ready table member
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have := ready.live.arrays.usedBefore
    have := ready.live.arrays.orderBefore
    have := ready.live.arrays.endBound
    omega
  have widthBound : (widths table).toNat ≤ 52 := by
    rcases supported with same | same | same <;> rw [same] <;> decide
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨present,oldValue,middle,_,midReady,oldLocal,cost,remaining,memory,globals,code,domain,endian,locals,run⟩ :=
    ready.jdel_lookup_supported state (widths table) table pointer keys stride capacity used values order reverse items key bits supported args keyAligned keyWords keyBytes (by omega)
  have midWorld : RollbackWorld widths tables journal snapshot count middle := world.after_read memory globals code domain endian
    (locals (ofString "snap") (by decide))
  have midSep := separated.after_read memory globals code domain endian
  have suffixSuccess : (evaluateHOLFiniteState middle journalDeleteAfterGet32).1 = some (.returned returnedValue) :=
    (congrArg Prod.fst run).symm.trans success
  obtain ⟨next,counts,valid,apart⟩ := midWorld.journal_delete_after_get_success midSep table member pointer key (widths table)
    ((locals (ofString "key") (by decide)).trans keyLocal) midReady.live.arrays.code (by omega)
    midReady.live.frontier.heap midReady.live.frontier.bounded midReady.live.frontier.aligned keyAligned
    (by simpa only [domain] using keyWords) (by simpa only [domain] using keyBytes)
    present oldValue rfl supported ((locals (ofString "t") (by decide)).trans tableLocal) oldLocal
    journalBound journalAligned journalHeaders
    (by intro address upper; rw [domain]; exact heapDomain address upper) (by rw [globals]; exact capacityGlobal) returnedValue suffixSuccess
  rw [run]
  exact ⟨next,counts,valid.after_logical_frame rfl rfl rfl rfl rfl,apart.after_read rfl rfl rfl rfl rfl⟩

#print axioms RollbackWorld.jdel_body_success
end InitECandidate.Runtime
