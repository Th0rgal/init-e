import InitECandidate.Runtime.RollbackWorldJournalDeleteLogicalSnapshot
import InitECandidate.Runtime.OriginalJournalDeleteCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original jdel call has a uniform all-outcome bound. Its callee
has only the declared t/key locals; snap remains purely logical. -/
theorem rollback_world_jdel_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state))
    (separated : RollbackPhysicalSeparated widths tables state)
    (member : table ∈ tables) (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 + 1 ≤ state.clock)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).1 ≠ some .timeOut ∧
      state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).2.clock + (2 ^ 43 + 1) ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  let logicalEntry := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) entry
  have entryWorld : RollbackWorld widths tables journal snapshot count logicalEntry := world.after_read rfl rfl rfl rfl rfl (by
    simp [logicalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  have entrySep : RollbackPhysicalSeparated widths tables entry := separated.after_read rfl rfl rfl rfl rfl
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "key" ≠ ofString "t" from by decide]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := jdel_body_bounded_logical_snapshot entryWorld entrySep table key member supported t k keyAligned keyWords keyBytes
    (by change 2 ^ 43 ≤ state.clock - 1; omega) journalBound journalAligned journalHeaders heapDomain capacityGlobal
  have installed : state.code.lookup (ofString "jdel") = some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_jdel,.one) := by
    rw [code]; exact originalRuntimeCode_journalDelete_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "jdel") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_jdel) table key (by decide) installed
  have noTimeout := evaluate_discard_call_body_no_timeout state (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).2 (ofString "jdel")
    [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_jdel) callee .one
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).1 arguments lookup (by omega) rfl bounded.2.2.2
  have clock := evaluate_discard_call_body_clock state (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).2 (ofString "jdel")
    [tableArgument,keyArgument] [.val (.word table),.val (.word key)] (sourceFunctionBody Guest.guestFn_jdel) callee .one
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).1 arguments lookup (by omega) rfl
  have entryClock : entry.clock = state.clock - 1 := rfl
  refine ⟨noTimeout,?_,?_⟩
  · rw [clock]; omega
  · rw [clock]; omega

#print axioms rollback_world_jdel_call_bounded
end InitECandidate.Runtime
