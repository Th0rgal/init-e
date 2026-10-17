import InitECandidate.Runtime.RollbackWorldJournalSetLogicalSnapshot
import InitECandidate.Runtime.OriginalJournalSetCode
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original jset call has a uniform all-outcome bound. Its callee
has only the declared t/key/value locals; snap remains purely logical. -/
theorem rollback_world_jset_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state))
    (separated : RollbackPhysicalSeparated widths tables state)
    (member : table ∈ tables) (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 73 + 1 ≤ state.clock)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).1 ≠ some .timeOut ∧
      state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2.clock + (2 ^ 73 + 1) ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  let logicalEntry := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) entry
  have entryWorld : RollbackWorld widths tables journal snapshot count logicalEntry := world.after_read rfl rfl rfl rfl rfl (by
    simp [logicalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  have entrySep : RollbackPhysicalSeparated widths tables entry := separated.after_read rfl rfl rfl rfl rfl
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "value" ≠ ofString "t" from by decide,show ofString "key" ≠ ofString "t" from by decide]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "value" ≠ ofString "key" from by decide]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := jset_body_bounded_logical_snapshot entryWorld entrySep table key value member supported t k v keyAligned keyWords keyBytes
    (by change 2 ^ 73 ≤ state.clock - 1; omega) journalBound journalAligned journalHeaders heapDomain capacityGlobal
  have installed : state.code.lookup (ofString "jset") = some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_jset,.one) := by
    rw [code]; exact originalRuntimeCode_journalSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "jset") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_jset) table key value (by decide) (by decide) (by decide) installed
  have noTimeout := evaluate_discard_call_body_no_timeout state (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).2 (ofString "jset")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)] (sourceFunctionBody Guest.guestFn_jset) callee .one
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).1 arguments lookup (by omega) rfl bounded.2.2.2
  have clock := evaluate_discard_call_body_clock state (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).2 (ofString "jset")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)] (sourceFunctionBody Guest.guestFn_jset) callee .one
    (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).1 arguments lookup (by omega) rfl
  have entryClock : entry.clock = state.clock - 1 := rfl
  refine ⟨noTimeout,?_,?_⟩
  · rw [clock]; omega
  · rw [clock]; omega

#print axioms rollback_world_jset_call_bounded
end InitECandidate.Runtime
