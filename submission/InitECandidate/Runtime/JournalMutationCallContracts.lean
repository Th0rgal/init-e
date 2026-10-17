import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.RollbackWorldJournalSetCallSuccess
import InitECandidate.Runtime.RollbackWorldJournalDeleteCallSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Combined clock, terminal, metadata and successful-world contract for the actual mutation call. -/
theorem rollback_world_jset_call_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 73 + 1) ∧ output.2.clock ≤ state.clock ∧
      output.2.code = state.code ∧ output.2.memaddrs = state.memaddrs ∧ output.2.be = state.be ∧
      (output.1 = none → RollbackWorld widths tables journal snapshot (count + 1)
        (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) output.2) ∧ RollbackPhysicalSeparated widths tables output.2) := by
  have bounded := rollback_world_jset_call_bounded state widths tables journal snapshot count table key value world separated member supported tableArgument keyArgument valueArgument arguments keyAligned keyWords keyBytes ticks journalBound journalAligned journalHeaders heapDomain capacityGlobal code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,metadata.1,metadata.2.1,metadata.2.2.1,?_⟩
  intro success
  exact rollback_world_jset_call_success state widths tables journal snapshot count table key value world separated member supported tableArgument keyArgument valueArgument arguments keyAligned keyWords keyBytes ticks journalBound journalAligned journalHeaders heapDomain capacityGlobal code success

#print axioms rollback_world_jset_call_contract

/-- Combined clock, terminal, metadata and successful-world contract for the actual mutation call. -/
theorem rollback_world_jdel_call_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 43 + 1) ∧ output.2.clock ≤ state.clock ∧
      output.2.code = state.code ∧ output.2.memaddrs = state.memaddrs ∧ output.2.be = state.be ∧
      (output.1 = none → ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧
        RollbackWorld widths tables journal snapshot next
          (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) output.2) ∧ RollbackPhysicalSeparated widths tables output.2) := by
  have bounded := rollback_world_jdel_call_bounded state widths tables journal snapshot count table key world separated member supported tableArgument keyArgument arguments keyAligned keyWords keyBytes ticks journalBound journalAligned journalHeaders heapDomain capacityGlobal code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,metadata.1,metadata.2.1,metadata.2.2.1,?_⟩
  intro success
  exact rollback_world_jdel_call_success state widths tables journal snapshot count table key world separated member supported tableArgument keyArgument arguments keyAligned keyWords keyBytes ticks journalBound journalAligned journalHeaders heapDomain capacityGlobal code success

#print axioms rollback_world_jdel_call_contract

end InitECandidate.Runtime
