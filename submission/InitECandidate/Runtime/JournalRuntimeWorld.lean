import InitECandidate.Runtime.JournalMutationCallContracts
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Stable journal state for repeated original mutation calls. Snapshot is
logical; the full reserved buffer, capacity and code survive successful calls. -/
structure JournalRuntimeWorld {F : Type} (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  world : RollbackWorld widths tables journal snapshot count (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state)
  separated : RollbackPhysicalSeparated widths tables state
  journalBound : journal.toNat + 524288 * 32 ≤ 33806089496
  journalAligned : journal.toNat % 8 = 0
  journalHeaders : ∀ table ∈ tables, journal.toNat + 524288 * 32 ≤ table.toNat
  heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address
  capacity : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64)))
  code : state.code = originalRuntimeCode
  supported : ∀ table ∈ tables, widths table = 20 ∨ widths table = 32 ∨ widths table = 52

/-- Reusable full invariant and uniform bound for the actual original mutation call. -/
theorem JournalRuntimeWorld.jset_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (valid : JournalRuntimeWorld widths tables journal snapshot count state)
    (member : table ∈ tables)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 73 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 73 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → JournalRuntimeWorld widths tables journal snapshot (count + 1) output.2) := by
  have contract := rollback_world_jset_call_contract state widths tables journal snapshot count table key value valid.world valid.separated member (valid.supported table member) tableArgument keyArgument valueArgument arguments keyAligned keyWords keyBytes ticks valid.journalBound valid.journalAligned valid.journalHeaders valid.heapDomain valid.capacity valid.code
  refine ⟨contract.1,contract.2.1,contract.2.2.1,?_⟩
  intro success
  obtain ⟨world,apart,capacity⟩ := contract.2.2.2.2.2.2 success
  refine ⟨world,apart,valid.journalBound,valid.journalAligned,valid.journalHeaders,?_,capacity.trans valid.capacity,contract.2.2.2.1.trans valid.code,valid.supported⟩
  intro address upper
  rw [contract.2.2.2.2.1]
  exact valid.heapDomain address upper

#print axioms JournalRuntimeWorld.jset_call

/-- Reusable full invariant and uniform bound for the actual original mutation call. -/
theorem JournalRuntimeWorld.jdel_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key : BitVec 64)
    (valid : JournalRuntimeWorld widths tables journal snapshot count state)
    (member : table ∈ tables)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 + 1 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument]);
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + (2 ^ 43 + 1) ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧ JournalRuntimeWorld widths tables journal snapshot next output.2) := by
  have contract := rollback_world_jdel_call_contract state widths tables journal snapshot count table key valid.world valid.separated member (valid.supported table member) tableArgument keyArgument arguments keyAligned keyWords keyBytes ticks valid.journalBound valid.journalAligned valid.journalHeaders valid.heapDomain valid.capacity valid.code
  refine ⟨contract.1,contract.2.1,contract.2.2.1,?_⟩
  intro success
  obtain ⟨next,counts,world,apart,capacity⟩ := contract.2.2.2.2.2.2 success
  refine ⟨next,counts,world,apart,valid.journalBound,valid.journalAligned,valid.journalHeaders,?_,capacity.trans valid.capacity,contract.2.2.2.1.trans valid.code,valid.supported⟩
  intro address upper
  rw [contract.2.2.2.2.1]
  exact valid.heapDomain address upper

#print axioms JournalRuntimeWorld.jdel_call

end InitECandidate.Runtime
