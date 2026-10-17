import InitECandidate.Runtime.JournalSetGuardWidth
import InitECandidate.Runtime.JournalDeleteGuardWidth
import InitECandidate.Runtime.AllocationFailureDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Once the original key-length scope is entered, rejected allocation
terminates before the journal copy continuation within two source clocks. -/
theorem evaluate_journal_key_allocation_failure_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength pointer : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (failure : ((33806089496 : BitVec 64) - pointer).toNat < keyLength.toNat) :
    (evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] continuation)).1 ≠ none ∧
      (evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] continuation)).2.clock = state.clock - 2 := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "klen")] = some [.val (.word keyLength)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,klen]
  exact evaluate_alloc_request_failure_declaration state (.var .local (ofString "klen")) pointer keyLength
    (ofString "kc") .one continuation arguments code heap failure

theorem evaluate_journal_set_allocation_failure_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer count capacity : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word capacity)))
    (room : count.toNat < capacity.toNat)
    (domain : state.memaddrs (table + 0)) (cell : state.memory (table + 0) = .word keyLength)
    (failure : ((33806089496 : BitVec 64) - pointer).toNat < keyLength.toNat) :
    (evaluateHOLFiniteState state journalSetAfterGet32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalSetAfterGet32).2.clock = state.clock - 2 := by
  let entered := setVarHOLFinite (ofString "klen") (.val (.word keyLength)) state
  have klen : entered.locals.lookup (ofString "klen") = some (.val (.word keyLength)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have rejected := evaluate_journal_key_allocation_failure_width entered keyLength pointer journalSetCopy32 code heap klen failure
  rw [evaluate_journalSet_guard_width state keyLength table count capacity t countGlobal capacityGlobal room domain cell]
  dsimp only
  exact rejected

#print axioms evaluate_journal_set_allocation_failure_width
theorem evaluate_journal_delete_allocation_failure_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer count capacity : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word capacity)))
    (room : count.toNat < capacity.toNat)
    (domain : state.memaddrs (table + 0)) (cell : state.memory (table + 0) = .word keyLength)
    (failure : ((33806089496 : BitVec 64) - pointer).toNat < keyLength.toNat) :
    (evaluateHOLFiniteState state journalDeletePresent32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalDeletePresent32).2.clock = state.clock - 2 := by
  let entered := setVarHOLFinite (ofString "klen") (.val (.word keyLength)) state
  have klen : entered.locals.lookup (ofString "klen") = some (.val (.word keyLength)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have rejected := evaluate_journal_key_allocation_failure_width entered keyLength pointer journalDeleteCopy32 code heap klen failure
  rw [evaluate_journalDelete_guard_width state keyLength table count capacity t countGlobal capacityGlobal room domain cell]
  dsimp only
  exact rejected

#print axioms evaluate_journal_delete_allocation_failure_width
#print axioms evaluate_journal_key_allocation_failure_width
end InitECandidate.Runtime
