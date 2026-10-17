import InitECandidate.Runtime.JournalSetSource32
import InitECandidate.Runtime.JournalDeleteSource32
import InitECandidate.Runtime.TrapCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A full journal executes the original trap call and never enters the
allocation continuation, at any clock including zero. -/
theorem evaluate_journal_overflow32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count capacity trapCode : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word capacity)))
    (full : capacity.toNat ≤ count.toNat) :
    evaluateHOLFiniteState state
      (.seq (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
        (.call (some (none,none)) (ofString "trap_with") [.const trapCode]) .skip) continuation) =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const trapCode]) := by
  have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) = some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,countGlobal,capacityGlobal,Compiler.Encoders.Asm.wordCmpHOL]
    exact BitVec.le_def.mpr full
  have selected : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
        (.call (some (none,none)) (ofString "trap_with") [.const trapCode]) .skip) =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const trapCode]) := by
    rw [evaluateHOLFiniteState_ite,condition]
    rfl
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const trapCode] =
      some [.val (.word trapCode)] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  have terminal := evaluate_trap_call_terminal state (.const trapCode) trapCode code arguments
  rw [evaluateHOLFiniteState_seq]
  dsimp only
  rw [fixClockHOLFinite_evaluateState,selected]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const trapCode]) with
  | mk result post =>
    rw [run] at terminal
    cases result with
    | none => exact False.elim (terminal rfl)
    | some result => rfl

theorem evaluate_journal_set_overflow32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word capacity)))
    (full : capacity.toNat ≤ count.toNat) :
    (evaluateHOLFiniteState state journalSetAfterGet32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalSetAfterGet32).2.clock = state.clock - 1 := by
  have run : evaluateHOLFiniteState state journalSetAfterGet32 =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 4]) :=
    evaluate_journal_overflow32 state count capacity 4 _ code countGlobal capacityGlobal full
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 4] =
      some [.val (.word (4 : BitVec 64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  rw [run]
  exact ⟨evaluate_trap_call_terminal state (.const 4) 4 code arguments,
    evaluate_trap_call_clock state (.const 4) 4 code arguments⟩

#print axioms evaluate_journal_set_overflow32
theorem evaluate_journal_delete_overflow32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count capacity : BitVec 64) (code : state.code = originalRuntimeCode)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word capacity)))
    (full : capacity.toNat ≤ count.toNat) :
    (evaluateHOLFiniteState state journalDeletePresent32).1 ≠ none ∧
      (evaluateHOLFiniteState state journalDeletePresent32).2.clock = state.clock - 1 := by
  have run : evaluateHOLFiniteState state journalDeletePresent32 =
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const 5]) :=
    evaluate_journal_overflow32 state count capacity 5 _ code countGlobal capacityGlobal full
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 5] =
      some [.val (.word (5 : BitVec 64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
  rw [run]
  exact ⟨evaluate_trap_call_terminal state (.const 5) 5 code arguments,
    evaluate_trap_call_clock state (.const 5) 5 code arguments⟩

#print axioms evaluate_journal_delete_overflow32
#print axioms evaluate_journal_overflow32
end InitECandidate.Runtime
