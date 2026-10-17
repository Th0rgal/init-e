import InitECandidate.Runtime.JournalSetSource32
import InitECandidate.Runtime.HeaderLoadScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The successful original journal-capacity guard followed by the original
key-length header load reaches the allocator with no clock consumption. -/
theorem evaluate_journalSet_guard32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table count capacity : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word capacity)))
    (room : count.toNat < capacity.toNat)
    (domain : state.memaddrs (table + 0)) (cell : state.memory (table + 0) = .word (32 : BitVec 64)) :
    evaluateHOLFiniteState state journalSetAfterGet32 =
      (let output := evaluateHOLFiniteState
        (setVarHOLFinite (ofString "klen") (.val (.word (32 : BitVec 64))) state)
        (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32);
       (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (ofString "klen",state.locals.lookup (ofString "klen")))})) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap"))) =
      some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,countGlobal,capacityGlobal,Compiler.Encoders.Asm.wordCmpHOL]
    exact BitVec.lt_def.mpr room
  have guard : evaluateHOLFiniteState state
      (.ite (.cmp .notLower (.var .global (ofString "journal_n")) (.var .global (ofString "journal_cap")))
        (.call (some (none,none)) (ofString "trap_with") [.const 4]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite,condition]
    simp [evaluateHOLFiniteState_skip]
  unfold journalSetAfterGet32
  have scope := evaluate_header_load_scope state (ofString "klen") (ofString "t") table 0 32
    (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32)
    tableLocal domain cell
  exact evaluate_seq_none guard scope

#print axioms evaluate_journalSet_guard32
end InitECandidate.Runtime
