import InitECandidate.Runtime.StatelessWitnessMemFrame
import InitECandidate.Runtime.StatelessWitnessOffsetBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned actual witness suffix must have completed its real offset check.
The continuation retains the caller state and the accepted offset facts are
about that caller's actual memory, rather than assumed at the three-list entry. -/
theorem stateless_witness_checked_entry {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (offsets length : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atOffsets : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : s.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (run : evaluateHOLFiniteState s (statelessAt 35) = (some (.returned v),post)) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState ready (statelessAt 36) = (some (.returned v),post) ∧
      ready.locals = s.locals ∧ ready.memory = s.memory ∧ ready.globals = s.globals ∧
      ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
      SszCheckOffsetsReturned s offsets 3 12 length (.val (.word 0)) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) statelessWitnessCheckArguments =
      some [.val (.word offsets),.val (.word 3),.val (.word 12),.val (.word length)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [statelessWitnessCheckArguments,evalListHOLExact,evalHOLExact,atOffsets,atLength]
  rw [source_stateless_witness_check,evaluateHOLFiniteState_seq_line780] at run
  cases callRun : evaluateHOLFiniteState s statelessWitnessCheckCall with
  | mk result ready =>
    rw [callRun] at run
    cases result with
    | none =>
      obtain ⟨accepted,memory,globals,domain,locals⟩ := sszCheckOffsets_call_returned s statelessWitnessCheckArguments
        offsets 3 12 length args code (by decide) ready callRun
      have metadata := evaluateHOLFiniteState_metadata s statelessWitnessCheckCall
      rw [callRun] at metadata
      exact ⟨ready,run,locals,memory,globals,domain,metadata.1,accepted⟩
    | some r =>
      have noReturn := evaluate_discard_call_no_return s (ofString "ssz_check_offsets") statelessWitnessCheckArguments v
      change evaluateHOLFiniteState s (.call (some (none,none)) (ofString "ssz_check_offsets") statelessWitnessCheckArguments) = _ at callRun
      rw [callRun] at noReturn
      exact False.elim (noReturn (Prod.mk.inj run).1)

#print axioms stateless_witness_checked_entry
end InitECandidate.Runtime
