import InitECandidate.Runtime.MainNormalOutputBound
/-!
The actual `main` normal suffix is bounded by 65 ticks **without** any VM-memory assumption.

`runBounded_main_normal_suffix` needs the chain cell at `si+88` to be readable.  Here we remove both
that cell assumption and the domain assumption: either `si+88` is a memory address, in which case the
cell exists and is a `HolWordLab.word` (the only constructor), so the existing 65-tick bound applies
with that chain word; or `si+88` is not a memory address, in which case the actual
`serialize_result` argument load fails, the real `mainAt 24` declaration call returns
`some .error` without consuming a source tick, and the same 65-tick bound holds trivially.

Therefore the bound needs only the original code, the typed `out`/`root`/`succ`/`si` locals and the
clock: nothing about the VM's memory or about any preserved `si+88` cell.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- **The normal suffix after a returned VM call costs at most 65 ticks, with no domain or chain-cell
assumption.**  If `si+88` is readable the chain word is whatever the memory holds there; otherwise the
real argument load fails and the suffix is an immediate source error. -/
theorem runBounded_main_normal_suffix_no_domain {F : Type} (state : PanSemStateFiniteExact 64 F)
    (output root success si : BitVec 64)
    (atOutput : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (atRoot : state.locals.lookup (ofString "root") = some (.val (.word root)))
    (atSuccess : state.locals.lookup (ofString "succ") = some (.val (.word success)))
    (atSi : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (code : state.code = originalRuntimeCode) (budget : 65 ≤ state.clock) :
    RunBounded state (mainAt 24) 65 := by
  by_cases domain : state.memaddrs (si + (88#64))
  · obtain ⟨chain,cell⟩ : ∃ chain : BitVec 64, state.memory (si + (88#64)) = .word chain := by
      cases held : state.memory (si + (88#64)) with
      | word value => exact ⟨value,rfl⟩
    exact runBounded_main_normal_suffix state output root success si chain atOutput atRoot atSuccess atSi
      domain cell code budget
  · have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        mainNormalSerializeArguments = none := by
      rw [evalListHOLFinite_eq_toExact]
      simp [mainNormalSerializeArguments,evalListHOLExact,evalHOLExact,atOutput,atRoot,atSuccess,atSi,
        wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain]
    have run : evaluateHOLFiniteState state (mainAt 24) = (some .error,state) := by
      rw [source_main_normal_serialization,mainNormalSerialization]
      exact evaluateHOLFiniteState_decCall_args_none state (ofString "n") .one
        (ofString "serialize_result") mainNormalSerializeArguments mainNormalOutput arguments
    unfold RunBounded
    rw [run]
    refine ⟨?_,?_,?_⟩
    · simp
    · simp
    · simp

#print axioms runBounded_main_normal_suffix_no_domain
end InitECandidate.Runtime
