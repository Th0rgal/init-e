import InitECandidate.Runtime.WitnessExtensionSource
import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.ProgBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_unwind_hash_zero {F : Type} (s : PanSemStateFiniteExact 64 F) (hash : BitVec 64)
    (atHash : s.locals.lookup (ofString "hash")=some (.val (.word hash)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word (0#64)))) :
    evaluateHOLFiniteState s witnessUnwindHashStore=(none,s) := by
  rw [source_witness_unwind_hash_store]
  by_cases zero : hash=0
  · subst hash
    simp [evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,atHash,atResult,wordOpHOL,wordOp,
      valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip,
      show AndOp.and (0#64) (AndOp.and (0#64) (18446744073709551615#64)) = (0#64) from by decide,
      show AndOp.and (1#64) (AndOp.and (0#64) (18446744073709551615#64)) = (0#64) from by decide]
  · simp [evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,atHash,atResult,wordOpHOL,wordOp,
      valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,show hash ≠ 0#64 from zero,evaluateHOLFiniteState_skip,
      show AndOp.and (0#64) (AndOp.and (0#64) (18446744073709551615#64)) = (0#64) from by decide,
      show AndOp.and (1#64) (AndOp.and (0#64) (18446744073709551615#64)) = (0#64) from by decide]

theorem witness_unwind_hash_store_frame {F : Type} (s : PanSemStateFiniteExact 64 F) (result hash : BitVec 64)
    (atHash : s.locals.lookup (ofString "hash")=some (.val (.word hash)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (code : s.code=originalRuntimeCode) :
    (evaluateHOLFiniteState s witnessUnwindHashStore).2.locals=s.locals ∧
      (evaluateHOLFiniteState s witnessUnwindHashStore).2.globals=s.globals ∧
      ∀ watched : BitVec 64, result=0 ∨ watched ≠ result+24 →
        (evaluateHOLFiniteState s witnessUnwindHashStore).2.memory watched=s.memory watched := by
  have globalFrame : OriginalGlobalsFrame witnessUnwindHashStore := by
    apply originalGlobalsFrame_leaf
    intro watched
    rw [source_witness_unwind_hash_store]
    rfl
  refine ⟨?_,globalFrame s code,?_⟩
  · rw [source_witness_unwind_hash_store,evaluateHOLFiniteState_ite]
    split
    · split
      · rw [evaluateHOLFiniteState_skip]
      · exact (evaluate_store_control_frame s _ _).2.1
    · rfl
  · intro watched separate
    rcases separate with zero | different
    · subst result
      rw [witness_unwind_hash_zero s hash atHash atResult]
    · have wordFrame := evaluate_wordStore_memory_frame s
        (.op .add [.var .local (ofString "result"),.const 24]) (.var .local (ofString "hash")) (result+24) watched
        (by simp [evalHOLExact,evalListHOLExact,atResult,wordOpHOL,wordOp,valueIsWord,valueWord])
        (by intro parsed actual; exact ⟨hash,by simpa [evalHOLExact,atHash] using actual.symm⟩) different
      rw [source_witness_unwind_hash_store,evaluateHOLFiniteState_ite]
      split
      · split
        · rw [evaluateHOLFiniteState_skip]
        · exact wordFrame
      · rfl

theorem witness_unwind_hash_store_bounded : ProgBounded witnessUnwindHashStore 0 := by
  apply ProgBounded.straight
  rw [source_witness_unwind_hash_store]
  rfl

#print axioms witness_unwind_hash_zero
#print axioms witness_unwind_hash_store_frame
#print axioms witness_unwind_hash_store_bounded
end InitECandidate.Runtime
