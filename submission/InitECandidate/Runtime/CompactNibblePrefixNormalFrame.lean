import InitECandidate.Runtime.CompactNibblePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the actual optional prefix write supplies its counter
and caller locals. An inaccessible destination cannot produce normal completion. -/
theorem compact_nibble_prefix_normal_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (out c0 odd : BitVec 64)
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atOdd : s.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (atCounter : s.locals.lookup (ofString "k") = some (.val (.word (0#64))))
    (run : evaluateHOLFiniteState s compactNibblePrefix = (none,post)) :
    post.locals.lookup (ofString "k") = some (.val (.word (if odd = 0 then 0 else 1))) ∧
      (∀ name, name ≠ ofString "k" → post.locals.lookup name = s.locals.lookup name) := by
  by_cases zero : odd = 0
  · have same : evaluateHOLFiniteState s compactNibblePrefix = (none,s) := by
      rw [source_compactNibble_prefix]
      simp [evaluateHOLFiniteState_ite,evalHOLExact,atOdd,Compiler.Encoders.Asm.wordCmpHOL,zero,
        evaluateHOLFiniteState_skip]
    have postEq := (Prod.mk.inj (same.symm.trans run)).2
    subst post
    exact ⟨by simpa [zero] using atCounter,fun _ _ => rfl⟩
  · by_cases domain : s.memaddrs (panByteAlignHOL out)
    · obtain ⟨actual,actualRun,_,counter,_,_,_,locals⟩ := evaluate_compactNibble_prefix s out c0 odd atOut atByte atOdd atCounter domain
      have postEq := (Prod.mk.inj (actualRun.symm.trans run)).2
      subst post
      exact ⟨counter,locals⟩
    · rw [source_compactNibble_prefix,evaluateHOLFiniteState_ite] at run
      simp [evalHOLExact,evalListHOLExact,atOdd,atOut,atByte,Compiler.Encoders.Asm.wordCmpHOL,
        show odd ≠ 0#64 from zero,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_storeByte,
        wordOpHOL,wordOp,valueIsWord,valueWord,panMemStoreByteWord8HOL,domain] at run

#print axioms compact_nibble_prefix_normal_frame
end InitECandidate.Runtime
