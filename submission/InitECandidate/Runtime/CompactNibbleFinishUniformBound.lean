import InitECandidate.Runtime.KeyToNibblesUniformCallBound
import InitECandidate.Runtime.CompactNibbleFinish
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual compact decoder's conversion call needs no byte-access success
premises. Its source and destination pointers may have arbitrary alignment. -/
theorem runBounded_compact_nibble_conversion {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length out initial : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (atInitial : s.locals.lookup (ofString "k") = some (.val (.word initial)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 4 ≤ s.clock) :
    RunBounded s compactNibbleConversion ((length - 1).toNat / 4 + 4) := by
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) compactNibbleArguments =
      some [.val (.word (pointer + 1)),.val (.word (length - 1)),.val (.word (out + initial))] := by
    simp [compactNibbleArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atLength,atOut,atInitial,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_compactNibble_conversion]
  exact evaluate_keyToNibbles_call_uniform_bounded s _ _ _ (pointer + 1) (out + initial) (length - 1) small code args ticks

/-- Adding the original structured return costs no further source clock. -/
theorem runBounded_compact_nibble_finish {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length out initial : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (atInitial : s.locals.lookup (ofString "k") = some (.val (.word initial)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 4 ≤ s.clock) :
    RunBounded s compactNibbleFinish ((length - 1).toNat / 4 + 4) := by
  rw [source_compactNibble_finish]
  exact RunBounded.seq (b := 0)
    (runBounded_compact_nibble_conversion s pointer length out initial small atPointer atLength atOut atInitial code ticks)
    (by omega) (by
      intro next normal nextCode budget
      exact RunBounded.ofProg (ProgBounded.straight _ rfl) (nextCode.trans code) (by omega))

#print axioms runBounded_compact_nibble_conversion
#print axioms runBounded_compact_nibble_finish
end InitECandidate.Runtime
