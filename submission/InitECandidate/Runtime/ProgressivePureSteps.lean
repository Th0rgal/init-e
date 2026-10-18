import InitECandidate.Runtime.ProgressiveMerkleSource
import InitECandidate.Runtime.ProgressiveCounters
import InitECandidate.Runtime.ProgBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def progressiveUpdateState {F : Type} (state : PanSemStateFiniteExact 64 F)
    (off size k : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "k") (.val (.word (k + (1#64))))
    (setVarHOLFinite (ofString "size") (.val (.word (size <<< (2 : Nat))))
      (setVarHOLFinite (ofString "off") (.val (.word (off + size))) state))

theorem evaluate_progressive_updates {F : Type} (state : PanSemStateFiniteExact 64 F)
    (off size k : BitVec 64)
    (atOff : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (atSize : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (atK : state.locals.lookup (ofString "k") = some (.val (.word k))) :
    evaluateHOLFiniteState state progressiveUpdates = (none,progressiveUpdateState state off size k) := by
  rw [source_progressive_updates]
  simp (config := {decide := true}) [progressiveUpdateState,evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atOff,atSize,atK,
    wordOpHOL,wordOp,valueIsWord,valueWord,wordShiftHOL,lookupKvarHOLExact,isValidValueHOLExact,
    setKvarHOLFinite,setVarHOLFinite,shapeOfHOLExact,shapeEqHOL,HolFiniteMapExact.lookup_update,FUPDATE]

theorem progressive_update_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (off size k : BitVec 64) :
    (progressiveUpdateState state off size k).locals.lookup (ofString "off") = some (.val (.word (off + size))) ∧
      (progressiveUpdateState state off size k).locals.lookup (ofString "size") = some (.val (.word (size <<< (2 : Nat)))) ∧
      (progressiveUpdateState state off size k).locals.lookup (ofString "k") = some (.val (.word (k + (1#64)))) := by
  simp (config := {decide := true}) [progressiveUpdateState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem progressive_update_other_local {F : Type} (state : PanSemStateFiniteExact 64 F)
    (off size k : BitVec 64) (key : MlS)
    (noOff : key ≠ ofString "off") (noSize : key ≠ ofString "size") (noK : key ≠ ofString "k") :
    (progressiveUpdateState state off size k).locals.lookup key = state.locals.lookup key := by
  simp [progressiveUpdateState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    Ne.symm noOff,Ne.symm noSize,Ne.symm noK]

def progressiveClippedState {F : Type} (state : PanSemStateFiniteExact 64 F)
    (n off size : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let entered := setVarHOLFinite (ofString "cnt") (.val (.word (n - off))) state
  if size < n - off then setVarHOLFinite (ofString "cnt") (.val (.word size)) entered else entered

theorem evaluate_progressive_clip {F : Type} (state : PanSemStateFiniteExact 64 F)
    (n off size : BitVec 64)
    (atSize : state.locals.lookup (ofString "size") = some (.val (.word size))) :
    evaluateHOLFiniteState (setVarHOLFinite (ofString "cnt") (.val (.word (n - off))) state) progressiveClip =
      (none,progressiveClippedState state n off size) := by
  rw [source_progressive_clip,evaluateHOLFiniteState_ite]
  by_cases less : size < n - off
  all_goals simp (config := {decide := true}) [progressiveClippedState,evalHOLExact,atSize,
    Compiler.Encoders.Asm.wordCmpHOL,less,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_assign,
    lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,setVarHOLFinite,shapeOfHOLExact,shapeEqHOL,
    HolFiniteMapExact.lookup_update,FUPDATE]

theorem progressive_clipped_count {F : Type} (state : PanSemStateFiniteExact 64 F)
    (n off size : BitVec 64) :
    (progressiveClippedState state n off size).locals.lookup (ofString "cnt") =
      some (.val (.word (progressiveChunkCount n off size))) := by
  unfold progressiveClippedState progressiveChunkCount
  split <;> simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

theorem progressive_clipped_other_local {F : Type} (state : PanSemStateFiniteExact 64 F)
    (n off size : BitVec 64) (key : MlS) (different : key ≠ ofString "cnt") :
    (progressiveClippedState state n off size).locals.lookup key = state.locals.lookup key := by
  unfold progressiveClippedState
  split <;> simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

theorem progressive_pure_bounds : ProgBounded progressiveClip 0 ∧ ProgBounded progressiveUpdates 0 := by
  exact ⟨ProgBounded.straight _ (by rw [source_progressive_clip]; decide),
    ProgBounded.straight _ (by rw [source_progressive_updates]; decide)⟩

#print axioms evaluate_progressive_updates
#print axioms progressive_update_fields
#print axioms progressive_update_other_local
#print axioms evaluate_progressive_clip
#print axioms progressive_clipped_count
#print axioms progressive_clipped_other_local
#print axioms progressive_pure_bounds
end InitECandidate.Runtime
