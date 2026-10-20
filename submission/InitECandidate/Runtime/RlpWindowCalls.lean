import InitECandidate.Runtime.HtabSetBound
import InitECandidate.Runtime.ByteStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A one-word shape pins a value to a word. -/
theorem shapeWord_of_one {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ y : BitVec 64, v = .val (.word y) := by
  cases v with
  | val x => cases x with
    | word y => exact ⟨y,rfl⟩
  | _ => simp [shapeOfHOLExact,shapeEqHOL] at h

#print axioms shapeWord_of_one

/-- A program whose whole memory is framed keeps any single watched cell. -/
theorem window_of_memoryFrame {program : ProgHOL 64} (frame : MemoryFrame program)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s program).2.memory w = s.memory w :=
  congrFun (frame s code).1 w

#print axioms window_of_memoryFrame

/-- Sequencing two window-preserving programs preserves the window. -/
theorem window_seq {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    {first second : ProgHOL 64}
    (h1 : (evaluateHOLFiniteState s first).2.memory w = s.memory w)
    (h2 : ∀ (t : PanSemStateFiniteExact 64 F), t.memory w = s.memory w →
      (evaluateHOLFiniteState t second).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s (.seq first second)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState s first with
  | mk r middle =>
    rw [run] at h1
    cases r with
    | none =>
      dsimp only
      exact h2 middle h1
    | some res => exact h1

#print axioms window_seq

/-- A discarded call of an installed function whose body keeps the watched cell keeps it too, in
every outcome: argument or lookup failure, clock timeout, any callee result, and the call-shape
checks. -/
theorem discardCall_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (w : BitVec 64)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values)
    (hlookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s (.call (some (none,none)) function arguments)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_call,hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp [emptyLocalsHOLFinite]
  · cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
    | mk rb st =>
      rw [run] at hbody
      cases rb with
      | none => exact hbody
      | some rr =>
        cases rr with
        | «returned» value =>
          dsimp only
          split
          · dsimp only
            exact hbody
          · exact hbody
        | _ =>
          dsimp only
          first
            | exact hbody
            | (simp only [emptyLocalsHOLFinite]; exact hbody)

#print axioms discardCall_window

/-- A tail call of an installed function whose body keeps the watched cell keeps it too, in every
outcome. -/
theorem tailCall_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (w : BitVec 64)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values)
    (hlookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape))
    (hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s (.call none function arguments)).2.memory w = s.memory w := by
  rw [evaluateHOLFiniteState_call,hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp [emptyLocalsHOLFinite]
  · cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
    | mk rb st =>
      rw [run] at hbody
      cases rb with
      | none => exact hbody
      | some rr =>
        cases rr with
        | «returned» value =>
          dsimp only
          split
          · dsimp only
            first
              | exact hbody
              | (simp only [emptyLocalsHOLFinite]; exact hbody)
          · exact hbody
        | _ =>
          dsimp only
          first
            | exact hbody
            | (simp only [emptyLocalsHOLFinite]; exact hbody)

#print axioms tailCall_window

/-- A `decCall` of an installed function whose body keeps the watched cell keeps it too, provided the
continuation keeps it for the word the callee returns.  Every other outcome (argument or lookup
failure, timeout, a non-returning callee, a failed shape check) returns the callee post-state, whose
memory is already framed. -/
theorem decCall_window {F : Type} (s : PanSemStateFiniteExact 64 F)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (w : BitVec 64)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values)
    (hlookup : lookupCodeHOLFinite s.code.lookup function values = some (body,callee,returnShape))
    (hbody : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).2.memory w = s.memory w)
    (hcont : ∀ (value : ValueHOL 64) (base : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned value),base) →
      shapeEqHOL (shapeOfHOLExact value) shape = true →
      shapeEqHOL (shapeOfHOLExact value) returnShape = true →
      ∀ (k : Nat), (evaluateHOLFiniteState
        (setVarHOLFinite resultName value {base with clock := k, locals := s.locals})
        continuation).2.memory w = s.memory w) :
    (evaluateHOLFiniteState s (.decCall resultName shape function arguments continuation)).2.memory w =
      s.memory w := by
  rw [evaluateHOLFiniteState_decCall_total,hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp [emptyLocalsHOLFinite]
  · cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
    | mk rb st =>
      rw [run] at hbody
      cases rb with
      | none =>
        dsimp only
        exact hbody
      | some rr =>
        cases rr with
        | «returned» value =>
          dsimp only
          split
          · rename_i hshape
            simp only [Bool.and_eq_true] at hshape
            exact hcont value st run hshape.1 hshape.2 _
          · dsimp only
            exact hbody
        | _ =>
          dsimp only
          first
            | exact hbody
            | (simp only [emptyLocalsHOLFinite]; exact hbody)

#print axioms decCall_window

end InitECandidate.Runtime
