import InitECandidate.Runtime.MemeqLoopSteps
import InitECandidate.Runtime.HashWordStep
/-!
Read-check-advance steps whose checks all read: no error outcome, and an explicit frame.  A step either advances its
counter (every other field of the state kept) or returns `0` from the unchanged state.  Instantiated for the source
`memeq` byte loops (`memeqByte8Step`, `memeqByte1Step`) from the aligned cells of the compared bytes.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The check conditions of a read-check-advance step, in order. -/
def rcChecks : ProgHOL 64 → List (ExpHOL 64)
  | .seq (.ite c (.return _) .skip) rest => c :: rcChecks rest
  | _ => []

section st
variable {F : Type}

theorem evaluate_rcStep_readable {counter : MlS} {increment : BitVec 64} {program : ProgHOL 64}
    (supported : ReadCheckAdvanceStep counter increment program) (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup counter = some (.val (.word index)))
    (readable : ∀ c ∈ rcChecks program, ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) c = some (.val (.word v))) :
    (evaluateHOLFiniteState state program =
        (none, setVarHOLFinite counter (.val (.word (index + increment))) state)) ∨
      evaluateHOLFiniteState state program = (some (.returned (.val (.word 0))), emptyLocalsHOLFinite state) := by
  induction supported generalizing state with
  | advance =>
    left
    apply evaluate_local_word_assignment state counter _ index (index + increment) binding
    simp [evalHOLExact, evalListHOLExact, binding, wordOpHOL, wordOp, valueIsWord, valueWord]
  | check condition tail ih =>
    obtain ⟨v, hv⟩ := readable condition (by simp [rcChecks])
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    rw [hv]
    by_cases z : v = 0
    · simp only [z, if_true, evaluateHOLFiniteState_skip]
      exact ih state binding (fun c hc => readable c (by simp [rcChecks, hc]))
    · right
      simp [z, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      have z' : ¬ v = 0#64 := z
      simp only [z', if_false]

/-- A source byte comparison `ld8 (x + i + c) != ld8 (y + i + c)`. -/
def mbCheck (cs : List (BitVec 64)) : ExpHOL 64 :=
  .cmp .notEqual
    (.loadByte (.op .add ([.var .local (ofString "a"), .var .local (ofString "i")] ++ cs.map .const)))
    (.loadByte (.op .add ([.var .local (ofString "b"), .var .local (ofString "i")] ++ cs.map .const)))

theorem rcChecks_memeqByte8 : rcChecks memeqByte8Step =
    [mbCheck [], mbCheck [1], mbCheck [2], mbCheck [3], mbCheck [4], mbCheck [5], mbCheck [6], mbCheck [7]] := by rfl

theorem rcChecks_memeqByte1 : rcChecks memeqByte1Step = [mbCheck []] := by rfl

theorem eval_mbCheck (state : PanSemStateFiniteExact 64 F) (a b i : BitVec 64)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word i))) (cs : List (BitVec 64))
    (da : state.memaddrs (panByteAlignHOL (a + (i + cs.foldr (· + ·) 0))))
    (db : state.memaddrs (panByteAlignHOL (b + (i + cs.foldr (· + ·) 0)))) :
    ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (mbCheck cs) = some (.val (.word v)) := by
  have consts : ∀ ds : List (BitVec 64), @evalListHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (ds.map .const) =
        some (ds.map fun d => .val (.word d)) := by
    intro ds; induction ds with
    | nil => rfl
    | cons d rest ih => simp [evalListHOLExact, evalHOLExact, ih]
  have addr : ∀ (x : MlS) (xv : BitVec 64), state.locals.lookup x = some (.val (.word xv)) →
      @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .add ([.var .local x, .var .local (ofString "i")] ++ cs.map .const)) =
        some (.val (.word (xv + (i + cs.foldr (· + ·) 0)))) := by
    intro x xv hx
    rw [evalHOLExact]
    simp only [List.cons_append, List.nil_append]
    rw [evalListHOLExact, evalListHOLExact, consts cs]
    simp [evalHOLExact, hx, hi, valueIsWord, valueWord, wordOpHOL, wordOp, List.foldr_map]
  have load : ∀ (x : MlS) (xv : BitVec 64), state.locals.lookup x = some (.val (.word xv)) →
      state.memaddrs (panByteAlignHOL (xv + (i + cs.foldr (· + ·) 0))) →
      ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.loadByte (.op .add ([.var .local x, .var .local (ofString "i")] ++ cs.map .const))) = some (.val (.word v)) := by
    intro x xv hx dx
    obtain ⟨w, cw⟩ : ∃ w : BitVec 64, state.memory (panByteAlignHOL (xv + (i + cs.foldr (· + ·) 0))) = .word w := by
      cases state.memory (panByteAlignHOL (xv + (i + cs.foldr (· + ·) 0))) with | word w => exact ⟨w, rfl⟩
    rw [evalHOLExact, addr x xv hx]
    simp [panMemLoadByteHOL, cw, dx]
    exact dx
  obtain ⟨va, la⟩ := load _ a ha da
  obtain ⟨vb, lb⟩ := load _ b hb db
  unfold mbCheck
  rw [evalHOLExact, la, lb]
  exact ⟨_, rfl⟩

end st
#print axioms evaluate_rcStep_readable
#print axioms rcChecks_memeqByte8
#print axioms eval_mbCheck
end InitECandidate.Runtime
