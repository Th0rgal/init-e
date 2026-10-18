import InitECandidate.Runtime.PanReturnedPath
import InitECandidate.Runtime.StoreControlFrame
import InitECandidate.Runtime.GlobalsFrameComposition
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A run of word or structure stores in front of a tail program. -/
inductive StoreChain : ProgHOL 64 → ProgHOL 64 → Prop
  | nil (tail : ProgHOL 64) : StoreChain tail tail
  | cons (destination value : ExpHOL 64) {rest tail : ProgHOL 64} :
      StoreChain rest tail → StoreChain (.seq (.store destination value) rest) tail

/-- If a store chain returns, every store finished normally, globals, code,
domain and clock are unchanged, and the tail returned from the reached state. -/
theorem StoreChain.returned {program tail : ProgHOL 64} (chain : StoreChain program tail)
    {F : Type} {s post : PanSemStateFiniteExact 64 F} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s program = (some (.returned v),post)) :
    ∃ mid : PanSemStateFiniteExact 64 F, mid.globals = s.globals ∧ mid.code = s.code ∧ mid.memaddrs = s.memaddrs ∧
      mid.clock = s.clock ∧ evaluateHOLFiniteState mid tail = (some (.returned v),post) := by
  induction chain generalizing s with
  | nil => exact ⟨s,rfl,rfl,rfl,rfl,run⟩
  | cons destination value rest ih =>
    have frame := evaluate_store_control_frame s destination value
    obtain ⟨mid,first,second⟩ := seq_returned_of_first frame.1 run
    obtain ⟨final,g,c,m,k,r⟩ := ih second
    have meta' := evaluateHOLFiniteState_metadata s (.store destination value)
    have globals : (evaluateHOLFiniteState s (.store destination value)).2.globals = s.globals := by
      rw [evaluateHOLFiniteState_store]
      repeat' first | split | rfl
    rw [first] at meta' frame globals
    refine ⟨final,?_,?_,?_,?_,r⟩
    · rw [g]; exact globals
    · rw [c]; exact meta'.1
    · rw [m]; exact meta'.2.1
    · rw [k]; exact frame.2.2

/-- A call followed by a tail cannot return when the clock is already exhausted
at the call. -/
theorem call_seq_returned_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64))} {function : MlS}
    {arguments : List (ExpHOL 64)} {tail : ProgHOL 64} {v : ValueHOL 64}
    (run : evaluateHOLFiniteState s (.seq (.call info function arguments) tail) = (some (.returned v),post)) :
    s.clock ≠ 0 := by
  intro zero
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call] at run
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [args] at run; simp at run
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [lookup] at run; simp at run
    | some data =>
      obtain ⟨b,c,r⟩ := data
      rw [lookup] at run
      simp [zero] at run

#print axioms StoreChain.returned
#print axioms call_seq_returned_clock
end InitECandidate.Runtime
