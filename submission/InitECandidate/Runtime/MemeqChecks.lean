import InitECandidate.Runtime.HashFindDecision
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memeqChecks : List (ExpHOL 64 × ExpHOL 64) → ProgHOL 64
  | [] => .return (.const 1)
  | (left,right) :: rest => .seq
      (.ite (.cmp .notEqual left right) (.return (.const 0)) .skip) (memeqChecks rest)

/-- A readable straight-line comparison chain returns a Boolean word, spends
no source clocks and preserves all memory and metadata. -/
theorem evaluate_memeqChecks {F : Type} (state : PanSemStateFiniteExact 64 F)
    (checks : List (ExpHOL 64 × ExpHOL 64))
    (readable : ∀ pair ∈ checks, ∃ left right : BitVec 64,
      @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) pair.1 =
        some (.val (.word left)) ∧
      @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) pair.2 =
        some (.val (.word right))) :
    ∃ value : BitVec 64, (value = 0 ∨ value = 1) ∧ evaluateHOLFiniteState state (memeqChecks checks) =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
  induction checks with
  | nil =>
    refine ⟨1,Or.inr rfl,?_⟩
    simp [memeqChecks,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  | cons pair rest ih =>
    obtain ⟨left,right,l,r⟩ := readable pair (by simp)
    have tail := ih (fun pair member => readable pair (by simp [member]))
    have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.cmp .notEqual pair.1 pair.2) =
        some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .notEqual left right then 1 else 0))) := by
      simp [evalHOLExact,l,r]
    cases flag : Compiler.Encoders.Asm.wordCmpHOL .notEqual left right with
    | false =>
      obtain ⟨value,boolean,run⟩ := tail
      refine ⟨value,boolean,?_⟩
      simp only [memeqChecks,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition,flag]
      simpa using run
    | true =>
      refine ⟨0,Or.inl rfl,?_⟩
      simp only [memeqChecks,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition,flag]
      simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms evaluate_memeqChecks
end InitECandidate.Runtime
