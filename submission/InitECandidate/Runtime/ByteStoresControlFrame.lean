import InitECandidate.Runtime.SourceByteStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Byte-store expression or memory failure yields error; success changes only
memory. Neither outcome consumes clock or changes locals or globals. -/
theorem evaluate_storeByte_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) :
    ((evaluateHOLFiniteState state (.storeByte destination value)).1 = none ∨
      (evaluateHOLFiniteState state (.storeByte destination value)).1 = some .error) ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.clock = state.clock ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.locals = state.locals ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.globals = state.globals ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.code = state.code ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.memaddrs = state.memaddrs ∧
    (evaluateHOLFiniteState state (.storeByte destination value)).2.be = state.be := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · split
    · split <;> simp
    · simp
  · simp

/-- The actual two-byte padding prefix is zero-clock even when either store
fails. Local bindings, globals, code and memory accessibility remain fixed. -/
theorem evaluate_two_storeBytes_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (firstDestination firstValue secondDestination secondValue : ExpHOL 64) :
    let output := evaluateHOLFiniteState state (.seq (.storeByte firstDestination firstValue) (.storeByte secondDestination secondValue));
    (output.1 = none ∨ output.1 = some .error) ∧ output.2.clock = state.clock ∧
      output.2.locals = state.locals ∧ output.2.globals = state.globals ∧ output.2.code = state.code ∧
      output.2.memaddrs = state.memaddrs ∧ output.2.be = state.be := by
  have first := evaluate_storeByte_control_frame state firstDestination firstValue
  cases firstRun : evaluateHOLFiniteState state (.storeByte firstDestination firstValue) with
  | mk result middle =>
    rw [firstRun] at first
    obtain ⟨control,clock,locals,globals,code,domain,endian⟩ := first
    rw [evaluateHOLFiniteState_seq_line780,firstRun]
    rcases control with rfl | rfl
    · have second := evaluate_storeByte_control_frame middle secondDestination secondValue
      exact ⟨second.1,second.2.1.trans clock,second.2.2.1.trans locals,second.2.2.2.1.trans globals,
        second.2.2.2.2.1.trans code,second.2.2.2.2.2.1.trans domain,second.2.2.2.2.2.2.trans endian⟩
    · exact ⟨Or.inr rfl,clock,locals,globals,code,domain,endian⟩

#print axioms evaluate_storeByte_control_frame
#print axioms evaluate_two_storeBytes_control_frame
end InitECandidate.Runtime
