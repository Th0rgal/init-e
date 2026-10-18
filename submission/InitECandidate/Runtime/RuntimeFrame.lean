import InitECandidate.Runtime.Bswap64CallBound
import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original-code fragments preserving memory and globals at every clock. -/
def RuntimeFrame (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
    (evaluateHOLFiniteState state program).2.memory = state.memory ∧
    (evaluateHOLFiniteState state program).2.globals = state.globals

theorem runtimeFrame_readOnly (program : ProgHOL 64) (supported : readOnlyMemory program = true) :
    RuntimeFrame program := by
  intro F state code
  exact ⟨evaluate_readOnly_memory program supported state,evaluate_readOnly_globals program supported state⟩

theorem runtimeFrame_seq (first second : ProgHOL 64) (one : RuntimeFrame first) (two : RuntimeFrame second) :
    RuntimeFrame (.seq first second) := by
  intro F state code
  have frame := one state code
  have metadata := (evaluateHOLFiniteState_metadata state first).1
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result post =>
    rw [run] at frame metadata
    cases result with
    | none =>
      have next := two post (metadata.trans code)
      exact ⟨next.1.trans frame.1,next.2.trans frame.2⟩
    | some result => exact frame

theorem runtimeFrame_ite (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (one : RuntimeFrame yes) (two : RuntimeFrame no) : RuntimeFrame (.ite condition yes no) := by
  intro F state code
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact two state code
    · exact one state code
  · exact ⟨rfl,rfl⟩

theorem runtimeFrame_dec (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
    (body : ProgHOL 64) (frame : RuntimeFrame body) : RuntimeFrame (.dec name shape initializer body) := by
  intro F state code
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨rfl,rfl⟩
  · rename_i value initialized
    split
    · have kept := frame (setVarHOLFinite name value state) code
      cases run : evaluateHOLFiniteState (setVarHOLFinite name value state) body with
      | mk result post =>
        rw [run] at kept
        exact kept
    · exact ⟨rfl,rfl⟩

theorem bswap64_body_readOnly : readOnlyMemory (sourceFunctionBody Guest.guestFn_bswap64) = true := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem runtimeFrame_bswap64 (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (tail : RuntimeFrame continuation) :
    RuntimeFrame (.decCall name shape (ofString "bswap64") arguments continuation) := by
  intro F state code
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_decCall_total,args]; exact ⟨rfl,rfl⟩
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup (ofString "bswap64") values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_total,args]
      dsimp only
      rw [lookup]
      exact ⟨rfl,rfl⟩
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      have installed := originalRuntimeCode_bswap64_lookup
      rw [← code] at installed
      have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "bswap64")
        [(ofString "x",.one)] (sourceFunctionBody Guest.guestFn_bswap64) body .one returnShape values callee installed lookup
      have supported : readOnlyMemory body = true := by rw [same]; exact bswap64_body_readOnly
      let entry := callEntryStateHOLFinite state callee
      have memory := evaluate_readOnly_memory body supported entry
      have globals := evaluate_readOnly_globals body supported entry
      have metadata := (evaluateHOLFiniteState_metadata entry body).1
      rw [evaluateHOLFiniteState_decCall_total,args]
      dsimp only
      rw [lookup]
      dsimp only
      split
      · exact ⟨rfl,rfl⟩
      · rw [fixClockHOLFinite_evaluateState]
        cases run : evaluateHOLFiniteState entry body with
        | mk result post =>
          rw [run] at memory globals metadata
          dsimp only at memory globals metadata
          cases result with
          | none => exact ⟨memory,globals⟩
          | some result =>
            cases result with
            | returned value =>
              simp only
              split
              · let resumed := setVarHOLFinite name value {post with locals := state.locals}
                have kept := tail resumed (metadata.trans code)
                exact ⟨kept.1.trans memory,kept.2.trans globals⟩
              · exact ⟨memory,globals⟩
            | error => exact ⟨memory,globals⟩
            | timeOut => exact ⟨memory,globals⟩
            | «break» => exact ⟨memory,globals⟩
            | «continue» => exact ⟨memory,globals⟩
            | exception exception value => exact ⟨memory,globals⟩
            | finalFfi ffi => exact ⟨memory,globals⟩

#print axioms runtimeFrame_bswap64
end InitECandidate.Runtime
