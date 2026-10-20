import InitECandidate.Runtime.OriginalRlpWriterCode
import InitECandidate.Runtime.DiscardCallGlobalsFrame
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.AllocationRound
import InitECandidate.Runtime.AllocationSuccess
import InitECandidate.Runtime.RlpEncodeWordWindow
import InitECandidate.Runtime.RlpEncodeBytesPrefix
import InitECandidate.Runtime.RlpFinishList
import InitECandidate.Runtime.RlpHeaderLenMemoryFrame
import InitECandidate.Runtime.RlpWriteHeaderWindow
import InitECandidate.Runtime.RlpPutBeWindow
import InitECandidate.Runtime.RlpEncodeListHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A tail call that binds nothing, into a globals-retaining installed body, retains globals. -/
theorem originalGlobalsFrame_tail_call (function : MlS)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call none function arguments) := by
  intro F state code
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rfl
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rfl
    | some data =>
      obtain ⟨foundBody,locals,foundShape⟩ := data
      dsimp only
      by_cases zero : state.clock = 0
      · simp [zero,emptyLocalsHOLFinite]
      · rw [if_neg zero]
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body
          foundBody returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := frame (callEntryStateHOLFinite state locals) code
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          cases result with
          | none => exact globals
          | some result =>
            cases result <;> dsimp only
            all_goals (try split) <;> all_goals (try split) <;> all_goals
              (first
                | exact globals
                | (simp only [setKvarHOLFinite,setVarHOLFinite,emptyLocalsHOLFinite]; exact globals))

/-- A call binding its result to a local retains globals when the installed body does. -/
theorem originalGlobalsFrame_local_call (name function : MlS)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some ((some (.local,name)),none)) function arguments) := by
  intro F state code
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rfl
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rfl
    | some data =>
      obtain ⟨foundBody,locals,foundShape⟩ := data
      dsimp only
      by_cases zero : state.clock = 0
      · simp [zero,emptyLocalsHOLFinite]
      · rw [if_neg zero]
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body
          foundBody returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := frame (callEntryStateHOLFinite state locals) code
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          cases result with
          | none => exact globals
          | some result =>
            cases result <;> dsimp only
            all_goals (try split) <;> all_goals (try split) <;> all_goals
              (first
                | exact globals
                | (simp only [setKvarHOLFinite,setVarHOLFinite,emptyLocalsHOLFinite]; exact globals))

/-- A declaration call binding its result to a local retains globals when both the installed body
and the continuation do, in every outcome. -/
theorem originalGlobalsFrame_local_decCall (name : MlS) (shape : ShapeHOL) (function : MlS)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyFrame : OriginalGlobalsFrame body) (continuation : ProgHOL 64)
    (contFrame : OriginalGlobalsFrame continuation) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.decCall name shape function arguments continuation) := by
  intro F state code
  rw [evaluateHOLFiniteState_decCall_total]
  dsimp only
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rfl
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rfl
    | some data =>
      obtain ⟨foundBody,locals,foundShape⟩ := data
      dsimp only
      by_cases zero : state.clock = 0
      · simp [zero,emptyLocalsHOLFinite]
      · rw [if_neg zero]
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body
          foundBody returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := bodyFrame (callEntryStateHOLFinite state locals) code
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          dsimp only
          cases result with
          | none => simpa only [fixClockHOLFinite] using globals
          | some result =>
            cases result with
            | returned value =>
              dsimp only
              split
              · dsimp only
                let ready : PanSemStateFiniteExact 64 F :=
                  {(fixClockHOLFinite (callEntryStateHOLFinite state locals)
                    (some (PanSemResultExact.returned value),post)).2 with locals := state.locals}
                have readyGlobals : ready.globals = state.globals := by
                  simp only [ready,fixClockHOLFinite]
                  exact globals
                have postCode : post.code = state.code := by
                  have met := (evaluateHOLFiniteState_metadata
                    (callEntryStateHOLFinite state locals) foundBody).1
                  rw [run] at met
                  exact met
                have readyCode : ready.code = originalRuntimeCode := by
                  simp only [ready,fixClockHOLFinite]
                  rw [postCode]
                  exact code
                have frame := contFrame (setVarHOLFinite name value ready) readyCode
                show (evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation).2.globals
                  = state.globals
                exact frame.trans readyGlobals
              · simpa only [fixClockHOLFinite] using globals
            | error => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | timeOut => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | «break» => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | «continue» => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | exception id value => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | finalFfi event => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals

#print axioms originalGlobalsFrame_tail_call
#print axioms originalGlobalsFrame_local_call
#print axioms originalGlobalsFrame_local_decCall

/-- A declaration call step, with everything the goal determines kept implicit. -/
theorem globalsFrame_declCall_step {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {returnShape : ShapeHOL} {name : MlS} {shape : ShapeHOL}
    {continuation : ProgHOL 64} {arguments : List (ExpHOL 64)}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyFrame : OriginalGlobalsFrame body) (contFrame : OriginalGlobalsFrame continuation) :
    OriginalGlobalsFrame (.decCall name shape function arguments continuation) :=
  originalGlobalsFrame_local_decCall name shape function parameters body returnShape installed
    bodyFrame continuation contFrame arguments

/-- A local-bound call step, with everything the goal determines kept implicit. -/
theorem globalsFrame_localCall_step {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {returnShape : ShapeHOL} {name : MlS} {arguments : List (ExpHOL 64)}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) :
    OriginalGlobalsFrame (.call (some ((some (.local,name)),none)) function arguments) :=
  originalGlobalsFrame_local_call name function parameters body returnShape installed frame arguments

/-- A discarded call step, with everything the goal determines kept implicit. -/
theorem globalsFrame_discard_step {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {returnShape : ShapeHOL} {arguments : List (ExpHOL 64)}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) :
    OriginalGlobalsFrame (.call (some (none,none)) function arguments) :=
  originalGlobalsFrame_discard_call function parameters body returnShape installed frame arguments

/-- A tail-call step, with everything the goal determines kept implicit. -/
theorem globalsFrame_tailStep {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {returnShape : ShapeHOL} {arguments : List (ExpHOL 64)}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) :
    OriginalGlobalsFrame (.call none function arguments) :=
  originalGlobalsFrame_tail_call function parameters body returnShape installed frame arguments

theorem rlpBeLen_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_be_len) := by
  rw [source_rlpBeLen_body]
  exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem rlpPutBe_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_put_be) := by
  rw [source_rlpPutBe_body,rlpPutBeLoop,rlpPutBeStep]
  exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem rlpHeaderLen_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_header_len) := by
  rw [source_rlpHeaderLen_body]
  apply originalGlobalsFrame_sequence
  · apply originalGlobalsFrame_conditional
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
  · have tail : OriginalGlobalsFrame (.return (.op .add [.const (1#64),
        .var .local (ofString "ll")])) :=
      originalGlobalsFrame_leaf _ (by intro watched; rfl)
    apply globalsFrame_declCall_step originalRuntimeCode_rlp_be_len_lookup
      rlpBeLen_globals_frame
    exact tail

theorem rlpListHeaderLen_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_list_header_len) := by
  rw [source_rlpListHeaderLen_body]
  exact globalsFrame_tailStep originalRuntimeCode_rlp_header_len_lookup rlpHeaderLen_globals_frame

theorem rlpWriteHeader_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_write_header) := by
  rw [source_rlpWriteHeader_body,rlpWriteHeaderPrefix,rlpWriteHeaderTail]
  apply originalGlobalsFrame_sequence
  · apply originalGlobalsFrame_conditional
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
  · have tail : OriginalGlobalsFrame
        (.seq (.storeByte (.var .local (ofString "dst"))
            (.op .add [.var .local (ofString "base"), .const (55#64),
              .var .local (ofString "ll")]))
          (.seq (.call (some (none,none)) (ofString "rlp_put_be")
              [.op .add [.var .local (ofString "dst"), .const (1#64)],
               .var .local (ofString "n"), .var .local (ofString "ll")])
            (.return (.op .add [.const (1#64), .var .local (ofString "ll")])))) :=
      originalGlobalsFrame_sequence _ _
        (originalGlobalsFrame_leaf _ (by intro watched; rfl))
        (originalGlobalsFrame_sequence _ _
          (globalsFrame_discard_step originalRuntimeCode_rlp_put_be_lookup rlpPutBe_globals_frame)
          (originalGlobalsFrame_leaf _ (by intro watched; rfl)))
    apply globalsFrame_declCall_step originalRuntimeCode_rlp_be_len_lookup
      rlpBeLen_globals_frame
    exact tail

theorem rlpEncodeListHeader_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_encode_list_header) := by
  rw [source_rlpEncodeListHeader_body]
  exact globalsFrame_tailStep originalRuntimeCode_rlp_write_header_lookup
    rlpWriteHeader_globals_frame

theorem rlpEncodeBytes_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) := by
  rw [source_rlpEncodeBytes_body,rlpEncodeBytesPrefix,rlpEncodeBytesTail]
  apply originalGlobalsFrame_sequence
  · apply originalGlobalsFrame_conditional
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
  · have tail : OriginalGlobalsFrame
        (.seq (.call (some (none,none)) (ofString "memcpy")
            [.op .add [.var .local (ofString "dst"), .var .local (ofString "h")],
             .var .local (ofString "src"), .var .local (ofString "n")])
          (.return (.op .add [.var .local (ofString "h"),
            .var .local (ofString "n")]))) :=
      originalGlobalsFrame_sequence _ _
        (globalsFrame_discard_step originalRuntimeCode_memcpy_lookup memcpy_body_globals_frame)
        (originalGlobalsFrame_leaf _ (by intro watched; rfl))
    apply globalsFrame_declCall_step originalRuntimeCode_rlp_write_header_lookup
      rlpWriteHeader_globals_frame
    exact tail

theorem rlpFinishList_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_finish_list) := by
  rw [source_rlpFinishList_body,rlpFinishListPayloadInit,rlpFinishListTorso]
  apply originalGlobalsFrame_declaration
  have tail : OriginalGlobalsFrame
      (.seq (.call (some (none,none)) (ofString "memcpy")
          [.op .add [.var .local (ofString "dst"), .var .local (ofString "hl")],
           .op .add [.var .local (ofString "dst"), .const (9#64)],
           .var .local (ofString "payload")])
        (.seq (.call (some (none,none)) (ofString "rlp_encode_list_header")
            [.var .local (ofString "dst"), .var .local (ofString "payload")])
          (.return (.op .add [.var .local (ofString "hl"),
            .var .local (ofString "payload")])))) :=
    originalGlobalsFrame_sequence _ _
      (globalsFrame_discard_step originalRuntimeCode_memcpy_lookup memcpy_body_globals_frame)
      (originalGlobalsFrame_sequence _ _
        (globalsFrame_discard_step originalRuntimeCode_rlp_encode_list_header_lookup
          rlpEncodeListHeader_globals_frame)
        (originalGlobalsFrame_leaf _ (by intro watched; rfl)))
  apply globalsFrame_declCall_step originalRuntimeCode_rlp_list_header_len_lookup
    rlpListHeaderLen_globals_frame
  exact tail

theorem rlpEncodeWord_globals_frame :
    OriginalGlobalsFrame (sourceFunctionBody Guest.guestFn_rlp_encode_word) := by
  rw [source_rlpEncodeWord_body,rlpEncodeWordZero,rlpEncodeWordSmall,rlpEncodeWordLong]
  apply originalGlobalsFrame_sequence
  · apply originalGlobalsFrame_conditional
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
  · apply originalGlobalsFrame_sequence
    · apply originalGlobalsFrame_conditional
      · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
      · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)
    · have tail : OriginalGlobalsFrame
          (.seq (.storeByte (.var .local (ofString "dst"))
              (.op .add [.const (128#64), .var .local (ofString "ll")]))
            (.seq (.call (some (none,none)) (ofString "rlp_put_be")
                [.op .add [.var .local (ofString "dst"), .const (1#64)],
                 .var .local (ofString "w"), .var .local (ofString "ll")])
              (.return (.op .add [.const (1#64), .var .local (ofString "ll")])))) :=
        originalGlobalsFrame_sequence _ _
          (originalGlobalsFrame_leaf _ (by intro watched; rfl))
          (originalGlobalsFrame_sequence _ _
            (globalsFrame_discard_step originalRuntimeCode_rlp_put_be_lookup rlpPutBe_globals_frame)
            (originalGlobalsFrame_leaf _ (by intro watched; rfl)))
      apply globalsFrame_declCall_step originalRuntimeCode_rlp_be_len_lookup
        rlpBeLen_globals_frame
      apply tail

#print axioms rlpBeLen_globals_frame
#print axioms rlpHeaderLen_globals_frame
#print axioms rlpWriteHeader_globals_frame
#print axioms rlpEncodeBytes_globals_frame
#print axioms rlpFinishList_globals_frame
#print axioms rlpEncodeWord_globals_frame
end InitECandidate.Runtime
