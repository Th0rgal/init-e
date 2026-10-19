import InitECandidate.Runtime.HeaderRlpFieldDeclarationFrame
import InitECandidate.Runtime.BoundedDecCallReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- A real field declaration reaches its continuation with the checked value
and preserved globals/high memory, or terminates within the parser budget. -/
theorem header_rlp_field_declaration_reaches {F : Type} (s : PanSemStateFiniteExact 64 F) (field : HeaderRlpField)
    (array index extra pointer length input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some (headerRlpFieldValues field array index extra))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : headerRlpFieldCost inputLimit + 1 ≤ s.clock)
 :
    Reaches s (.decCall name shape (headerRlpFieldName field) arguments continuation)
      (fun ready => ∃ value : ValueHOL 64,
        ready.locals = s.locals.update (name,value) ∧
        shapeEqHOL (shapeOfHOLExact value) shape = true ∧
        shapeEqHOL (shapeOfHOLExact value) (headerRlpFieldShape field) = true ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        (∀ global : MlS, ready.globals.lookup global = s.globals.lookup global) ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → ready.memory address = s.memory address))
      (headerRlpFieldCost inputLimit + 1) continuation := by
  let callState := callEntryStateHOLFinite s (headerRlpFieldCallee field array index extra)
  have atArray : callState.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerRlpFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : callState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    cases field <;> simp (config := {decide := true}) [callState,callEntryStateHOLFinite,headerRlpFieldCallee,
      HolFiniteMapExact.lookup_update,FUPDATE]
  have calleeEntry : RlpSliceInputEntry callState array index pointer length input inputLength :=
    entry.after_frame s callState _ _ _ _ _ _ rfl rfl rfl
  have bodyBudget : headerRlpFieldCost inputLimit ≤ callState.clock := by
    change headerRlpFieldCost inputLimit ≤ s.clock - 1
    omega
  have bounded := runBounded_header_rlp_field_input callState field array index pointer length input inputLength scratch frame
    ceiling inputLimit atArray atIndex calleeEntry inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena bodyBudget
  have lookup := header_rlp_field_lookup field array index extra
  rw [← code] at lookup
  apply bounded_decCall_reaches s name (headerRlpFieldName field) shape (headerRlpFieldShape field) arguments
    (headerRlpFieldValues field array index extra) (sourceFunctionBody (headerRlpFieldDeclaration field)) continuation
    (headerRlpFieldCallee field array index extra) (headerRlpFieldCost inputLimit) _ args lookup budget bounded
  intro value post returned checked
  have lengthBound := (entry.length_bound s array index pointer length input inputLength).trans inputBound
  have parserBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ callState.clock := by
    have product := Nat.mul_le_mul lengthBound (by omega : (2 * length.toNat + 1) * 15 + 19 ≤ (2 * inputLimit + 1) * 15 + 19)
    unfold headerRlpFieldCost at bodyBudget
    omega
  obtain ⟨domain,installed,globals,memory⟩ := header_rlp_field_returned_frame callState post field pointer length scratch frame
    ceiling inputLimit (eval_header_rlp_field_arguments callState array index pointer length input inputLength atArray atIndex calleeEntry)
    entry.noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena parserBudget value returned
  exact ⟨value,rfl,checked.1,checked.2,domain,installed,globals,memory⟩

#print axioms header_rlp_field_declaration_reaches
end InitECandidate.Runtime
