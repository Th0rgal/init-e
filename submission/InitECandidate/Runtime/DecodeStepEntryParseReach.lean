import InitECandidate.Runtime.DecodeStepInitialLocals
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original entry through the handled parser reaches kind dispatch
with input-bounded payload fields and restored globals, or terminates in the
all-outcome parse budget. Includes the real two initial declarations. -/
theorem decode_step_entry_parse_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepParseCost length.toNat ≤ s.clock) :
    Reaches s (decodeStepAt 0)
      (fun post => ∃ kind payloadPointer payload : BitVec 64,
        post.locals.lookup (ofString "it") =
          some (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word length)]) ∧
        (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ length.toNat ∧ 0 < length.toNat ∧
        payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
        payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
        (∀ watched, post.globals.lookup watched = s.globals.lookup watched) ∧
        post.code = s.code ∧ post.memaddrs = s.memaddrs ∧ post.be = s.be)
      (decodeStepParseCost length.toNat) (decodeStepAt 3) := by
  have parsed := decode_step_parse_prefix_reaches (decodeStepInitialLocals s) pointer length scratch frame ceiling
    inputLimit
    (by simp (config := {decide := true}) [decodeStepInitialLocals,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,atPointer])
    (by simp (config := {decide := true}) [decodeStepInitialLocals,setVarHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,atLength])
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  have composed := reaches_trans_budget s (decodeStepAt 0) (decodeStepAt 2) (decodeStepAt 3)
    _ _ 0 (decodeStepParseCost length.toNat) (by simpa using budget)
    (decode_step_initial_locals_reaches s) (by
      intro ready same ticks
      subst ready
      exact parsed)
  simpa only [Nat.zero_add,decodeStepInitialLocals,setVarHOLFinite] using composed

#print axioms decode_step_entry_parse_reaches
end InitECandidate.Runtime
