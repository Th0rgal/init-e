import InitECandidate.Runtime.RlpValidationLoopInvariant
import InitECandidate.Runtime.RlpValidationInitialization
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real initialized validator state satisfies the complete loop invariant,
with rank exactly twice its supplied input length. -/
theorem rlpValidation_initial_witness {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address) :
    ∃ valid : RlpValidationLoopWitness (rlpValidationInitialState state pointer length) frame ceiling inputLimit,
      rlpValidationRank valid.position valid.stop valid.frames = 2 * length.toNat ∧ valid.flag = 1 := by
  have initial := rlpValidation_initial_state state pointer length noWrap
  dsimp only at initial
  refine ⟨{
    position := pointer, stop := pointer + length, scratch := scratch, frames := [], flag := 1
    positionLocal := initial.2.1, stopLocal := initial.2.2.1, topLocal := initial.1
    flagLocal := initial.2.2.2.1
    stack := .nil, intervals := initial.2.2.2.2.2.1
    rankBound := ?_
    scratchGlobal := scratchGlobal, frameGlobal := frameGlobal, code := code
    orderedFrame := orderedFrame, scratchBelow := scratchBelow
    stackCeiling := ?_, arena := arena },initial.2.2.2.2.2.2.1,rfl⟩
  · rw [initial.2.2.2.2.2.2.1]
    omega
  · intro saved member
    simp at member

/-- Actual execution of the original declaration scopes exposes a loop with
the complete initial witness; scope restoration retains its clock result. -/
theorem evaluate_rlpValidation_witness_initialized {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (result : Option (PanSemResultExact 64))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn__rlp_validate_items_body) = (result,post)) :
    ∃ (valid : RlpValidationLoopWitness (rlpValidationInitialState state pointer length) frame ceiling inputLimit)
      (output : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (rlpValidationInitialState state pointer length) rlpValidationLoopAndReturn = (result,output) ∧
      rlpValidationRank valid.position valid.stop valid.frames = 2 * length.toNat ∧
      valid.flag = 1 ∧ post.clock = output.clock := by
  obtain ⟨valid,rank,flag⟩ := rlpValidation_initial_witness state pointer length scratch frame ceiling inputLimit
    noWrap lengthBound scratchGlobal frameGlobal code orderedFrame scratchBelow arena
  obtain ⟨output,body,clock,_⟩ := evaluate_rlpValidation_initialized_loop state post pointer length result pointerLocal lengthLocal run
  exact ⟨valid,output,body,rank,flag,clock⟩

#print axioms rlpValidation_initial_witness
#print axioms evaluate_rlpValidation_witness_initialized
end InitECandidate.Runtime
