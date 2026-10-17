import InitECandidate.Runtime.RlpListCountCallGlobals
import InitECandidate.Runtime.PanDiscardReturnGlobals
import InitECandidate.Runtime.RlpItemLongListFinishBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_short_list_tail_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (argumentShape : arguments = [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")])
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemShortListTail = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rw [source_rlpItem_short_list_tail] at run
  obtain ⟨middle,called,globals⟩ := evaluate_discard_then_return_globals state post (ofString "rlp_list_count")
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")] _ value (by decide) run
  rw [globals]
  subst arguments
  exact rlpListCount_call_normal_globals state middle [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")] pointer length scratch frame ceiling inputLimit
    args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget called

#print axioms rlpItem_short_list_tail_returned_globals
theorem rlpItem_long_list_tail_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (argumentShape : arguments = [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")])
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemLongListTail = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rw [source_rlpItem_long_list_tail] at run
  obtain ⟨middle,called,globals⟩ := evaluate_discard_then_return_globals state post (ofString "rlp_list_count")
    [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")] _ value (by decide) run
  rw [globals]
  subst arguments
  exact rlpListCount_call_normal_globals state middle [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")] pointer length scratch frame ceiling inputLimit
    args noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget called

#print axioms rlpItem_long_list_tail_returned_globals
end InitECandidate.Runtime
