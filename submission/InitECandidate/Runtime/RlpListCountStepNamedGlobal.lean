import InitECandidate.Runtime.RlpListCountStep
import InitECandidate.Runtime.RlpItemTotalDeclarationNamedGlobal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal original list-count iteration retains scratch/frame globals
through item-total execution, cursor assignments and temporary restoration. -/
theorem rlpListCount_normal_step_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
    (pointer length offset scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (offsetBound : offset.toNat ≤ length.toNat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 18 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpListCountStep = (none,post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"),.var .local (ofString "off")]] =
      some [.val (.word (pointer + offset)),.val (.word (length - offset))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal,offsetLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  have remainingNat : (length - offset).toNat = length.toNat - offset.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr offsetBound)
  have pointerNat : (pointer + offset).toNat = pointer.toNat + offset.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  have nestedNoWrap : (pointer + offset).toNat + (length - offset).toNat < 2^64 := by
    rw [pointerNat,remainingNat]; omega
  rw [source_rlpListCount_step] at run
  have supported : readOnlyMemory rlpListCountUpdates = true := by rw [source_rlpListCount_updates]; rfl
  exact rlpItemTotal_declaration_normal_named_global state post watched different (ofString "total") rlpListCountUpdates supported _
    (pointer + offset) (length - offset) scratch frame ceiling inputLimit args nestedNoWrap (by rw [remainingNat]; omega)
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (by rw [remainingNat]; omega) run

#print axioms rlpListCount_normal_step_named_global
end InitECandidate.Runtime
