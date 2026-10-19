import InitECandidate.Runtime.HtrPcontainerSource
import InitECandidate.Runtime.ByteStoreMemoryFrame
import InitECandidate.Runtime.MemcpyIntervalFrame
import InitECandidate.Runtime.NormalWhileInvariantByGuard
import InitECandidate.Runtime.LocalBoundLoop
import InitECandidate.Runtime.HtabGrowRehash
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrPcontainerMaskValue : ExpHOL 64 :=
  match htrPcontainerMaskStore with | .storeByte _ value => value | _ => .const 0

theorem htrPcontainer_mask_step_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (active index watched : BitVec 64)
    (atActive : state.locals.lookup (ofString "act") = some (.val (.word active)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (small : index.toNat < 256) (aligned : active.toNat % 8 = 0)
    (fits : active.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < active.toNat ∨ active.toNat + 32 ≤ watched.toNat) :
    (evaluateHOLFiniteState state htrPcontainerMaskBody).2.memory watched = state.memory watched := by
  have shiftNat : (index >>> 3).toNat = index.toNat / 8 := by
    simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have shiftSmall : (index >>> 3).toNat < 32 := by rw [shiftNat]; omega
  have shiftWord : index >>> 3 = BitVec.ofNat 64 (index.toNat / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [shiftNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have destination : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .add [.var .local (ofString "act"),.shift .lsr (.var .local (ofString "i")) (.const 3)]) =
      some (.val (.word (active + (index >>> 3)))) := by
    simp [evalHOLExact,evalListHOLExact,atActive,atIndex,wordShiftHOL,wordOpHOL,wordOp,valueIsWord,valueWord]
  have separate := (memcpy_interval_separate active (32#64) watched aligned fits outside
    (index.toNat / 8) (by change index.toNat / 8 < 32; omega)).2
  rw [← shiftWord] at separate
  have frame := evaluate_storeByte_memory_frame state _ htrPcontainerMaskValue (active + (index >>> 3)) watched destination separate
  rw [source_htrPcontainer_mask_body,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state htrPcontainerMaskStore with
  | mk result middle =>
    change (evaluateHOLFiniteState state htrPcontainerMaskStore).2.memory watched = _ at frame
    rw [stored] at frame
    cases result with
    | some stopped => exact frame
    | none =>
      have readonly := evaluate_readOnly_memory
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) rfl middle
      exact (congrFun readonly watched).trans frame

theorem htrPcontainer_mask_step_index {F : Type} (state post : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (run : evaluateHOLFiniteState state htrPcontainerMaskBody = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + (1#64)))) := by
  rw [source_htrPcontainer_mask_body,evaluateHOLFiniteState_seq_line780] at run
  cases stored : evaluateHOLFiniteState state htrPcontainerMaskStore with
  | mk result middle =>
    rw [stored] at run
    cases result with
    | some stopped => cases run
    | none =>
      have locals : (evaluateHOLFiniteState state htrPcontainerMaskStore).2.locals = state.locals :=
        (evaluate_storeByte_control_frame state _ _).2.2.1
      rw [stored] at locals
      dsimp only at run
      rw [evaluate_increment_local middle (ofString "i") index (by rw [locals]; exact atIndex)] at run
      cases run
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms htrPcontainer_mask_step_memory
#print axioms htrPcontainer_mask_step_index
end InitECandidate.Runtime
