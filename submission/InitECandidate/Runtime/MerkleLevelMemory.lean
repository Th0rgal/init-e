import InitECandidate.Runtime.MerklePairLoopMemory
import InitECandidate.Runtime.MerkleLevelReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleLevel_body_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf cur watched : BitVec 64) (chunks : Nat)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "cur") = some (.val (.word cur)))
    (limit : cur.toNat ≤ chunks)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + chunks * 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : cur.toNat * 137 ≤ state.clock)
    (run : evaluateHOLFiniteState state merkleLevelBody = (none,post)) :
    post.memory watched = state.memory watched := by
  rw [source_merkleLevel_body] at run
  have initialized : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift .lsr (.var .local (ofString "cur")) (.const 1)) = some (.val (.word (cur >>> 1))) := by
    simp [evalHOLExact,atIndex,wordShiftHOL]
  obtain ⟨afterHalf,innerRun,halfScope⟩ := evaluate_dec_word_result_scope state post (ofString "half")
    _ (cur >>> 1) _ none initialized run
  obtain ⟨inner,loopTailRun,indexScope⟩ := evaluate_dec_word_result_scope
    (setVarHOLFinite (ofString "half") (.val (.word (cur >>> 1))) state) afterHalf
    (ofString "j") (.const (0#64)) 0 _ none rfl innerRun
  let entered := setVarHOLFinite (ofString "j") (.val (.word (0#64)))
    (setVarHOLFinite (ofString "half") (.val (.word (cur >>> 1))) state)
  have localHalf : entered.locals.lookup (ofString "half") = some (.val (.word (cur >>> 1))) := by
    simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have halfBound : (cur >>> 1).toNat ≤ cur.toNat := by
    have natural : (cur >>> 1).toNat = cur.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    rw [natural]
    exact Nat.div_le_self _ _
  change evaluateHOLFiniteState entered
    (.seq merklePairLoop (.assign .local (ofString "cur") (.var .local (ofString "half")))) = (none,inner) at loopTailRun
  rw [evaluateHOLFiniteState_seq_line780] at loopTailRun
  cases loopRun : evaluateHOLFiniteState entered merklePairLoop with
  | mk result middle =>
    rw [loopRun] at loopTailRun
    cases result with
    | some result => cases loopTailRun
    | none =>
      have frame := merklePair_loop_normal_memory entered middle pointer accelerator buf 0 (cur >>> 1) watched chunks
        atPointer atAccel
        (by simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atBuf)
        (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) localHalf
        (by simp) (by omega) aligned fits before accelAligned accelFits pointerFits accelOutside pointerOutside code
        (by change ((cur >>> 1).toNat - 0) * 137 ≤ state.clock; omega) loopRun
      dsimp only at loopTailRun
      have memory := evaluate_readOnly_memory (.assign .local (ofString "cur") (.var .local (ofString "half"))) rfl middle
      rw [loopTailRun] at memory
      rw [halfScope,indexScope]
      exact (congrFun memory watched).trans frame

#print axioms merkleLevel_body_normal_memory
end InitECandidate.Runtime
