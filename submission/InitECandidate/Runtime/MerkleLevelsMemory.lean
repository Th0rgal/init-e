import InitECandidate.Runtime.MerkleLevelMemory
import InitECandidate.Runtime.MerkleLevelsInputBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merkleLevel_body_globals : OriginalGlobalsFrame merkleLevelBody := by
  rw [source_merkleLevel_body]
  apply originalGlobalsFrame_declaration
  apply originalGlobalsFrame_declaration
  apply originalGlobalsFrame_sequence
  · exact originalGlobalsFrame_while _ _ merklePair_body_globals
  · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem merkleLevels_loop_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf initial watched : BitVec 64) (chunks : Nat)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "cur") = some (.val (.word initial)))
    (small : initial.toNat ≤ chunks)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + chunks * 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : initial.toNat * (chunks * 137 + 1) ≤ state.clock)
    (run : evaluateHOLFiniteState state (.while merkleLevelsCondition merkleLevelBody) = (none,post)) :
    post.memory watched = state.memory watched := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧
      current.globals.lookup (ofString "sha_st") = some (.val (.word pointer)) ∧
      current.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)) ∧
      current.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧ current.code = originalRuntimeCode ∧
      ∃ cur : BitVec 64, current.locals.lookup (ofString "cur") = some (.val (.word cur)) ∧
        cur.toNat ≤ chunks ∧ cur.toNat * (chunks * 137 + 1) ≤ current.clock
  have finalInvariant := evaluate_normal_while_invariant_by_guard merkleLevelsCondition merkleLevelBody Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,pointerLocal,accelLocal,bufLocal,installed,cur,counter,bounded,remaining⟩ := invariant
    have curSmall : cur.toNat < 2 ^ 63 := by omega
    rw [eval_merkleLevels_condition current cur counter curSmall] at guard
    have running : 1 < cur.toNat := by
      by_contra stopped
      exact nonzero (by simpa [stopped] using guard.symm)
    have upperCost : cur.toNat * 137 ≤ chunks * 137 := Nat.mul_le_mul_right _ bounded
    have creditStart : chunks * 137 + 1 ≤ cur.toNat * (chunks * 137 + 1) := by
      exact Nat.le_mul_of_pos_left _ (by omega)
    have enough : cur.toNat * 137 ≤ (decClockHOLFinite current).clock := by
      change cur.toNat * 137 ≤ current.clock - 1
      omega
    have bodyFrame := merkleLevel_body_normal_memory (decClockHOLFinite current) next pointer accelerator buf cur watched chunks
      pointerLocal accelLocal bufLocal counter bounded aligned fits before accelAligned accelFits pointerFits
      accelOutside pointerOutside installed enough bodyRun
    have kept := evaluate_avoidsLocal_flowing (ofString "buf") merkleLevelBody (by decide) (decClockHOLFinite current)
      (by rw [bodyRun]; exact Or.inl rfl)
    have globals := merkleLevel_body_globals (decClockHOLFinite current) installed
    have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite current) merkleLevelBody
    have spent := (runBounded_merkleLevel (decClockHOLFinite current) cur counter curSmall installed enough).1
    rw [bodyRun] at kept globals metadata spent
    have nextCounter := merkleLevel_body_normal (decClockHOLFinite current) next cur counter bodyRun
    have natural : (cur >>> 1).toNat = cur.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    have decreases : (cur >>> 1).toNat + 1 ≤ cur.toNat := by
      rw [natural]
      have := Nat.div_lt_self (by omega : 0 < cur.toNat) (by decide : 1 < 2)
      omega
    have credit := Nat.mul_le_mul_right (chunks * 137 + 1) decreases
    rw [Nat.add_mul] at credit
    refine ⟨bodyFrame.trans memory,?_,?_,kept.trans bufLocal,metadata.1.trans installed,
      cur >>> 1,nextCounter,by omega,?_⟩
    · rw [globals]; exact pointerLocal
    · rw [globals]; exact accelLocal
    · change current.clock - 1 ≤ next.clock + cur.toNat * 137 at spent
      omega)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,atPointer,atAccel,atBuf,code,initial,atIndex,small,budget⟩ run
  exact finalInvariant.1

#print axioms merkleLevel_body_globals
#print axioms merkleLevels_loop_normal_memory
end InitECandidate.Runtime
