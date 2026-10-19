import InitECandidate.Runtime.HtrPcontainerMaskMemory
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrPcontainerMaskCondition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))

theorem htrPcontainer_mask_step_control {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state htrPcontainerMaskBody).1 ≠ some .break ∧
    (evaluateHOLFiniteState state htrPcontainerMaskBody).1 ≠ some .continue := by
  have control : (evaluateHOLFiniteState state htrPcontainerMaskStore).1 = none ∨
      (evaluateHOLFiniteState state htrPcontainerMaskStore).1 = some .error :=
    (evaluate_storeByte_control_frame state _ _).1
  rw [source_htrPcontainer_mask_body,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state htrPcontainerMaskStore with
  | mk result middle =>
    rw [stored] at control
    rcases control with normal | error
    · dsimp only at normal
      subst result
      exact evaluate_noLoopControl _ rfl middle
    · dsimp only at error
      subst result
      simp

/-- Normal completion of the actual bitmap loop preserves every word outside
its 32-byte active-field bitmap. No clock or successful-store premise is added. -/
theorem htrPcontainer_mask_loop_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (active count index watched : BitVec 64)
    (atActive : state.locals.lookup (ofString "act") = some (.val (.word active)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (within : index.toNat ≤ count.toNat) (small : count.toNat ≤ 256)
    (aligned : active.toNat % 8 = 0) (fits : active.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < active.toNat ∨ active.toNat + 32 ≤ watched.toNat)
    (run : evaluateHOLFiniteState state (.while htrPcontainerMaskCondition htrPcontainerMaskBody) = (none,post)) :
    post.memory watched = state.memory watched := by
  let invariant (current : PanSemStateFiniteExact 64 F) : Prop :=
    current.locals.lookup (ofString "act") = some (.val (.word active)) ∧
    current.locals.lookup (ofString "n") = some (.val (.word count)) ∧
    (∃ i : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ count.toNat) ∧
    current.memory watched = state.memory watched
  have preserved := evaluate_normal_while_invariant_by_guard htrPcontainerMaskCondition htrPcontainerMaskBody invariant
    (by
      intro current next flag valid guard nonzero normal
      obtain ⟨activeLocal,countLocal,⟨i,indexLocal,inside⟩,cell⟩ := valid
      have condition := eval_localBound_less current (ofString "i") (ofString "n") .less (Or.inl rfl)
        i count (by omega) (by omega) indexLocal countLocal
      change evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
        htrPcontainerMaskCondition = _ at condition
      have running : i.toNat < count.toNat := by
        by_contra stopped
        rw [condition] at guard
        have : flag = (0#64) := by simpa [stopped] using guard.symm
        exact nonzero this
      have memory := htrPcontainer_mask_step_memory (decClockHOLFinite current) active i watched activeLocal indexLocal
        (by omega) aligned fits outside
      rw [normal] at memory
      have advanced := htrPcontainer_mask_step_index (decClockHOLFinite current) next i indexLocal normal
      have natural : (i + (1#64)).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2^64; omega)]
        rfl
      have keep (key : MlS) (different : key ≠ ofString "i") : next.locals.lookup key = current.locals.lookup key := by
        have kept := evaluate_avoidsLocal_flowing key htrPcontainerMaskBody
          (by
            rw [source_htrPcontainer_mask_body]
            have first : avoidsLocal key htrPcontainerMaskStore = true := by rfl
            rw [avoidsLocal,first]
            simp [avoidsLocal,beq_iff_eq,Ne.symm different]) (decClockHOLFinite current) (by rw [normal]; exact Or.inl rfl)
        rw [normal] at kept
        simpa only [decClockHOLFinite] using kept
      exact ⟨(keep _ (by decide)).trans activeLocal,(keep _ (by decide)).trans countLocal,
        ⟨i + (1#64),advanced,by rw [natural]; omega⟩,memory.trans cell⟩)
    htrPcontainer_mask_step_control state post ⟨atActive,atCount,⟨index,atIndex,within⟩,rfl⟩ run
  exact preserved.2.2.2

#print axioms htrPcontainer_mask_step_control
#print axioms htrPcontainer_mask_loop_normal_memory
end InitECandidate.Runtime
