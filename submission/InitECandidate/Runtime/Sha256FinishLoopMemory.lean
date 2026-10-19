import InitECandidate.Runtime.Sha256FinishBodyMemory
import InitECandidate.Runtime.NormalWhileInvariantByGuard
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaFinish_loop_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer out initial watched : BitVec 64)
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word initial)))
    (small : initial.toNat ≤ 8) (aligned : out.toNat % 8 = 0) (fits : out.toNat + 32 ≤ 33806089496)
    (outside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.while (.cmp .less (.var .local (ofString "i")) (.const 8)) shaFinishBody) = (none,post)) :
    post.memory watched = state.memory watched := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧
      current.locals.lookup (ofString "stp") = some (.val (.word pointer)) ∧
      current.locals.lookup (ofString "out") = some (.val (.word out)) ∧ current.code = originalRuntimeCode ∧
      ∃ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ 8
  have finalInvariant := evaluate_normal_while_invariant_by_guard _ shaFinishBody Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,pointerLocal,outLocal,installed,index,indexLocal,indexBound⟩ := invariant
    rw [eval_counted_condition current (ofString "i") .less (Or.inl rfl) (8 : BitVec 64) index (by decide) (by omega) indexLocal] at guard
    have running : index.toNat < 8 := by
      by_contra stopped
      exact nonzero (by simpa [stopped] using guard.symm)
    have bodyFrame := shaFinish_body_normal_memory (decClockHOLFinite current) next pointer out index watched
      pointerLocal outLocal indexLocal running aligned fits outside installed bodyRun
    have kept (key : MlS) (supported : avoidsLocal key shaFinishBody = true) :
        next.locals.lookup key = current.locals.lookup key := by
      have localFrame := evaluate_avoidsLocal_flowing key shaFinishBody supported (decClockHOLFinite current)
        (by rw [bodyRun]; exact Or.inl rfl)
      rw [bodyRun] at localFrame
      exact localFrame
    have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite current) shaFinishBody
    rw [bodyRun] at metadata
    have natural : (index + (1 : BitVec 64)).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
      rfl
    exact ⟨bodyFrame.1.trans memory,(kept _ (by decide)).trans pointerLocal,(kept _ (by decide)).trans outLocal,
      metadata.1.trans installed,index + 1,bodyFrame.2,by rw [natural]; omega⟩)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,atPointer,atOut,code,initial,atIndex,small⟩ run
  exact finalInvariant.1

#print axioms shaFinish_loop_normal_memory
end InitECandidate.Runtime
