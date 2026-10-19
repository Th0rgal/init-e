import InitECandidate.Runtime.MerklePairMemory
import InitECandidate.Runtime.NormalWhileInvariantByGuard
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merklePair_body_globals : OriginalGlobalsFrame merklePairBody := by
  rw [source_merklePair_arguments]
  exact originalGlobalsFrame_sequence _ _ (shaPair_call_globals_frame _)
    (originalGlobalsFrame_leaf _ (by intro watched; rfl))

theorem merklePair_loop_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf initial half watched : BitVec 64) (chunks : Nat)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "j") = some (.val (.word initial)))
    (atHalf : state.locals.lookup (ofString "half") = some (.val (.word half)))
    (small : initial.toNat ≤ half.toNat) (limit : half.toNat ≤ chunks)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + chunks * 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : (half.toNat - initial.toNat) * 137 ≤ state.clock)
    (run : evaluateHOLFiniteState state merklePairLoop = (none,post)) :
    post.memory watched = state.memory watched := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧
      current.globals.lookup (ofString "sha_st") = some (.val (.word pointer)) ∧
      current.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)) ∧
      current.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
      current.locals.lookup (ofString "half") = some (.val (.word half)) ∧ current.code = originalRuntimeCode ∧
      ∃ index : BitVec 64, current.locals.lookup (ofString "j") = some (.val (.word index)) ∧
        index.toNat ≤ half.toNat ∧ (half.toNat - index.toNat) * 137 ≤ current.clock
  have finalInvariant := evaluate_normal_while_invariant_by_guard _ merklePairBody Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,pointerLocal,accelLocal,bufLocal,halfLocal,installed,index,indexLocal,indexBound,remaining⟩ := invariant
    have halfSmall : half.toNat < 2 ^ 63 := by omega
    have condition : evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
        (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half"))) =
        evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
          (.cmp .less (.var .local (ofString "j")) (.const half)) := by
      simp [evalHOLFinite_eq_toExact,evalHOLExact,halfLocal]
    rw [condition,eval_counted_condition current (ofString "j") .less (Or.inl rfl) half index
      halfSmall (by omega) indexLocal] at guard
    have running : index.toNat < half.toNat := by
      by_contra stopped
      exact nonzero (by simpa [stopped] using guard.symm)
    have enough : 136 ≤ (decClockHOLFinite current).clock := by
      change 136 ≤ current.clock - 1
      omega
    have bodyFrame := merklePair_body_normal_memory (decClockHOLFinite current) next pointer accelerator buf index watched chunks
      pointerLocal accelLocal bufLocal indexLocal (by omega) aligned fits before accelAligned accelFits pointerFits
      accelOutside pointerOutside installed (by omega) bodyRun
    have kept (key : MlS) (supported : avoidsLocal key merklePairBody = true) :
        next.locals.lookup key = current.locals.lookup key := by
      have localFrame := evaluate_avoidsLocal_flowing key merklePairBody supported (decClockHOLFinite current)
        (by rw [bodyRun]; exact Or.inl rfl)
      rw [bodyRun] at localFrame
      exact localFrame
    have globals := merklePair_body_globals (decClockHOLFinite current) installed
    have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite current) merklePairBody
    have spent := (merklePair_counted.run (decClockHOLFinite current) installed index indexLocal enough).1
    rw [bodyRun] at globals metadata spent
    have natural : (index + (1#64)).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]; rfl
    refine ⟨bodyFrame.1.trans memory,?_,?_,(kept _ (by decide)).trans bufLocal,
      (kept _ (by decide)).trans halfLocal,metadata.1.trans installed,index + (1#64),bodyFrame.2,?_,?_⟩
    · rw [globals]; exact pointerLocal
    · rw [globals]; exact accelLocal
    · rw [natural]; omega
    · rw [natural]
      change current.clock - 1 ≤ next.clock + (136 + 0) at spent
      omega)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,atPointer,atAccel,atBuf,atHalf,code,initial,atIndex,small,budget⟩ run
  exact finalInvariant.1

#print axioms merklePair_body_globals
#print axioms merklePair_loop_normal_memory
end InitECandidate.Runtime
