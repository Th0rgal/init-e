import InitECandidate.Runtime.MerklePaddingBodyMemory
import InitECandidate.Runtime.NormalWhileInvariantByGuard
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem merklePadding_body_globals : OriginalGlobalsFrame merklePaddingBody := by
  rw [source_merklePadding_arguments]
  exact originalGlobalsFrame_sequence _ _ (shaPair_call_globals_frame _)
    (originalGlobalsFrame_leaf _ (by intro watched; rfl))

theorem merklePadding_loop_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator buf zeroHashes initial target watched : BitVec 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atBuf : state.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (atIndex : state.locals.lookup (ofString "d") = some (.val (.word initial)))
    (atTarget : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (small : initial.toNat ≤ target.toNat) (limit : target.toNat ≤ 63)
    (aligned : buf.toNat % 8 = 0) (fits : buf.toNat + 32 ≤ 33806089496)
    (before : watched.toNat < buf.toNat) (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (budget : (target.toNat - initial.toNat) * 137 ≤ state.clock)
    (run : evaluateHOLFiniteState state merklePaddingLoop = (none,post)) :
    post.memory watched = state.memory watched := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧
      current.globals.lookup (ofString "sha_st") = some (.val (.word pointer)) ∧
      current.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)) ∧
      current.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)) ∧
      current.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
      current.locals.lookup (ofString "target") = some (.val (.word target)) ∧ current.code = originalRuntimeCode ∧
      ∃ index : BitVec 64, current.locals.lookup (ofString "d") = some (.val (.word index)) ∧
        index.toNat ≤ target.toNat ∧ (target.toNat - index.toNat) * 137 ≤ current.clock
  have finalInvariant := evaluate_normal_while_invariant_by_guard _ merklePaddingBody Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,pointerLocal,accelLocal,zeroLocal,bufLocal,targetLocal,installed,index,indexLocal,indexBound,remaining⟩ := invariant
    have targetSmall : target.toNat < 2 ^ 63 := by omega
    have condition : evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
        (.cmp .less (.var .local (ofString "d")) (.var .local (ofString "target"))) =
        evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a))
          (.cmp .less (.var .local (ofString "d")) (.const target)) := by
      simp [evalHOLFinite_eq_toExact,evalHOLExact,targetLocal]
    rw [condition,eval_counted_condition current (ofString "d") .less (Or.inl rfl) target index
      targetSmall (by omega) indexLocal] at guard
    have running : index.toNat < target.toNat := by
      by_contra stopped
      exact nonzero (by simpa [stopped] using guard.symm)
    have enough : 136 ≤ (decClockHOLFinite current).clock := by
      change 136 ≤ current.clock - 1
      omega
    have bodyFrame := merklePadding_body_normal_memory (decClockHOLFinite current) next pointer accelerator buf zeroHashes index watched
      pointerLocal accelLocal zeroLocal bufLocal indexLocal aligned fits before accelAligned accelFits pointerFits
      accelOutside pointerOutside installed (by omega) bodyRun
    have kept (key : MlS) (supported : avoidsLocal key merklePaddingBody = true) :
        next.locals.lookup key = current.locals.lookup key := by
      have localFrame := evaluate_avoidsLocal_flowing key merklePaddingBody supported (decClockHOLFinite current)
        (by rw [bodyRun]; exact Or.inl rfl)
      rw [bodyRun] at localFrame
      exact localFrame
    have globals := merklePadding_body_globals (decClockHOLFinite current) installed
    have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite current) merklePaddingBody
    have spent := (merklePadding_counted.run (decClockHOLFinite current) installed index indexLocal enough).1
    rw [bodyRun] at globals metadata spent
    have natural : (index + (1#64)).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]; rfl
    refine ⟨bodyFrame.1.trans memory,?_,?_,?_,(kept _ (by decide)).trans bufLocal,
      (kept _ (by decide)).trans targetLocal,metadata.1.trans installed,index + (1#64),bodyFrame.2,?_,?_⟩
    · rw [globals]; exact pointerLocal
    · rw [globals]; exact accelLocal
    · rw [globals]; exact zeroLocal
    · rw [natural]; omega
    · rw [natural]
      change current.clock - 1 ≤ next.clock + (136 + 0) at spent
      omega)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,atPointer,atAccel,atZero,atBuf,atTarget,code,initial,atIndex,small,budget⟩ run
  exact finalInvariant.1

#print axioms merklePadding_body_globals
#print axioms merklePadding_loop_normal_memory
end InitECandidate.Runtime
