import InitECandidate.Runtime.Sha256PackLoopMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlockPack_loop_normal_facts {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (initial accelerator watched : BitVec 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word initial)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (small : initial.toNat ≤ 4) (fits : accelerator.toNat + 96 ≤ 33806089496)
    (outside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state
      (.while (.cmp .less (.var .local (ofString "i")) (.const 4)) shaBlockPackBody) = (none,post)) :
    post.memory watched = state.memory watched ∧
      post.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)) ∧
      post.code = originalRuntimeCode ∧
      ∃ index : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ 4 := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧
      current.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)) ∧
      current.code = originalRuntimeCode ∧
      ∃ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ 4
  have finalInvariant := evaluate_normal_while_invariant_by_guard _ shaBlockPackBody Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,global,installed,index,indexLocal,indexBound⟩ := invariant
    have evaluated := eval_counted_condition current (ofString "i") .less (Or.inl rfl) (4 : BitVec 64) index
      (by decide) (by omega) indexLocal
    rw [evaluated] at guard
    have running : index.toNat < 4 := by
      by_contra stopped
      exact nonzero (by simpa [stopped] using guard.symm)
    have bodyFrame := shaBlockPack_body_memory (decClockHOLFinite current) index accelerator watched indexLocal global running fits outside
    have counter := shaBlockPack_counted.run (decClockHOLFinite current) installed index indexLocal (Nat.zero_le _)
    have globals := evaluate_avoidsGlobalAssignment (ofString "sha_accel") shaBlockPackBody rfl (decClockHOLFinite current)
    rw [bodyRun] at bodyFrame counter globals
    obtain ⟨newIndex,newCode⟩ := counter.2.2.2.2 rfl
    have natural : (index + (1#64)).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
      rfl
    exact ⟨bodyFrame.trans memory,globals.trans global,newCode.trans installed,index + (1#64),newIndex,by rw [natural]; omega⟩)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,atAccel,code,initial,atIndex,small⟩ run
  exact finalInvariant

#print axioms shaBlockPack_loop_normal_facts
end InitECandidate.Runtime
