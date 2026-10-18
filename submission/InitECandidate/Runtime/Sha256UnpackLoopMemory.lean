import InitECandidate.Runtime.Sha256UnpackBodyMemory
import InitECandidate.Runtime.Sha256BlockBound
import InitECandidate.Runtime.NormalWhileInvariantByGuard
import InitECandidate.Runtime.NoTopBreak
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlockUnpack_counted : NestedCountedBody (ofString "i") 1 shaBlockUnpackBody 0 := by
  rw [source_shaBlock_unpack_body]
  apply NestedCountedBody.dec _ _ _ (by decide)
  apply NestedCountedBody.base
  apply CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ (by decide)) (by decide) (by decide)
  exact CountedBody.seq (a := 0) (b := 0) _ (ProgBounded.straight _ (by decide)) (by decide) (by decide) CountedBody.incr

/-- Every normal exit of the actual four-word packing loop preserves memory
outside its pointer buffer, carrying the real bounded index throughout. -/
theorem shaBlockUnpack_loop_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (initial pointer watched : BitVec 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word initial)))
    (atPointer : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (small : initial.toNat ≤ 4) (fits : pointer.toNat + 64 ≤ 33806089496)
    (outside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state
      (.while (.cmp .less (.var .local (ofString "i")) (.const 4)) shaBlockUnpackBody) = (none,post)) :
    post.memory watched = state.memory watched := by
  let Inv := fun current : PanSemStateFiniteExact 64 F =>
    current.memory watched = state.memory watched ∧
      current.locals.lookup (ofString "stp") = some (.val (.word pointer)) ∧
      current.code = originalRuntimeCode ∧
      ∃ index : BitVec 64, current.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ 4
  have finalInvariant := evaluate_normal_while_invariant_by_guard _ shaBlockUnpackBody Inv (by
    intro current next flag invariant guard nonzero bodyRun
    obtain ⟨memory,global,installed,index,indexLocal,indexBound⟩ := invariant
    have evaluated := eval_counted_condition current (ofString "i") .less (Or.inl rfl) (4 : BitVec 64) index
      (by decide) (by omega) indexLocal
    rw [evaluated] at guard
    have running : index.toNat < 4 := by
      by_contra stopped
      exact nonzero (by simpa [stopped] using guard.symm)
    have bodyFrame := shaBlockUnpack_body_memory (decClockHOLFinite current) index pointer watched indexLocal global running fits outside
    have counter := shaBlockUnpack_counted.run (decClockHOLFinite current) installed index indexLocal (Nat.zero_le _)
    have globals := evaluate_avoidsLocal_flowing (ofString "stp") shaBlockUnpackBody (by decide)
      (decClockHOLFinite current) (by rw [bodyRun]; exact Or.inl rfl)
    rw [bodyRun] at bodyFrame counter globals
    obtain ⟨newIndex,newCode⟩ := counter.2.2.2.2 rfl
    have natural : (index + (1#64)).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
      rfl
    exact ⟨bodyFrame.trans memory,globals.trans global,newCode.trans installed,index + (1#64),newIndex,by rw [natural]; omega⟩)
    (by intro current; exact ⟨evaluate_noTopBreak _ (by decide) current,evaluate_noTopContinue _ (by decide) current⟩)
    state post ⟨rfl,atPointer,code,initial,atIndex,small⟩ run
  exact finalInvariant.1

#print axioms shaBlockUnpack_counted
#print axioms shaBlockUnpack_loop_normal_memory
end InitECandidate.Runtime
