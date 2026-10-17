import InitECandidate.Runtime.RlpListCountLoopBound
import InitECandidate.Runtime.RlpSlicesLoopBound
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- At the common terminal cursor, the actual fill loop returns the complete
input-bounded slice prefix without taking another iteration. -/
theorem rlpCountFill_loop_done {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer length array count finalCount : BitVec 64)
    (checkedOffset : checked.locals.lookup (ofString "off") = some (.val (.word length)))
    (checkedLength : checked.locals.lookup (ofString "len") = some (.val (.word length)))
    (checkedCount : checked.locals.lookup (ofString "count") = some (.val (.word count)))
    (finalLocal : checkedPost.locals.lookup (ofString "count") = some (.val (.word finalCount)))
    (uncheckedIndex : unchecked.locals.lookup (ofString "i") = some (.val (.word count)))
    (uncheckedCount : unchecked.locals.lookup (ofString "count") = some (.val (.word finalCount)))
    (filled : RlpSliceInputPrefix unchecked array pointer length count.toNat)
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpSlicesLoop = (none,uncheckedPost)) :
    count = finalCount ∧ uncheckedPost = unchecked ∧
    RlpSliceInputPrefix uncheckedPost array pointer length finalCount.toNat := by
  have checkedGuard : evalHOLFinite checked (h := fun a => Classical.propDecidable (checked.memaddrs a))
      (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) = some (.val (.word 0)) := by
    simp [evalHOLFinite,evalHOLExact,checkedOffset,checkedLength,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_rlpListCount_loop,evaluateHOLFiniteState_while_total,checkedGuard] at checkedRun
  have checkedSame : checked = checkedPost := (Prod.mk.inj checkedRun).2
  have equal : count = finalCount := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj
    (checkedCount.symm.trans (by rw [checkedSame]; exact finalLocal))))
  have uncheckedGuard : evalHOLFinite unchecked (h := fun a => Classical.propDecidable (unchecked.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) = some (.val (.word 0)) := by
    simp [evalHOLFinite,evalHOLExact,uncheckedIndex,uncheckedCount,equal,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_rlpSlices_loop,evaluateHOLFiniteState_while_total,uncheckedGuard] at uncheckedRun
  have uncheckedSame : unchecked = uncheckedPost := (Prod.mk.inj uncheckedRun).2
  refine ⟨equal,uncheckedSame.symm,?_⟩
  rw [← uncheckedSame,← equal]
  exact filled

#print axioms rlpCountFill_loop_done
end InitECandidate.Runtime
