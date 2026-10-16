import InitECandidate.Runtime.StackWorkLeaves
import InitECandidate.Runtime.StackPathWork
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
theorem pathWork_leaf_bound {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) (leaf : workLeaf prog = true) :
    BoundedFlattenProp prog s1 (pathWork prog s1) := by
  apply boundedFlattenProp_mono (two_le_pathWork prog s1)
  cases prog with
  | skip => exact boundedFlattenProp_mono (by decide) (flattenSkip_bounded s1)
  | inst i => exact boundedFlattenProp_mono (by decide) (flattenInst_bounded s1 i)
  | get v name => exact boundedFlattenProp_mono (by decide) (flattenGuardedGet s1 v name)
  | set name v => exact boundedFlattenProp_mono (by decide) (flattenGuardedSet s1 v name)
  | opCurrHeap op v src => exact boundedFlattenProp_mono (by decide) (flattenGuardedOpCurrHeap s1 op v src)
  | call ret dest handler => simp [workLeaf] at leaf
  | seq c1 c2 => simp [workLeaf] at leaf
  | ite cmp reg ri c1 c2 => simp [workLeaf] at leaf
  | loop body => simp [workLeaf] at leaf
  | jumpLower r1 r2 dest => simp [workLeaf] at leaf
  | alloc k => exact boundedFlattenProp_mono (by decide) (flattenGuardedAlloc s1 k)
  | storeConsts a b stub => exact boundedFlattenProp_mono (by decide) (flattenGuardedStoreConsts s1 a b stub)
  | raise v => exact boundedFlattenProp_mono (by decide) (flattenRaise_bounded s1 v)
  | ret v => exact boundedFlattenProp_mono (by decide) (flattenRet_bounded s1 v)
  | «break» k => exact boundedFlattenProp_mono (by decide) (flattenBreak_bounded s1 k)
  | «continue» k => exact boundedFlattenProp_mono (by decide) (flattenContinue_bounded s1 k)
  | ffi f ptr len ptr2 len2 ret => exact boundedFlattenProp_mono (by decide) (flattenFfi_bounded s1 f ptr len ptr2 len2 ret)
  | tick => exact boundedFlattenProp_mono (by decide) (flattenTick_bounded s1)
  | locValue reg l1 l2 => exact boundedFlattenProp_mono (by decide) (flattenLocValue_bounded s1 reg l1 l2)
  | install ptr len dptr dlen ret => exact boundedFlattenProp_mono (by decide) (flattenInstall_bounded s1 ptr len dptr dlen ret)
  | shMemOp op reg addr =>
    rcases addr with ⟨a, w⟩
    exact boundedFlattenProp_mono (by decide) (flattenShMemOp_bounded s1 op reg a w)
  | codeBufferWrite r1 r2 => exact boundedFlattenProp_mono (by decide) (flattenCodeBufferWrite_bounded s1 r1 r2)
  | dataBufferWrite r1 r2 => exact boundedFlattenProp_mono (by decide) (flattenGuardedDataBufferWrite s1 r1 r2)
  | rawCall dest => simp [workLeaf] at leaf
  | stackAlloc k => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackAlloc s1 k)
  | stackFree k => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackFree s1 k)
  | stackStore r k => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackStore s1 r k)
  | stackStoreAny r rn => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackStoreAny s1 r rn)
  | stackLoad r k => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackLoad s1 r k)
  | stackLoadAny r rn => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackLoadAny s1 r rn)
  | stackGetSize r => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackGetSize s1 r)
  | stackSetSize r => exact boundedFlattenProp_mono (by decide) (flattenGuardedStackSetSize s1 r)
  | bitmapLoad r v => exact boundedFlattenProp_mono (by decide) (flattenGuardedBitmapLoad s1 r v)
  | halt v => exact boundedFlattenProp_mono (by decide) (flattenHalt_bounded s1 v)

#print axioms pathWork_leaf_bound
end InitECandidate.Runtime.StackToLab
