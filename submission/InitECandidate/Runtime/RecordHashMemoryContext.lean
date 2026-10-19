import InitECandidate.Runtime.HtrRequestRecordsCallBound
import InitECandidate.Runtime.HtrBytesVectorMemory
import InitECandidate.Runtime.HtrBytesVectorGlobals
import InitECandidate.Runtime.HtrU64AtMemoryFrame
import InitECandidate.Runtime.MemcpyDecodedFrame
import InitECandidate.Runtime.KeccakGlobalsFrame
namespace InitECandidate.Runtime
set_option maxRecDepth 100000
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure RecordHashMemoryContext {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes input roots heap out mark watched count : BitVec 64) : Prop where
  atInput : state.locals.lookup (ofString "e") = some (.val (.word input))
  atRoots : state.locals.lookup (ofString "ch") = some (.val (.word roots))
  atOut : state.locals.lookup (ofString "out") = some (.val (.word out))
  atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark))
  atSha : state.globals.lookup (ofString "sha_st") = some (.val (.word sha))
  atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator))
  atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes))
  atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  rootsAligned : roots.toNat % 8 = 0
  rootsFits : roots.toNat + count.toNat * 32 ≤ 33806089496
  rootsBefore : watched.toNat < roots.toNat
  outAligned : out.toNat % 8 = 0
  outFits : out.toNat + 32 ≤ 33806089496
  outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat
  heapAligned : heap.toNat % 8 = 0
  heapFits : heap.toNat ≤ 33806089496
  heapBefore : watched.toNat < heap.toNat
  accelAligned : accelerator.toNat % 8 = 0
  accelFits : accelerator.toNat + 96 ≤ 33806089496
  shaFits : sha.toNat + 64 ≤ 33806089496
  accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat
  shaOutside : watched.toNat < sha.toNat ∨ sha.toNat + 64 ≤ watched.toNat
  code : state.code = originalRuntimeCode

theorem RecordHashMemoryContext.after_call {F : Type} {state post : PanSemStateFiniteExact 64 F}
    {sha accelerator zeroHashes input roots heap out mark watched count : BitVec 64}
    (ctx : RecordHashMemoryContext state sha accelerator zeroHashes input roots heap out mark watched count)
    (locals : ∀ key, post.locals.lookup key = state.locals.lookup key)
    (globals : post.globals = state.globals) (code : post.code = state.code) :
    RecordHashMemoryContext post sha accelerator zeroHashes input roots heap out mark watched count := by
  exact ⟨(locals _).trans ctx.atInput,(locals _).trans ctx.atRoots,(locals _).trans ctx.atOut,(locals _).trans ctx.atMark,
    (by rw [globals]; exact ctx.atSha),(by rw [globals]; exact ctx.atAccel),
    (by rw [globals]; exact ctx.atZero),(by rw [globals]; exact ctx.atHeap),
    ctx.rootsAligned,ctx.rootsFits,ctx.rootsBefore,ctx.outAligned,ctx.outFits,ctx.outOutside,
    ctx.heapAligned,ctx.heapFits,ctx.heapBefore,ctx.accelAligned,ctx.accelFits,ctx.shaFits,ctx.accelOutside,ctx.shaOutside,
    code.trans ctx.code⟩

def RecordHashStep.outputOffset : RecordHashStep → BitVec 64
  | .vector _ _ o => o
  | .copy _ o => o
  | .uint _ o => o

def RecordHashStep.Fits (count : BitVec 64) (step : RecordHashStep) : Prop :=
  step.Small ∧ step.outputOffset.toNat % 8 = 0 ∧ step.outputOffset.toNat + 32 ≤ count.toNat * 32

/-- A fixed record hashing operation preserves an earlier watched cell and all
caller globals/locals on normal return. Source reads may reject. -/
theorem recordHash_step_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes input roots heap out mark watched count : BitVec 64)
    (ctx : RecordHashMemoryContext state sha accelerator zeroHashes input roots heap out mark watched count)
    (step : RecordHashStep) (fits : step.Fits count) (budget : step.cost ≤ state.clock)
    (run : evaluateHOLFiniteState state (.call (some (none,none)) step.function step.arguments) = (none,post)) :
    post.memory watched = state.memory watched ∧ post.globals = state.globals ∧
      ∀ key, post.locals.lookup key = state.locals.lookup key := by
  have natural : (roots + step.outputOffset).toNat = roots.toNat + step.outputOffset.toNat := by
    apply BitVec.toNat_add_of_lt
    have := ctx.rootsFits
    have := fits.2.2
    omega
  have aligned : (roots + step.outputOffset).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,ctx.rootsAligned,fits.2.1]
  have destinationFits : (roots + step.outputOffset).toNat + 32 ≤ 33806089496 := by
    rw [natural]
    have := ctx.rootsFits
    have := fits.2.2
    omega
  have outside : watched.toNat < (roots + step.outputOffset).toNat := by
    rw [natural]
    have := ctx.rootsBefore
    omega
  have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key (.call (some (none,none)) step.function step.arguments) rfl state
      (by rw [run]; exact Or.inl rfl)
    simpa only [run] using frame
  refine ⟨?_,?_,keep⟩
  · cases step with
    | vector i n o =>
      have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (RecordHashStep.vector i n o).arguments =
          some [.val (.word (input + i)),.val (.word n),.val (.word (roots + o))] := by
        simp only [RecordHashStep.arguments,evalListHOLFinite,evalListHOLExact,
          recordHashAddress_eval state _ input i ctx.atInput,recordHashAddress_eval state _ roots o ctx.atRoots,evalHOLExact]
      exact htrBytesVector_call_normal_memory state post _ sha accelerator zeroHashes (input+i) n heap (roots+o) watched args
        ctx.atSha ctx.atAccel ctx.atZero ctx.atHeap aligned destinationFits (Or.inl outside) fits.1 ctx.heapAligned ctx.heapFits
        ctx.heapBefore ctx.accelAligned ctx.accelFits ctx.shaFits ctx.accelOutside ctx.shaOutside ctx.code budget run
    | copy i o =>
      have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (RecordHashStep.copy i o).arguments =
          some [.val (.word (roots + o)),.val (.word (input + i)),.val (.word (32#64))] := by
        simp only [RecordHashStep.arguments,evalListHOLFinite,evalListHOLExact,
          recordHashAddress_eval state _ input i ctx.atInput,recordHashAddress_eval state _ roots o ctx.atRoots,evalHOLExact]
        rfl
      have separate := memcpy_interval_separate (roots+o) (32#64) watched aligned destinationFits (Or.inl outside)
      exact memcpy_call_normal_memory state post _ (roots+o) (input+i) (32#64) watched args ctx.code
        (fun offset inside => (separate offset inside).1) (fun offset inside => (separate offset inside).2)
        (by decide) budget run
    | uint i o =>
      have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (RecordHashStep.uint i o).arguments = some [.val (.word (input+i)),.val (.word (roots+o))] := by
        simp only [RecordHashStep.arguments,evalListHOLFinite,evalListHOLExact,
          recordHashAddress_eval state _ input i ctx.atInput,recordHashAddress_eval state _ roots o ctx.atRoots]
      exact htrU64At_call_normal_memory state post _ (input+i) (roots+o) watched args ctx.code aligned destinationFits
        (Or.inl outside) budget run
  · cases step with
    | vector i n o =>
      have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
          (RecordHashStep.vector i n o).arguments =
          some [.val (.word (input + i)),.val (.word n),.val (.word (roots + o))] := by
        simp only [RecordHashStep.arguments,evalListHOLFinite,evalListHOLExact,
          recordHashAddress_eval state _ input i ctx.atInput,recordHashAddress_eval state _ roots o ctx.atRoots,evalHOLExact]
      exact htrBytesVector_call_normal_globals state post _ (input+i) n (roots+o) heap args ctx.atHeap ctx.code run
    | copy i o =>
      have frame := memcpy_call_globals_frame (RecordHashStep.copy i o).arguments state ctx.code
      simp only [RecordHashStep.function] at run
      simpa only [run] using frame
    | uint i o =>
      have frame := htrU64At_call_globals (RecordHashStep.uint i o).arguments state ctx.code
      simp only [RecordHashStep.function] at run
      simpa only [run] using frame

#print axioms RecordHashMemoryContext.after_call
#print axioms recordHash_step_normal_memory
end InitECandidate.Runtime
