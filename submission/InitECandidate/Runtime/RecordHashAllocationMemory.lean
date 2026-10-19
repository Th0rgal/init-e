import InitECandidate.Runtime.RecordHashSuffixMemory
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure RecordHashEntryContext {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes input heap out watched : BitVec 64) : Prop where
  atInput : state.locals.lookup (ofString "e") = some (.val (.word input))
  atOut : state.locals.lookup (ofString "out") = some (.val (.word out))
  atSha : state.globals.lookup (ofString "sha_st") = some (.val (.word sha))
  atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator))
  atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes))
  atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
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

theorem recordHash_allocation_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes input heap out mark watched count : BitVec 64) (value : ValueHOL 64)
    (steps : List RecordHashStep) (fits : ∀ step ∈ steps, step.Fits count)
    (ctx : RecordHashEntryContext state sha accelerator zeroHashes input heap out watched)
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (small : count.toNat ≤ 134217712) (budget : 2 + recordHashCost steps ≤ state.clock)
    (run : evaluateHOLFiniteState state (recordHashAllocation count steps) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  let argument : ExpHOL 64 := .panop .mul [.const count,.const 32]
  let bytes := count * (32#64)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word bytes)] := by
    simp [argument,bytes,evalListHOLExact,evalHOLExact,panOpHOL,isWfShapeExactHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches state argument (ofString "ch") heap bytes
    (recordHashSuffix steps count) args ctx.code ctx.atHeap ctx.heapFits (by omega)
  obtain ⟨next,allocated,spent,_,agreement,normal⟩ := reaches_returned_continuation state (recordHashAllocation count steps)
    (recordHashSuffix steps count) _ 2 value reached (by rw [run])
  obtain ⟨locals,memory,installed,_,globals,cap,covers,aligned⟩ := allocated
  have keep (key : MlS) (different : key ≠ ofString "ch") : next.locals.lookup key = state.locals.lookup key := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have nonHeap (key : MlS) (different : key ≠ ofString "heap_ptr") : next.globals.lookup key = state.globals.lookup key := by
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have bytesNat : bytes.toNat = count.toNat * 32 := by
    apply BitVec.toNat_mul_of_lt
    change count.toNat * 32 < 2 ^ 64
    omega
  have nextCtx : RecordHashMemoryContext next sha accelerator zeroHashes input heap (allocationEnd heap bytes) out mark watched count := {
    atInput := (keep _ (by decide)).trans ctx.atInput
    atRoots := by rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
    atOut := (keep _ (by decide)).trans ctx.atOut
    atMark := (keep _ (by decide)).trans atMark
    atSha := (nonHeap _ (by decide)).trans ctx.atSha
    atAccel := (nonHeap _ (by decide)).trans ctx.atAccel
    atZero := (nonHeap _ (by decide)).trans ctx.atZero
    atHeap := by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    rootsAligned := ctx.heapAligned
    rootsFits := by rw [bytesNat] at covers; omega
    rootsBefore := ctx.heapBefore
    outAligned := ctx.outAligned
    outFits := ctx.outFits
    outOutside := ctx.outOutside
    heapAligned := aligned
    heapFits := cap
    heapBefore := by have := ctx.heapBefore; omega
    accelAligned := ctx.accelAligned
    accelFits := ctx.accelFits
    shaFits := ctx.shaFits
    accelOutside := ctx.accelOutside
    shaOutside := ctx.shaOutside
    code := installed.trans ctx.code }
  have frame := recordHash_suffix_returned_memory next (evaluateHOLFiniteState next (recordHashSuffix steps count)).2
    sha accelerator zeroHashes input heap (allocationEnd heap bytes) out mark watched count value steps fits nextCtx small (by omega)
    (Prod.ext normal rfl)
  have outputMemory : post.memory = (evaluateHOLFiniteState next (recordHashSuffix steps count)).2.memory := by
    have same := agreement.2.2.1
    rw [run] at same
    exact same
  rw [outputMemory,frame]
  exact congrFun memory watched

#print axioms recordHash_allocation_returned_memory
end InitECandidate.Runtime
