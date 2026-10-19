import InitECandidate.Runtime.RecordHashAllocationMemory
import InitECandidate.Runtime.HeapMarkCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem recordHash_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes input heap out watched count : BitVec 64) (value : ValueHOL 64)
    (steps : List RecordHashStep) (fits : ∀ step ∈ steps, step.Fits count)
    (ctx : RecordHashEntryContext state sha accelerator zeroHashes input heap out watched)
    (small : count.toNat ≤ 134217712) (budget : 1 + (2 + recordHashCost steps) ≤ state.clock)
    (run : evaluateHOLFiniteState state (recordHashBody count steps) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have enough : 1 ≤ state.clock := (Nat.le_add_right 1 _).trans budget
  obtain ⟨marked,_,clock,memory,globals,locals,installed,_,_,declaration⟩ :=
    evaluate_heapMark_call_and_declaration state heap ctx.code ctx.atHeap (by omega)
  change evaluateHOLFiniteState state (recordHashBody count steps) = _ at run
  change evaluateHOLFiniteState state (.decCall (ofString "mark") .one (ofString "heap_mark") [] (recordHashAllocation count steps)) = _ at run
  rw [declaration] at run
  let next := setVarHOLFinite (ofString "mark") (.val (.word heap)) marked
  change (let output := evaluateHOLFiniteState next (recordHashAllocation count steps);
    (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "mark",state.locals.lookup (ofString "mark"))})) =
      (some (.returned value),post) at run
  cases tailRun : evaluateHOLFiniteState next (recordHashAllocation count steps) with
  | mk result inner =>
    rw [tailRun] at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    change result = some (.returned value) at resultEq
    subst result
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
    have remaining : (2 + recordHashCost steps) ≤ next.clock := by
      change _ ≤ marked.clock
      omega
    have nextCtx : RecordHashEntryContext next sha accelerator zeroHashes input heap out watched := {
      atInput := (keep _ (by decide)).trans ctx.atInput
      atOut := (keep _ (by decide)).trans ctx.atOut
      atSha := by change marked.globals.lookup _ = _; rw [globals]; exact ctx.atSha
      atAccel := by change marked.globals.lookup _ = _; rw [globals]; exact ctx.atAccel
      atZero := by change marked.globals.lookup _ = _; rw [globals]; exact ctx.atZero
      atHeap := by change marked.globals.lookup _ = _; rw [globals]; exact ctx.atHeap
      outAligned := ctx.outAligned
      outFits := ctx.outFits
      outOutside := ctx.outOutside
      heapAligned := ctx.heapAligned
      heapFits := ctx.heapFits
      heapBefore := ctx.heapBefore
      accelAligned := ctx.accelAligned
      accelFits := ctx.accelFits
      shaFits := ctx.shaFits
      accelOutside := ctx.accelOutside
      shaOutside := ctx.shaOutside
      code := installed.trans ctx.code }
    have frame := recordHash_allocation_returned_memory next inner sha accelerator zeroHashes input heap out heap watched count value
      steps fits nextCtx (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) small remaining tailRun
    rw [← postEq]
    exact frame.trans (congrFun memory watched)

#print axioms recordHash_body_returned_memory
end InitECandidate.Runtime
