import InitECandidate.Runtime.HtrRequestListSuffixBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.HeapMarkDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure RequestListInputs {F : Type} (state : PanSemStateFiniteExact 64 F) (kind pointer size count out : BitVec 64) : Prop where
  kindLocal : state.locals.lookup (ofString "kind") = some (.val (.word kind))
  pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer))
  sizeLocal : state.locals.lookup (ofString "sz") = some (.val (.word size))
  countLocal : state.locals.lookup (ofString "n") = some (.val (.word count))
  outLocal : state.locals.lookup (ofString "out") = some (.val (.word out))

def htrRequestListAllocationCost (count : BitVec 64) : Nat := 2 + htrRequestListSuffixCost count
def htrRequestListBodyCost (count : BitVec 64) : Nat := 1 + htrRequestListAllocationCost count

theorem runBounded_htrRequestList_allocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind pointer size count out heap : BitVec 64) (inputs : RequestListInputs state kind pointer size count out)
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : count.toNat ≤ 134217712) (cap : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrRequestListAllocationCost count ≤ state.clock) :
    RunBounded state (htrRequestListAt 1) (htrRequestListAllocationCost count) := by
  let argument : ExpHOL 64 := .op .add [.panop .mul [.var .local (ofString "n"),.const 32],.const 32]
  let bytes := count * (32#64) + (32#64)
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word bytes)] := by
    simp [argument,bytes,evalListHOLExact,evalHOLExact,inputs.countLocal,panOpHOL,wordOpHOL,wordOp,
      isWfShapeExactHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches state argument (ofString "roots") heap bytes
    (htrRequestListAt 2) args code hh cap (by change 2 + htrRequestListSuffixCost count ≤ state.clock at budget; omega)
  rw [← source_htrRequestList_alloc] at reached
  exact evaluate_reaches_terminal_bounded state (htrRequestListAt 1) (htrRequestListAt 2) _ 2 _ budget reached (by
    intro ready facts remaining
    obtain ⟨locals,_,installed,_,globals,newCap,_,_⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "roots") : ready.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    rw [source_htrRequestList_zero]
    apply RunBounded.decConst
    let next := setVarHOLFinite (ofString "i") (.val (.word (0#64))) ready
    have retained (key : MlS) (ni : key ≠ ofString "i") (nr : key ≠ ofString "roots") :
        next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni]
      exact keep key nr
    have valid : HtrRequestListState kind pointer size heap (allocationEnd heap bytes) count next count.toNat := {
      heapGlobal := by change ready.globals.lookup _ = _; rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      pointerLocal := (retained _ (by decide) (by decide)).trans inputs.pointerLocal
      kindLocal := (retained _ (by decide) (by decide)).trans inputs.kindLocal
      sizeLocal := (retained _ (by decide) (by decide)).trans inputs.sizeLocal
      rootsLocal := by simp (config := {decide := true}) [next,setVarHOLFinite,locals,HolFiniteMapExact.lookup_update,FUPDATE]
      countLocal := (retained _ (by decide) (by decide)).trans inputs.countLocal
      cursor := ⟨0#64,by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],by simp,by simp⟩ }
    exact runBounded_htrRequestList_suffix next kind pointer size heap (allocationEnd heap bytes) count out small newCap
      (installed.trans code) valid ((retained _ (by decide) (by decide)).trans inputs.outLocal) remaining)

theorem runBounded_htrRequestList_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind pointer size count out heap : BitVec 64) (inputs : RequestListInputs state kind pointer size count out)
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : count.toNat ≤ 134217712) (cap : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrRequestListBodyCost count ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_request_list) (htrRequestListBodyCost count) := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (htrRequestListAt 0) (htrRequestListBodyCost count)
  have reached := evaluate_heapMark_declaration_reaches state (ofString "mark") heap (htrRequestListAt 1) code hh
    (by change 1 + htrRequestListAllocationCost count ≤ state.clock at budget; omega)
  rw [← source_htrRequestList_mark] at reached
  exact evaluate_reaches_terminal_bounded state (htrRequestListAt 0) (htrRequestListAt 1) _ 1 _ budget reached (by
    intro next facts remaining
    obtain ⟨locals,_,globals,installed,_⟩ := facts
    have keep (key : MlS) (different : key ≠ ofString "mark") : next.locals.lookup key = state.locals.lookup key := by
      rw [locals]
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    exact runBounded_htrRequestList_allocation next kind pointer size count out heap
      ⟨(keep _ (by decide)).trans inputs.kindLocal,(keep _ (by decide)).trans inputs.pointerLocal,
        (keep _ (by decide)).trans inputs.sizeLocal,(keep _ (by decide)).trans inputs.countLocal,
        (keep _ (by decide)).trans inputs.outLocal⟩ (by rw [globals]; exact hh) small cap (installed.trans code) remaining)

#print axioms runBounded_htrRequestList_allocation
#print axioms runBounded_htrRequestList_body
end InitECandidate.Runtime
