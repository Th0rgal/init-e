import InitECandidate.Runtime.NormalRelLocalCall
import InitECandidate.Runtime.HtabNewTop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
/-- Concrete typed, aligned, capped allocator frontier; no reserve requirement. -/
def StateInitHeapReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
 ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr")=some (.val (.word p)) ∧
 p.toNat%8=0 ∧ p.toNat≤33806089496

/-- A normal actual assignment call inherits the installed callee's checked heap
contract when its assignment destination is distinct from heap_ptr. -/
theorem state_init_assignment_call_heap {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (kind : VarKind) (name function : MlS) (arguments : List (ExpHOL 64))
 (parameters : List (MlS×ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
 (installed : originalRuntimeCode.lookup function=some (parameters,body,shape))
 (bodyHeap : ReturnedRel HeapRel body)
 (destination : kind=.local ∨ name≠ofString "heap_ptr")
 (code : s.code=originalRuntimeCode) (heap : StateInitHeapReady s)
 (run : evaluateHOLFiniteState s (.call (some (some (kind,name),none)) function arguments)=(none,post)) :
 StateInitHeapReady post := by
 unfold ReturnedRel at bodyHeap
 rw [evaluateHOLFiniteState_call] at run
 cases args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments with
 | none => rw [args] at run; cases run
 | some values =>
  rw [args] at run
  dsimp only at run
  cases lookup : lookupCodeHOLFinite s.code.lookup function values with
  | none => rw [lookup] at run; cases run
  | some data =>
   obtain ⟨found,callee,foundShape⟩ := data
   rw [lookup] at run
   dsimp only at run
   have same := lookupCodeHOLFinite_installed_body s.code.lookup function parameters body found shape
    foundShape values callee (by rw [code];exact installed) lookup
   subst same
   split at run
   · cases run
   · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) found with
     | mk result output =>
      rw [bodyRun] at run
      cases result with
      | none => cases run
      | some result =>
       cases result with
       | returned value =>
        dsimp only at run
        split at run
        · split at run
          · obtain ⟨_,rfl⟩ := Prod.mk.inj run
            have rel := bodyHeap (callEntryStateHOLFinite s callee) output value code bodyRun
            have ready := heapWord_of_rel rel heap
            obtain ⟨p,atHeap,aligned,capped⟩ := ready
            refine ⟨p,?_,aligned,capped⟩
            cases kind with
            | «local» => exact atHeap
            | «global» =>
             have ne : name≠ofString "heap_ptr" := destination.resolve_left (by intro bad;cases bad)
             simpa [setKvarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne] using atHeap
          · cases run
        · cases run
       | error => cases run
       | timeOut => cases run
       | «break» => cases run
       | «continue» => cases run
       | finalFfi ffi => cases run
       | exception id value => cases run
#print axioms state_init_assignment_call_heap
end InitECandidate.Runtime
