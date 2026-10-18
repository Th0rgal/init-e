import InitECandidate.Runtime.HtrBytesVectorShortBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrBytesVectorBodyCost : Nat := htrBytesVectorShortCost + htrBytesVectorLongBodyCost

theorem runBounded_htrBytesVector_check {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n out : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (small : n.toNat ≤ 134217712) (code : state.code = originalRuntimeCode)
    (budget : htrBytesVectorShortCost ≤ state.clock) :
    RunBounded state htrBytesVectorCheck htrBytesVectorShortCost := by
  have checkRun : evaluateHOLFiniteState state htrBytesVectorCheck =
      if n.toNat ≤ 32 then evaluateHOLFiniteState state htrBytesVectorShort else (none,state) := by
    unfold htrBytesVectorCheck
    rw [evaluateHOLFiniteState_ite]
    by_cases short : n.toNat ≤ 32
    all_goals simp [evalHOLExact,hn,Compiler.Encoders.Asm.wordCmpHOL,BitVec.le_def,short,evaluateHOLFiniteState_skip]
  have bounded := runBounded_htrBytesVector_short state p n out hp hn ho small code budget
  unfold RunBounded at bounded ⊢
  rw [checkRun]
  split
  · exact bounded
  · simp

theorem runBounded_htrBytesVector_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n out heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrBytesVectorBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_bytes_vector) htrBytesVectorBodyCost := by
  rw [source_htrBytesVector_body]
  refine RunBounded.seq (runBounded_htrBytesVector_check state p n out hp hn ho small code
    (by unfold htrBytesVectorBodyCost at budget; omega)) budget ?_
  intro next normal nextCode remaining
  have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key htrBytesVectorCheck (by rfl) state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using frame
  have globals := htrBytesVector_check_globals state code
  rw [normal] at globals
  exact runBounded_htrBytesVectorLong_body next p n out heap ((keep _).trans hp) ((keep _).trans hn)
    ((keep _).trans ho) small (by rw [globals]; exact hh) heapBound (nextCode.trans code) remaining

#print axioms runBounded_htrBytesVector_check
#print axioms runBounded_htrBytesVector_body
end InitECandidate.Runtime
