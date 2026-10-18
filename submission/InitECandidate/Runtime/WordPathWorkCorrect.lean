import InitECandidate.Runtime.WordPathWorkLeaves
import InitECandidate.Runtime.WordPathWorkCompose
import InitECandidate.Runtime.WordPathWorkLoop
import InitECandidate.Runtime.WordPathWorkCalls
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Whole quantitative WordToStack simulation, with no recursive simulation
premises. The evaluator's original induction principle discharges all 26
constructors at their actual guarded successor states. Full original compiler
premises and result/resource postconditions remain in BoundedSimulation. -/
theorem wordPathWork_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) :
    ∀ (p : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width (Nat × C) F),
    BoundedSimulation ac p source (wordPathWork p source) := by
  apply WordSemStateFiniteExact.evaluate_ind
    (fun p source => BoundedSimulation ac p source (wordPathWork p source))
  refine ⟨?skip, ?alloc, ?storeConsts, ?move, ?inst, ?assign, ?get, ?set, ?opCurrHeap, ?store,
    ?tick, ?mustTerminate, ?seq, ?ret, ?raise, ?brk, ?cont, ?ite, ?loop, ?locValue, ?install,
    ?codeBufferWrite, ?dataBufferWrite, ?ffi, ?shareInst, ?call⟩
  case skip => exact fun  source => wordPathWork_leaf_correct ac (.skip) source rfl
  case alloc => exact fun n names source => wordPathWork_leaf_correct ac (.alloc n names) source rfl
  case storeConsts => exact fun t1 t2 a o words source => wordPathWork_leaf_correct ac (.storeConsts t1 t2 a o words) source rfl
  case move => exact fun priority moves source => wordPathWork_leaf_correct ac (.move priority moves) source rfl
  case inst => exact fun i source => wordPathWork_leaf_correct ac (.inst i) source rfl
  case assign => exact fun v e source => wordPathWork_leaf_correct ac (.assign v e) source rfl
  case get => exact fun v name source => wordPathWork_leaf_correct ac (.get v name) source rfl
  case set => exact fun name e source => wordPathWork_leaf_correct ac (.set name e) source rfl
  case opCurrHeap => exact fun op dst src source => wordPathWork_leaf_correct ac (.opCurrHeap op dst src) source rfl
  case store => exact fun e v source => wordPathWork_leaf_correct ac (.store e v) source rfl
  case tick => exact fun  source => wordPathWork_leaf_correct ac (.tick) source rfl
  case ret => exact fun loc values source => wordPathWork_leaf_correct ac (.return loc values) source rfl
  case raise => exact fun n source => wordPathWork_leaf_correct ac (.raise n) source rfl
  case brk => exact fun label source => wordPathWork_leaf_correct ac (.break label) source rfl
  case cont => exact fun label source => wordPathWork_leaf_correct ac (.continue label) source rfl
  case locValue => exact fun r loc source => wordPathWork_leaf_correct ac (.locValue r loc) source rfl
  case install => exact fun ptr len dptr dlen names source => wordPathWork_leaf_correct ac (.install ptr len dptr dlen names) source rfl
  case codeBufferWrite => exact fun a b source => wordPathWork_leaf_correct ac (.codeBufferWrite a b) source rfl
  case dataBufferWrite => exact fun a b source => wordPathWork_leaf_correct ac (.dataBufferWrite a b) source rfl
  case ffi => exact fun fi p1 l1 p2 l2 names source => wordPathWork_leaf_correct ac (.ffi fi p1 l1 p2 l2 names) source rfl
  case shareInst => exact fun op v exp source => wordPathWork_leaf_correct ac (.shareInst op v exp) source rfl
  case mustTerminate => exact fun body source _ => wordPathWork_leaf_correct ac (.mustTerminate body) source rfl
  case seq => exact fun first second source ih => wordPathWork_seq_correct ac first second source ih.2 ih.1
  case ite => exact fun cmp reg operand first second source ih =>
    wordPathWork_if_correct ac cmp reg operand first second source ih
  case loop => exact fun names body exitNames source ih => wordPathWork_loop_correct ac names exitNames body source ih
  case call => exact fun ret dest args handler source ih => wordPathWork_call_correct ac ret dest args handler source ih

#print axioms wordPathWork_correct
end InitECandidate.Runtime.WordToStack
