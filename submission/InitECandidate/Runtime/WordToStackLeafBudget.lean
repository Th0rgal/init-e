import InitECandidate.Runtime.WordToStackControlBudget
import InitECandidate.Runtime.WordToStackPrimitiveBudget
import InitECandidate.Runtime.WordToStackMemoryBudget
import InitECandidate.Runtime.WordToStackStoreConstsBudget
import InitECandidate.Runtime.WordToStackOneBudget

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Constructors requiring a genuine recursive simulation are excluded. The
MustTerminate case is discharged by the original state relation's termdep=0. -/
def leafCase {width : Nat} (p : WordLangProgHOL (BitVec width)) : Bool :=
  match p with
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _ | .call _ _ _ _ => false
  | _ => true

/-- Exact per-constructor ceilings for WordToStack's nonrecursive simulations. -/
def leafBudget {width : Nat} (p : WordLangProgHOL (BitVec width)) : Nat :=
  match p with
  | .raise _ | .shareInst _ _ _ => 1
  | _ => 0

/-- All 22 nonrecursive constructor cases with original full premises and
postconditions, and zero or one extra clock as appropriate. -/
theorem leafCase_correct {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (leaf : leafCase p = true) :
    BoundedSimulation ac p source (leafBudget p) := by
  cases p with
  | skip  =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.compCorrectSkip ac k f frame source post target result bs bsPost n nPost compiled lens premises
  | «break» label =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.compCorrectBreak ac label k f frame source post target result bs bsPost n nPost compiled lens premises
  | «continue» label =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.compCorrectContinue ac label k f frame source post target result bs bsPost n nPost compiled lens premises
  | tick  =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.compCorrectTick ac k f frame source post target result bs bsPost n nPost compiled lens premises
  | mustTerminate body =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.compCorrectMustTerminate ac body k f frame source post target result bs bsPost n nPost compiled lens premises
  | assign name expression =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.compCorrectAssign ac name expression k f frame source post target result bs bsPost n nPost compiled lens premises
  | store address value =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.compCorrectStore ac address value k f frame source post target result bs bsPost n nPost compiled lens premises
  | alloc name names =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.Alloc.compCorrectAlloc ac name names k f frame source post target result bs bsPost n nPost compiled lens premises
  | ffi fi p1 l1 p2 l2 names =>
      intro k f frame post target result bs bsPost n nPost compiled lens premises
      exact Zero.FFI.compCorrectFFI ac fi p1 l1 p2 l2 names k f frame source post target result bs bsPost n nPost compiled lens premises
  | move priority moves => exact Zero.MoveFull.compCorrectMove ac priority moves source
  | inst i => exact Zero.Inst.compCorrectInst ac i source
  | get v name => exact Zero.Get.compCorrectGet ac v name source
  | set name exp => exact Zero.Set.compCorrectSet ac name exp source
  | opCurrHeap op dest src => exact Zero.OpCurrHeap.compCorrectOpCurrHeap ac op dest src source
  | locValue v loc => exact Zero.LocValue.compCorrectLocValue ac v loc source
  | codeBufferWrite a b => exact Zero.CodeBufferWrite.compCorrectCodeBufferWrite ac a b source
  | dataBufferWrite a b => exact Zero.DataBufferWrite.compCorrectDataBufferWrite ac a b source
  | install p l dp dl names => exact Zero.Install.compCorrectInstall ac p l dp dl names source
  | storeConsts t1 t2 a o words => exact Zero.StoreConsts.compCorrectStoreConsts ac t1 t2 a o words source
  | «return» loc values => exact Zero.Return.compCorrectReturn ac loc values source
  | raise v => exact One.Raise.compCorrectRaise ac v source
  | shareInst op v exp => exact One.ShareInst.compCorrectShareInst ac op v exp source
  | seq _ _ | ite _ _ _ _ _ | loop _ _ _ | call _ _ _ _ => simp [leafCase] at leaf

#print axioms leafCase_correct
end InitECandidate.Runtime.WordToStack
