import InitECandidate.Proofs.Op5.InitCorrectArena

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackLang StackSemEvaluate
open Classical

/-- Optional initialization with the same executable initializer and an
arena-aware output predicate. No runtime code is changed. -/
noncomputable def makeInitOptWithArena {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F)
    (arena : BitVec width → Prop) :
    Option (StackSemStateFiniteExact width C F) :=
  match evaluate (initCode generateGc maxHeap pointer, s) with
  | (some _, _) => none
  | (none, t) =>
    if initPropWithArena generateGc maxHeap dataSpace
        (InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s))
        (initReduceWithArena arena generateGc jump bounds pointer code bitmaps dataSpace oracle t) arena
    then some (initReduceWithArena arena generateGc jump bounds pointer code bitmaps dataSpace
      oracle t)
    else none


/-- Total arena initializer, with scratch ownership also retained in the failure fallback. -/
noncomputable def makeInitAnyWithArena {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F)
    (arena : BitVec width → Prop) :
    StackSemStateFiniteExact width C F :=
  match makeInitOptWithArena generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s arena with
  | some t => t
  | none =>
    { s with
      regs := HolFiniteMapExact.empty.updateEq (0, .loc 1 0)
      fpRegs := HolFiniteMapExact.empty
      mdomain := fun a => decide (arena a)
      bitmaps := [4]
      useStack := true
      useStore := true
      useAlloc := false
      stack := [.word 0]
      stackSpace := 0
      compile := fun config program => s.compile config (program.map (progComp jump bounds pointer))
      compileOracle := oracle
      dataBuffer := { buffer := [], position := 0, spaceLeft := 0 }
      codeBuffer := { buffer := [], position := 0, spaceLeft := 0 }
      code := code
      store := HolFiniteMapExact.empty.updateListEq
        ((.currHeap :: storeList).map fun name =>
          (StackSemRegisterTransfers.storeOfSyntax name, .word 0)) }


/-- The actual optional initializer succeeds under the arena-framed machine
precondition and pinned compiler guards, establishing the full simulation. -/
theorem makeInitOptWithArena_correct {width : Nat} [NeZero width] {C F : Type}
    (gc : Bool) (maxHeap pointer : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (s : StackSemStateFiniteExact width C F) (arena : BitVec width → Prop)
    (jump : Bool) (bounds : BitVec width × BitVec width) (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (pre : initCodePreWithArena pointer bitmaps dataSpace s arena)
    (codeRel : codeRelHOL jump bounds pointer code s.code)
    (oracleEq : s.compileOracle = fun i =>
      let e := oracle i
      (e.1,e.2.1.map (progComp jump bounds pointer),e.2.2))
    (oracleBound : ∀ n i p, (i,p) ∈ (oracle n).2.1 →
      Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i+1)
    (err : sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)))
    (maxOk : maxStackAlloc ≤ maxHeap) :
    ∃ r t, makeInitOptWithArena gc maxHeap bitmaps dataSpace oracle jump bounds pointer code s arena = some r ∧
      evaluate (initCode gc maxHeap pointer,s) = (none,t) ∧
      stateRelHOL jump bounds pointer r t ∧ t.ffi = s.ffi ∧
      initPropWithArena gc maxHeap dataSpace
        (InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s)) r arena := by
  have main := initCodeThmWithArena gc maxHeap pointer bitmaps dataSpace s arena jump bounds code oracle
    ⟨pre,codeRel,oracleEq,oracleBound,err,maxOk⟩
  cases run : evaluate (initCode gc maxHeap pointer,s) with
  | mk result t =>
    rw [run] at main
    cases result with
    | some result => exact main.elim
    | none =>
      obtain ⟨_,rel,ffi,prop,_⟩ := main
      refine ⟨_,t,?_,rfl,rel,ffi,prop⟩
      unfold makeInitOptWithArena
      rw [run]
      exact if_pos prop

#print axioms makeInitOptWithArena_correct
end InitE.Op5
