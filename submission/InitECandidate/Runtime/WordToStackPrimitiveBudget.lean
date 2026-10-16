import InitECandidate.Runtime.WordToStackBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Get
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Set
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.OpCurrHeap
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.MoveFull
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CodeBufferWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.DataBufferWrite
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.LocValue
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Inst

namespace InitECandidate.Runtime.WordToStack.Zero
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-! Zero-extra-clock primitive simulations with full original premises,
bitmap/frame obligations and result-dependent resource conclusions. -/
namespace Get
open Flapjack.WordToStackProofs.CompCorrect.Get
theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register : Nat) (name : WordStoreHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.get register name) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  cases read : WordSemStateFiniteExact.getStore name source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have storeRel : source.store = target.store.eraseEq .handler :=
      related.2.2.2.2.2.2.2.2.2.2.2.1
    have targetRead : target.store.lookup (StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name)) = some value := by
      unfold WordSemStateFiniteExact.getStore at read
      rw [storeRel] at read
      cases name <;>
        simp only [storeNameOfWord,StackSemRegisterTransfers.storeOfSyntax,
          HolFiniteMapExact.eraseEq,FDOMSUB_HOL] at read ⊢ <;>
        simp only [reduceCtorEq,ite_false,ite_true] at read <;>
        exact read
    have useStore : target.useStore = true := related.2.2.2.2.2.1
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.get r (storeNameOfWord name),target) =
        (none,StackSemStateOps.setVar r value target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_get,useStore,targetRead]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens value (fun r => .get r (storeNameOfWord name))
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
    · simpa only [Nat.add_zero,← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel

#print axioms compCorrectGet
end Get

namespace Set
open Flapjack.WordToStackProofs.CompCorrect.Set
theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : WordStoreHOL)
    (expression : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.set name expression) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  cases expression <;> simp [flatExpConventions] at flat
  rename_i register
  simp only [WordSemStateFiniteExact.evaluate] at execution
  have notHandler : name ≠ .handler := by
    intro eq; subst name; simp only [true_or,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  have notBitmap : name ≠ .bitmapBase := by
    intro eq; subst name; simp only [or_true,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  simp only [notHandler,notBitmap,false_or,if_false,WordSemStateFiniteExact.wordExp] at execution
  cases read : WordSemStateFiniteExact.getVar register source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,everyVarExpHOL,isPhyVar] using conventions
    rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k,f,frame) with ⟨loads,reg⟩
    obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
      LoadRegister.evaluateWStackLoadWReg1 ac k f frame register reg loads
        source target lens value format even read related
    have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
    have codec : StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name) = name := by
      cases name <;> rfl
    have programEq := congrArg Prod.fst compilation
    have compiledEq : compiled = wStackLoadNative loads (.set (storeNameOfWord name) reg) := by
      cases name <;> simp only [compNative,format] at programEq <;>
        first | exact programEq.symm | contradiction
    subst compiled
    refine ⟨0, Nat.le_refl 0,StackSemStateOps.setStore name value loaded,none,?_,?_⟩
    · simp only [Nat.add_zero,LoadRegister.evaluateWStackLoadSeq,
        StackSemEvaluate.evaluate_seq,loadRun]
      have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
        have le : loaded.clock ≤ target.clock := by omega
        simp only [StackSemControl.fixClock,Nat.min_eq_right le]
      rw [fix]
      simp only [StackSemEvaluate.evaluate_set,useStore,not_true_eq_false,if_false,
        loadedRead,codec]
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte] using StateRelStoreUpdate.stateRelSetStore ac k f frame source
          loaded lens 0 name value notHandler loadRel

#print axioms compCorrectSet
end Set

namespace OpCurrHeap
open Flapjack.WordToStackProofs.CompCorrect.OpCurrHeap
private theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (operator : HolBinop) (dst src : Nat) (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.opCurrHeap operator dst src) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ operand heap value : BitVec width,
      WordSemStateFiniteExact.getVar src source = some (.word operand) ∧
      source.store.lookup .currHeap = some (.word heap) ∧
      wordOpHOL operator [operand,heap] = some value ∧
      result = none ∧ post = WordSemStateFiniteExact.setVar dst (.word value) source := by
  cases read : WordSemStateFiniteExact.getVar src source with
  | none =>
    simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
      read,theWords] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  | some operandValue =>
    cases operandValue with
    | loc l n =>
      simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
        read,theWords] at execution
      obtain ⟨rfl,rfl⟩ := execution
      contradiction
    | word operand =>
      cases heapRead : source.store.lookup .currHeap with
      | none =>
        simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
        obtain ⟨rfl,rfl⟩ := execution
        contradiction
      | some heapValue =>
        cases heapValue with
        | loc l n =>
          simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
          obtain ⟨rfl,rfl⟩ := execution
          contradiction
        | word heap =>
          cases operation : wordOpHOL operator [operand,heap] with
          | none =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            contradiction
          | some value =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            exact ⟨operand,heap,value,rfl,rfl,operation,rfl,rfl⟩
/-- Full original OpCurrHeap constructor under the unchanged simulation motive.
Source success supplies both words; the native arithmetic callback is proved
from the full loaded-state relation. Evaluator closure inherits
reals_as_rational_cuts; no independent real-analysis agreement is claimed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (operator : HolBinop) (dst src : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.opCurrHeap operator dst src) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨operand,heap,value,read,heapRead,operation,rfl,rfl⟩ :=
    sourceSuccess source sourcePost operator dst src result execution notError
  have evens : dst % 2 = 0 ∧ src % 2 = 0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  have dstEq : dst = 2*(dst/2) := by omega
  have bound : dst/2 < frame+k := by
    simp only [maxVarHOL] at maxBound
    omega
  rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 src (k,f,frame) with ⟨loads,reg⟩
  obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame src reg loads
      source target lens (.word operand) format evens.2 read related
  have storeEq : source.store = loaded.store.eraseEq .handler :=
    loadRel.2.2.2.2.2.2.2.2.2.2.2.1
  have targetHeap : loaded.store.lookup .currHeap = some (.word heap) := by
    rw [storeEq] at heapRead
    simpa [HolFiniteMapExact.eraseEq,FDOMSUB_HOL] using heapRead
  have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
  have callback : ∀ d, d ≤ k →
      StackSemEvaluate.evaluate (.opCurrHeap operator d reg,loaded) =
        (none,StackSemStateOps.setVar d (.word value) loaded) := by
    intro d _
    change loaded.regs.lookup reg = some (.word operand) at loadedRead
    simp [StackSemEvaluate.evaluate_opCurrHeap,useStore,StackSemExpressions.wordExp,
      loadedRead,targetHeap,operation]
  obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
    (dst/2) source loaded lens (.word value) (fun d => .opCurrHeap operator d reg)
    loadRel bound callback
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,format] at programEq
  subst compiled
  refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
  · simp only [Nat.add_zero,LoadRegister.evaluateWStackLoadSeq,
      StackSemEvaluate.evaluate_seq,loadRun]
    have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
      have le : loaded.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix]
    simpa only [← dstEq] using actual
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte,← dstEq] using postRel

#print axioms compCorrectOpCurrHeap
end OpCurrHeap

namespace MoveFull
open Flapjack.WordToStackProofs.CompCorrect.MoveFull
theorem compCorrectMove {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.move priority moves) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨values,distinct,reads,rfl,rfl⟩ :=
    Move.sourceSuccess priority moves source sourcePost result execution notError
  have evens : (∀ n ∈ moves.map Prod.fst, n % 2=0) ∧
      (∀ n ∈ moves.map Prod.snd, n % 2=0) := by
    have raw : (∀ a b, (a,b) ∈ moves → a % 2=0) ∧
        (∀ a b, (a,b) ∈ moves → b % 2=0) := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar,List.all_eq_true] using conventions
    constructor
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.1 a b input
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.2 a b input
  have wf : sptWf source.locals=true := by
    unfold stateRel at related
    tauto
  obtain ⟨post,run,relation,_,_⟩ := Move.actualScheduledRun ac k f frame lens moves source target
    related distinct evens.1 evens.2 (by simp [reads]) (by simpa [maxVarHOL] using maxBound)
  rw [Move.scheduledSourceStateReconstruction moves source target k values distinct
    evens.1 evens.2 reads wf] at relation
  have program := congrArg Prod.fst compilation
  simp only [compNative] at program
  subst compiled
  refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
  · simpa only [Nat.add_zero] using run
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,↓reduceIte] using relation

#print axioms compCorrectMove
end MoveFull

namespace CodeBufferWrite
open Flapjack.WordToStackProofs.CompCorrect.CodeBufferWrite
theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.codeBufferWrite r1 r2) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.codeBuffer = source.codeBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨0, Nat.le_refl 0,{t2 with codeBuffer := cb},none,?_,?_⟩
  · simp only [Nat.add_zero,wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    simp only [StackSemEvaluate.evaluate_codeBufferWrite,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using codeBufferRelation cb rel2


#print axioms compCorrectCodeBufferWrite
end CodeBufferWrite

namespace DataBufferWrite
open Flapjack.WordToStackProofs.CompCorrect.DataBufferWrite
theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.dataBufferWrite r1 r2) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.dataBuffer = source.dataBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have capacity : cb.buffer.length+cb.spaceLeft = source.dataBuffer.buffer.length+source.dataBuffer.spaceLeft := by
    unfold wordSemBufferWrite at writeEq
    split at writeEq
    · rename_i guard
      have equal := Option.some.inj writeEq
      subst cb
      simp only [List.length_append,List.length_singleton]
      omega
    · cases writeEq
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨0, Nat.le_refl 0,{t2 with dataBuffer := cb},none,?_,?_⟩
  · simp only [Nat.add_zero,wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    have useStack : t2.useStack = true := rel2.2.2.2.2.1
    simp only [StackSemEvaluate.evaluate_dataBufferWrite,useStack,not_true_eq_false,if_false,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using dataBufferRelation cb capacity rel2


#print axioms compCorrectDataBufferWrite
end DataBufferWrite

namespace LocValue
open Flapjack.WordToStackProofs.CompCorrect.LocValue
theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register location : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.locValue register location) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  by_cases present : sptMem location source.code
  swap
  · simp [present] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  · simp only [present,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have codeDomain : sptDomain target.code =
        (fun n => n=raiseStubLocation ∨ n=storeConstsStubLocation ∨ sptDomain source.code n) :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have valid : StackSem.locCheckExact target.code (location,0) := by
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change sptDomain target.code location
      rw [codeDomain]
      exact Or.inr (Or.inr present)
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.locValue r location 0,target) =
        (none,StackSemStateOps.setVar r (.loc location 0) target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_locValue,valid]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens (.loc location 0) (fun r => .locValue r location 0)
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
    · simpa only [Nat.add_zero,← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel

#print axioms compCorrectLocValue
end LocValue

namespace Inst
open Flapjack.WordToStackProofs.CompCorrect.Inst
private theorem instArgConvention_ofWordLangInst {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) :
    instArgConvention i = instArgConventionExact (HolInst.ofWordLangInst i) := by
  rcases i with _ | ⟨_, _⟩ | ⟨a⟩ | ⟨_, _, _⟩
  all_goals try rfl
  rcases a with ⟨_, _, _, ri⟩ | ⟨_, _, _, ri⟩ | _ | _ | _ | _ | _ | _
  all_goals try rfl
  all_goals (cases ri <;> rfl)

/-- Full original comp_correct Inst case (6315-6326) of comp_correct5756 /
motive5719-5751: the entire BoundedSimulation motive with all original
hypotheses and the full existential target-run/resource/result conclusion.
As in HOL, the source run succeeds with NONE, post_alloc_conventions supplies
every_var_inst is_phy_var and inst_arg_convention, max_var gives the
max_var_inst bound, and the full original evaluate_wInst supplies the target
run with ck = 0. The source WordLangInst is compiled through the reviewed
HolInst codec. Canonical maps and word widths are qualified; the evaluators
inherit reals_as_rational_cuts (SOUNDNESS item 8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (i : WordLangInst (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BoundedSimulation ac (.inst i) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, _flat,
    compilation, _lengthBound, _bitmapBound, _bitmapPrefix, _labels, maxBound⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases instRun : WordSemStateFiniteExact.inst i source with _ | post
  · rw [instRun] at execution
    obtain ⟨rfl, -⟩ := Prod.mk.inj execution
    exact absurd rfl notError
  · rw [instRun] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    have conventionParts := conventions
    simp only [postAllocConventionsHOL, everyVarHOL, callArgConventionHOL,
      Bool.and_eq_true] at conventionParts
    obtain ⟨physical, _, convention⟩ := conventionParts
    simp only [compNative, Prod.mk.injEq] at compilation
    obtain ⟨rfl, -⟩ := compilation
    obtain ⟨post', run, postRel, _, _⟩ :=
      InstSimulation.evaluateWInst ac (HolInst.ofWordLangInst i) k f frame source post
        target lens (by simpa only [HolInst.to_of] using instRun)
        (by simpa only [HolInst.to_of] using physical)
        (by simpa only [HolInst.to_of, maxVarHOL] using maxBound)
        (by rw [← instArgConvention_ofWordLangInst]; exact convention) related
    refine ⟨0, Nat.le_refl 0, post', none, by simpa using run, ?_⟩
    simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, if_false]
    exact postRel


#print axioms compCorrectInst
end Inst

end InitECandidate.Runtime.WordToStack.Zero
