import InitECandidate.Runtime.SelectedInitializerFields
import InitECandidate.Runtime.SelectedWordMemoryInitialization
namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

theorem selected_fields_of_initialization {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maxHeap pointer start : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : List (Nat × HolProg width)) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (hyp : InitMake.dischargeThese jump bounds generateGc maxHeap pointer start oracle code s ∧
      InitMake.propagateThese s bitmaps dataSpace)
    (post : StackSemStateFiniteExact width C F)
    (selected : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer
      (sptFromAList code) s = some post) :
    post.ffi = s.ffi ∧ post.store.lookup .currHeap = s.regs.lookup 2 := by
  obtain ⟨⟨every,oracleBound,oracleEq,codeEq,k8,entry1,save,noStack,noStore,noAlloc,maxOk⟩,
    good,ptr2,ptr3,ptr4,bp,r2,r3,r4,m0,m1,m2,m3,m4,cbEmpty,le,al2,al4,albp,big,heap⟩ := hyp
  apply selected_initializer_fields generateGc maxHeap pointer bitmaps dataSpace s jump bounds
    (sptFromAList code) oracle ?_ post selected
  refine ⟨?_,InitCodeRelation.impCodeRel jump bounds generateGc maxHeap pointer start code s.code
    ⟨every,codeEq⟩,oracleEq,oracleBound,?_,maxOk⟩
  · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
      rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg,BitVec.add_comm]
    rw [sub] at heap
    exact ⟨ptr2,ptr3,ptr4,bp,good,k8,entry1,save,noStack,noStore,noAlloc,r2,r3,r4,
      m0,m1,m2,m3,m4,le,big,al2,al4,albp,cbEmpty,heap⟩
  · rw [codeEq,sptLookup_sptFromAList]
    simp [compileHOL,initStubs,sptAListLookup,stackErrLab]


open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit

theorem selected_fields_of_full_initialization {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (post : StackSemStateFiniteExact width C F)
    (selected : InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 oracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) = some post) :
    post.ffi = target.ffi ∧
      post.store.lookup .currHeap = some (target.regs (StackNames.findNameSpt stackConf.regNames 2)) := by
  have fields := selected_fields_of_initialization stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind)
    maxHeap sp BvlToBvi.initGlobalsLocation (coracle1 oracle) (code1 dataConf code)
    (s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle) bitmaps dataSp
    ⟨dischargeThese_s2 initialized,propagateThese_s2 initialized⟩ post selected
  obtain ⟨_,_,_,_,_,_,_,_,ffi⟩ := s2_fields (stackConf := stackConf)
    (dataConf := dataConf) (maxHeap := maxHeap) (sp := sp) (offset := offset)
    (code := code) (t := target) (saveRegs := saveRegs) (coracle := oracle)
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,bijective⟩ := initialized
  exact ⟨fields.1.trans ffi,fields.2.trans (s2_regs_lookup bijective (Or.inl rfl))⟩

#print axioms selected_fields_of_full_initialization
#print axioms selected_fields_of_initialization
end InitECandidate.Runtime.StackRemove
