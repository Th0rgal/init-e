import InitECandidate.Runtime.StackRemoveEntryBudget
import InitECandidate.Runtime.StackRemovePathWorkCorrect
import InitECandidate.Runtime.StackRemoveAffineWork
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics

namespace InitECandidate.Runtime.StackRemove
open Flapjack Compiler.Backend.StackLang StackSemEvaluate
open Flapjack.Compiler.Backend.StackRemove
theorem entrySimulation_affine_bounded {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (result, postSource))
    (nonError : result ≠ some .error) :
    ∃ extra, extra ≤ removeAffineWork (.call none (.inl start) none) {source with clock := clock} ∧ ∃ postTarget,
      evaluate (.call none (.inl start) none, {target with clock := extra + clock}) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi := by
  obtain ⟨extra, bound, postTarget, targetRun, postRelation⟩ :=
    removePathWork_correct (.call none (.inl start) none)
      {source with clock := clock} result postSource {target with clock := clock}
      pointer bounds jump ⟨run, nonError,
        RelationLaws.stateRelWithClock jump bounds pointer clock source target relation,
        by simp [Flapjack.Compiler.Backend.StackProps.regBound]⟩
  refine ⟨extra, le_removeAffineWork _ _ result postSource run nonError extra bound, postTarget, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => exact (RelationLaws.stateRelConst jump bounds pointer postSource postTarget postRelation).2.2.2.2.1
    | some value =>
      cases value
      all_goals first
        | exact postRelation
        | exact (RelationLaws.stateRelConst jump bounds pointer postSource postTarget postRelation).2.2.2.2.1


theorem makeInitOpt_entry_affine_bounded {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (pointer start : Nat) (s : StackSemStateFiniteExact width C F)
    (jump : Bool) (bounds : BitVec width × BitVec width)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : Spt (HolProg width))
    (hyp : Proofs.InitMake.initPre generateGc maxHeap bitmaps dataSpace pointer start s ∧
      s.compileOracle = (fun index =>
        let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        Flapjack.Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      codeRelHOL jump bounds pointer code s.code)
    (source postSource : StackSemStateFiniteExact width C F) (fuel : Nat)
    (result : Option (StackSemResult width))
    (selected : Proofs.InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s = some source)
    (run : evaluate (.call none (.inl start) none, {source with clock := fuel}) = (result, postSource))
    (nonError : result ≠ some .error) :
    ∃ clocks postTarget,
      clocks ≤ fuel + removeAffineWork (.call none (.inl start) none) {source with clock := fuel} + 1 ∧
      evaluate (.call none (.inl 0) none, {s with clock := clocks}) = (result, postTarget) ∧
      postTarget.ffi = postSource.ffi := by
  have init := Proofs.InitSemantics.evaluateInitCode generateGc maxHeap bitmaps dataSpace pointer start s
    jump bounds oracle code hyp
  rcases initRun : evaluate (initCode generateGc maxHeap pointer, s) with ⟨initResult, ready⟩
  rw [initRun] at init
  cases initResult with
  | some r => exact False.elim init
  | none =>
    obtain ⟨built, opt, relation, _⟩ := init
    rw [selected] at opt
    cases Option.some.inj opt
    obtain ⟨extra, bound, postTarget, targetRun, ffi⟩ :=
      entrySimulation_affine_bounded jump bounds pointer start fuel source ready postSource result relation run nonError
    refine ⟨extra + fuel + 1, postTarget, by omega, ?_, ffi⟩
    exact initializer_prefix_run generateGc maxHeap pointer start (extra + fuel) s ready postTarget result
      hyp.1.1 initRun targetRun

open Flapjack.Compiler.Backend.StackRemove.Proofs
theorem discharge_entry_affine_bounded {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maxHeap pointer start : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : List (Nat × HolProg width)) (s2 : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (hyp : InitMake.dischargeThese jump bounds generateGc maxHeap pointer start oracle code s2 ∧
      InitMake.propagateThese s2 bitmaps dataSpace)
    (source postSource : StackSemStateFiniteExact width C F) (fuel : Nat)
    (result : Option (StackSemResult width))
    (selected : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer
      (sptFromAList code) s2 = some source)
    (run : StackSemEvaluate.evaluate (.call none (.inl start) none, {source with clock := fuel}) = (result, postSource))
    (nonError : result ≠ some .error) :
    ∃ clocks postTarget,
      clocks ≤ fuel + removeAffineWork (.call none (.inl start) none) {source with clock := fuel} + 1 ∧
      StackSemEvaluate.evaluate (.call none (.inl 0) none, {s2 with clock := clocks}) = (result, postTarget) ∧
      postTarget.ffi = postSource.ffi := by
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := hyp
  apply makeInitOpt_entry_affine_bounded generateGc maxHeap bitmaps dataSpace pointer start s2 jump bounds
    oracle (sptFromAList code) ?_ source postSource fuel result selected run nonError
  refine ⟨⟨?_, ?_, maxOk⟩, oracleEq, oracleBound, ?_, InitCodeRelation.impCodeRel jump bounds
    generateGc maxHeap pointer start code s2.code ⟨every, codeEq⟩⟩
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup]
  · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
      rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
    rw [sub] at heap
    exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
      m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup, stackErrLab]

#print axioms discharge_entry_affine_bounded
#print axioms makeInitOpt_entry_affine_bounded


#print axioms entrySimulation_affine_bounded
end InitECandidate.Runtime.StackRemove
