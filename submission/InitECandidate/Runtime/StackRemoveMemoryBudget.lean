import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemory
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemoryAny
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackSize
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Bitmap
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.DataBufferWrite
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.FFI
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StoreTransfers
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Install
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.ShMemOp
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackFreeSimulation

namespace InitECandidate.Runtime.StackRemove.MemoryZero
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRemove.CompCorrect
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemoryAny
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSize
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Bitmap
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.DataBufferWrite
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.FFI
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Install
theorem compCorrectStackLoad {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.stackLoad register count : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases bound : source.stackSpace + count < source.stack.length
  · rw [dif_pos bound] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
    change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
    have addressEq : base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count =
        base + wordOffset (source.stackSpace + count) := by
      simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
    have read : StackSemStateOps.memLoad
        (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count) target =
        some source.stack[source.stackSpace + count] := by
      rw [addressEq]
      exact reads (source.stackSpace + count) bound
    refine ⟨0, rfl, StackSemStateOps.setVar register source.stack[source.stackSpace + count] target, ?_, ?_⟩
    · simp only [Nat.zero_add]
      rw [comp]
      split
      · exact runLoad target register pointer _ _ _ pointerLookup read
      · have moveRun : StackSemEvaluate.evaluate (moveInst register pointer, target) =
            (none, StackSemStateOps.setVar register
              (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target) := by
          simp [moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemIntegerInstructions.instInteger, pointerLookup]
        rw [StackSemEvaluate.evaluate_seq, moveRun]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let initial := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target
        have initialLookup : initial.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := by
          simp [initial, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (stackLoad register count, initial) = _
        rw [stackLoad, StackSemEvaluate.evaluate_seq,
          ShiftSimulation.evaluateUpshift count register initial _ initialLookup]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let shifted := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) initial
        have shiftedLookup : shifted.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) := by
          simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (.inst (.mem .load register (.addr register 0)), shifted) = _
        have shiftedRead : StackSemStateOps.memLoad
            (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count + 0) shifted =
            some source.stack[source.stackSpace + count] := by
          simpa [shifted, initial, StackSemStateOps.memLoad, StackSemStateOps.setVar] using read
        rw [runLoad shifted register register _ 0 _ shiftedLookup shiftedRead]
        simp only [shifted, initial, StackFreeSimulation.setVarTwice]
        rfl
    · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
        source.stack[source.stackSpace + count] source target ⟨relation, lower⟩
  · rw [dif_neg bound] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
/-- Flapjack primitive-store execution factoring. The full constructor derives
the original register value, pointer lookup and memory-domain facts rather
than taking them as compiler-correctness premises. No standalone HOL declaration. -/
theorem runStore {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register baseReg : Nat)
    (base offset : BitVec width) (value : WordLocW width)
    (baseLookup : state.regs.lookup baseReg = some (.word base))
    (valueLookup : state.regs.lookup register = some value)
    (domain : state.mdomain (base + offset) = true) :
    StackSemEvaluate.evaluate (.inst (.mem .store register (.addr baseReg offset)), state) =
      (none, {state with memory := fun key => if key = base + offset then value else state.memory key}) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, baseLookup, valueLookup, wordOpHOL, wordOp,
    StackSemStateOps.memStore, domain]
/-- Genuine full original StackStore constructor, including direct store and
upshift/store/downshift fallback. The actual target memory update and exact
pointer restoration establish the full post-state relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStore {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.stackStore register count : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackStore] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases outsideBounds : source.stack.length ≤ source.stackSpace + count
  · rw [if_pos outsideBounds] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · rw [if_neg outsideBounds] at sourceRun
    cases sourceLookup : StackSemStateOps.getVar register source with
    | none =>
      rw [sourceLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some value =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have safe : source.stackSpace + count < source.stack.length := Nat.lt_of_not_ge outsideBounds
      have different : register ≠ pointer := by omega
      have valueLookup : target.regs.lookup register = some value := by
        change StackSemStateOps.getVar register target = some value
        rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower⟩]
        exact sourceLookup
      obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
      let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
      change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
      have addressEq : pointerWord + wordOffset count = base + wordOffset (source.stackSpace + count) := by
        dsimp [pointerWord]
        simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
      have read : StackSemStateOps.memLoad (pointerWord + wordOffset count) target =
          some source.stack[source.stackSpace + count] := by
        rw [addressEq]
        exact reads _ safe
      have domain : target.mdomain (pointerWord + wordOffset count) = true := by
        by_contra outside
        simp [StackSemStateOps.memLoad, outside] at read
      let updated := {target with memory := fun key => if key = pointerWord + wordOffset count then value else target.memory key}
      refine ⟨0, rfl, updated, ?_, ?_⟩
      · simp only [Nat.zero_add]
        rw [comp]
        split
        · exact runStore target register pointer _ _ value pointerLookup valueLookup domain
        · rw [stackStore, StackSemEvaluate.evaluate_seq,
            ShiftSimulation.evaluateUpshift count pointer target pointerWord pointerLookup]
          simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
          let shifted := StackSemStateOps.setVar pointer (.word (pointerWord + wordOffset count)) target
          have shiftedPointer : shifted.regs.lookup pointer = some (.word (pointerWord + wordOffset count)) := by
            simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          have shiftedValue : shifted.regs.lookup register = some value := by
            simpa [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using valueLookup
          have shiftedDomain : shifted.mdomain (pointerWord + wordOffset count + 0) = true := by
            simpa [shifted, StackSemStateOps.setVar] using domain
          change StackSemEvaluate.evaluate (.seq (.inst (.mem .store register (.addr pointer 0)))
            (downshift pointer count), shifted) = _
          rw [StackSemEvaluate.evaluate_seq,
            runStore shifted register pointer _ 0 value shiftedPointer shiftedValue shiftedDomain]
          simp only [StackSemControl.fixClock, Nat.min_self]
          let written := {shifted with memory := fun key => if key = pointerWord + wordOffset count + 0 then value else shifted.memory key}
          have writtenPointer : written.regs.lookup pointer = some (.word (pointerWord + wordOffset count)) := shiftedPointer
          change StackSemEvaluate.evaluate (downshift pointer count, written) = _
          rw [ShiftSimulation.evaluateDownshift count pointer written _ writtenPointer]
          simp only [BitVec.add_sub_cancel]
          have restore : StackSemStateOps.setVar pointer (.word pointerWord) shifted = target := by
            dsimp [shifted]
            rw [StackFreeSimulation.setVarTwice, StackFreeSimulation.setVarExisting target pointer (.word pointerWord) pointerLookup]
          let newMemory : BitVec width → WordLocW width :=
            fun key => if key = (pointerWord + wordOffset count + 0) then value else target.memory key
          change (none, {(StackSemStateOps.setVar pointer (.word pointerWord) shifted) with memory := newMemory}) = _
          rw [restore]
          simp [updated, newMemory]
      · simpa only [updated, relation.1, Nat.add_comm] using
          StackHeapWrites.stateRelStackStore jump bounds pointer count source target source.stack pointerWord
            (pointerWord + wordOffset count) value
            ⟨relation, rfl, pointerLookup, safe, by rw [WordAddressArithmetic.wordOffsetEq]⟩
theorem compCorrectStackLoadAny {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackLoadAny register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.stackLoadAny register index : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoadAny register index),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_stackLoadAny] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  cases indexLookup : StackSemStateOps.getVar index source with
  | none =>
    rw [indexLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    cases value with
    | loc block offset =>
      rw [indexLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word word =>
      rw [indexLookup] at sourceRun
      dsimp only at sourceRun
      by_cases valid : source.stackSpace + (word >>> wordShiftAmount width).toNat < source.stack.length ∧
          (word >>> wordShiftAmount width) <<< wordShiftAmount width = word
      · rw [dif_pos valid] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
        subst result
        subst postSource
        have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have offsetEq := alignedOffset word good valid.2
        have targetIndex : target.regs.lookup index = some (.word word) := by
          change StackSemStateOps.getVar index target = some (.word word)
          rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
          exact indexLookup
        obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
        let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
        change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
        have addressEq : word + pointerWord = base + wordOffset (source.stackSpace + (word >>> wordShiftAmount width).toNat) := by
          calc
            word + pointerWord = wordOffset (word >>> wordShiftAmount width).toNat + pointerWord := by
              rw [offsetEq]
            _ = _ := by
              dsimp [pointerWord]
              simp only [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add]
              rw [BitVec.add_comm (bytesInWord width * BitVec.ofNat width (word >>> wordShiftAmount width).toNat),
                BitVec.add_assoc]
        let entry := source.stack[source.stackSpace + (word >>> wordShiftAmount width).toNat]
        have read : StackSemStateOps.memLoad (word + pointerWord) target = some entry := by
          rw [addressEq]
          exact reads _ valid.1
        refine ⟨0, rfl, StackSemStateOps.setVar register entry target, ?_, ?_⟩
        · simp only [Nat.zero_add]
          rw [comp, StackSemEvaluate.evaluate_seq,
            runMoveAdd target register index pointer word pointerWord targetIndex pointerLookup (by omega)]
          simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
          let addressed := StackSemStateOps.setVar register (.word (word + pointerWord)) target
          have addressedLookup : addressed.regs.lookup register = some (.word (word + pointerWord)) := by
            simp [addressed, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          have addressedRead : StackSemStateOps.memLoad (word + pointerWord + 0) addressed = some entry := by
            simpa [addressed, StackSemStateOps.memLoad, StackSemStateOps.setVar] using read
          change StackSemEvaluate.evaluate (.inst (.mem .load register (.addr register 0)), addressed) = _
          rw [StackMemory.runLoad addressed register register _ 0 entry addressedLookup addressedRead]
          simp only [addressed, StackFreeSimulation.setVarTwice]
          rfl
        · simpa only [entry, relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
            entry source target ⟨relation, lower.1⟩
      · rw [dif_neg valid] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
/-- Flapjack native execution factoring for the original Any constructors;
all lookup facts are derived inside the full cases below. No standalone HOL
declaration is claimed. -/
theorem runAdd {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination left right : Nat)
    (first second : BitVec width)
    (leftLookup : state.regs.lookup left = some (.word first))
    (rightLookup : state.regs.lookup right = some (.word second)) :
    StackSemEvaluate.evaluate (.inst (.arith (.binop .add destination left (.reg right))), state) =
      (none, StackSemStateOps.setVar destination (.word (first + second)) state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp,
    leftLookup, rightLookup, wordOpHOL, wordOp]
/-- Flapjack native execution factoring for the original Any constructors;
all lookup facts are derived inside the full cases below. No standalone HOL
declaration is claimed. -/
theorem runSub {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination left right : Nat)
    (first second : BitVec width)
    (leftLookup : state.regs.lookup left = some (.word first))
    (rightLookup : state.regs.lookup right = some (.word second)) :
    StackSemEvaluate.evaluate (.inst (.arith (.binop .sub destination left (.reg right))), state) =
      (none, StackSemStateOps.setVar destination (.word (first - second)) state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp,
    leftLookup, rightLookup, wordOpHOL, wordOp]
/-- Genuine full original StackStoreAny compiler constructor. The source
alignment/index guard derives actual native heap access and the complete
postrelation; no target-access, postheap or pointer-restoration premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStoreAny {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackStoreAny register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.stackStoreAny register index : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStoreAny register index),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_stackStoreAny] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  cases valueLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [valueLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [valueLookup] at sourceRun
    cases indexLookup : StackSemStateOps.getVar index source with
    | none =>
      rw [indexLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some indexValue =>
      cases indexValue with
      | loc block offset =>
        rw [indexLookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | word word =>
        rw [indexLookup] at sourceRun
        dsimp only at sourceRun
        by_cases valid : source.stackSpace + (word >>> wordShiftAmount width).toNat < source.stack.length ∧
            (word >>> wordShiftAmount width) <<< wordShiftAmount width = word
        · rw [if_pos valid] at sourceRun
          rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
          subst result
          subst postSource
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have offsetEq := alignedOffset word good valid.2
          have pointerNeRegister : register ≠ pointer := by omega
          have pointerNeIndex : index ≠ pointer := by omega
          have targetValue : target.regs.lookup register = some value := by
            change StackSemStateOps.getVar register target = some value
            rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩]
            exact valueLookup
          have targetIndex : target.regs.lookup index = some (.word word) := by
            change StackSemStateOps.getVar index target = some (.word word)
            rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
            exact indexLookup
          obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
          let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
          change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
          have addressEq : pointerWord + word = base + wordOffset (source.stackSpace + (word >>> wordShiftAmount width).toNat) := by
            calc
              pointerWord + word = pointerWord + wordOffset (word >>> wordShiftAmount width).toNat := by rw [offsetEq]
              _ = _ := by
                dsimp [pointerWord]
                simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
          have read : StackSemStateOps.memLoad (pointerWord + word) target =
              some source.stack[source.stackSpace + (word >>> wordShiftAmount width).toNat] := by
            rw [addressEq]
            exact reads _ valid.1
          have domain : target.mdomain (pointerWord + word) = true := by
            by_contra outside
            simp [StackSemStateOps.memLoad, outside] at read
          let updated := {target with memory := fun key => if key = pointerWord + word then value else target.memory key}
          refine ⟨0, rfl, updated, ?_, ?_⟩
          · simp only [Nat.zero_add]
            rw [comp, StackSemEvaluate.evaluate_seq,
              runAdd target pointer pointer index pointerWord word pointerLookup targetIndex]
            simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
            let shifted := StackSemStateOps.setVar pointer (.word (pointerWord + word)) target
            have shiftedPointer : shifted.regs.lookup pointer = some (.word (pointerWord + word)) := by
              simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
            have shiftedValue : shifted.regs.lookup register = some value := by
              simpa [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNeRegister] using targetValue
            have shiftedDomain : shifted.mdomain (pointerWord + word + 0) = true := by
              simpa [shifted, StackSemStateOps.setVar] using domain
            change StackSemEvaluate.evaluate (.seq (.inst (.mem .store register (.addr pointer 0)))
              (.inst (.arith (.binop .sub pointer pointer (.reg index)))), shifted) = _
            rw [StackSemEvaluate.evaluate_seq,
              StackMemory.runStore shifted register pointer _ 0 value shiftedPointer shiftedValue shiftedDomain]
            simp only [StackSemControl.fixClock, Nat.min_self]
            let written := {shifted with memory := fun key => if key = pointerWord + word + 0 then value else shifted.memory key}
            have writtenPointer : written.regs.lookup pointer = some (.word (pointerWord + word)) := shiftedPointer
            have writtenIndex : written.regs.lookup index = some (.word word) := by
              simpa [written, shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNeIndex] using targetIndex
            change StackSemEvaluate.evaluate (.inst (.arith (.binop .sub pointer pointer (.reg index))), written) = _
            rw [runSub written pointer pointer index _ word writtenPointer writtenIndex]
            simp only [BitVec.add_sub_cancel]
            have restore : StackSemStateOps.setVar pointer (.word pointerWord) shifted = target := by
              dsimp [shifted]
              rw [StackFreeSimulation.setVarTwice, StackFreeSimulation.setVarExisting target pointer (.word pointerWord) pointerLookup]
            let newMemory : BitVec width → WordLocW width :=
              fun key => if key = (pointerWord + word + 0) then value else target.memory key
            change (none, {(StackSemStateOps.setVar pointer (.word pointerWord) shifted) with memory := newMemory}) = _
            rw [restore]
            simp [updated, newMemory]
          · simpa only [updated, relation.1, Nat.add_comm, offsetEq] using
              StackHeapWrites.stateRelStackStore jump bounds pointer (word >>> wordShiftAmount width).toNat
                source target source.stack pointerWord (pointerWord + word) value
                ⟨relation, rfl, pointerLookup, valid.1, by rw [← WordAddressArithmetic.wordOffsetEq, offsetEq]⟩
        · rw [if_neg valid] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
theorem compCorrectStackGetSize {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackGetSize register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.stackGetSize register : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackGetSize register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackGetSize] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  have resultEq := (Prod.mk.inj sourceRun).1.symm
  have sourceEq := (Prod.mk.inj sourceRun).2.symm
  subst result
  subst postSource
  obtain ⟨base, pointerLookup, baseLookup, inverse⟩ := sizeInverse jump bounds pointer source target relation
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, rfl, StackSemStateOps.setVar register (.word (BitVec.ofNat width source.stackSpace)) target, ?_, ?_⟩
  · simp only [Nat.zero_add]
    have execution := runGetSize target register pointer _ base pointerLookup baseLookup (by omega) good
    simpa only [comp, inverse] using execution
  · exact StateUpdates.stateRelSetVar jump bounds pointer register _ source target ⟨relation, lower⟩

/-- Full relation reconstructed after setting the stack position. This is
source-local constructor factoring, with no standalone HOL declaration. -/
theorem stateRelSizeStep {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (safe : count ≤ source.stack.length) :
    ∃ base : BitVec width,
      StackSemStateOps.getVar (pointer + 1) target = some (.word base) ∧
      stateRelHOL jump bounds pointer {source with stackSpace := count}
        (StackSemStateOps.setVar pointer (.word (base + bytesInWord width * BitVec.ofNat width count)) target) := by
  obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  refine ⟨base, baseLookup, ?_⟩
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  have baseNe : pointer + 1 ≠ pointer := by omega
  have heapNe : pointer + 2 ≠ pointer := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have low : ∀ query, query < pointer →
      (target.regs.updateEq (pointer, .word (base + bytesInWord width * BitVec.ofNat width count))).lookup query = source.regs.lookup query := by
    intro query below
    have ne : query ≠ pointer := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne, ite_false] using h18 query below
  simp only [stateRelHOL, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, baseNe, heapNe, ite_false, ite_true, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,low,h19,h20,h21,h22,h23,safe,
    h25.1,reserve,upper,True.intro,heap⟩

/-- Native SetSize executes the original shift and pointer reconstruction.
Lookup premises are supplied from the full source relation in the case below. -/
theorem runSetSize {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (word base : BitVec width)
    (wordLookup : state.regs.lookup register = some (.word word))
    (baseLookup : state.regs.lookup (pointer + 1) = some (.word base))
    (lower : register < pointer)
    (good : goodDimindex width) :
    StackSemEvaluate.evaluate (comp false (0,0) pointer (.stackSetSize register), state) =
      (none, StackSemStateOps.setVar pointer (.word (base + (word <<< wordShiftAmount width)))
        (StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state)) := by
  have shiftBound : wordShiftAmount width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftWidth : wordShiftAmount width < width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftRun : StackSemEvaluate.evaluate (leftShiftInst register (wordShiftAmount width), state) =
      (none, StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state) := by
    simp [leftShiftInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, wordLookup, wordShiftHOL,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftBound, Nat.not_le_of_gt shiftWidth]
  let shifted := StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state
  have shiftedWord : shifted.regs.lookup register = some (.word (word <<< wordShiftAmount width)) := by
    simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have shiftedBase : shifted.regs.lookup (pointer + 1) = some (.word base) := by
    have different : pointer + 1 ≠ register := by omega
    simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, baseLookup]
  rw [comp, StackSemEvaluate.evaluate_seq, shiftRun]
  simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
  change StackSemEvaluate.evaluate (.seq (moveInst pointer (pointer + 1)) (addInst pointer register), shifted) = _
  exact CompCorrect.StackMemoryAny.runMoveAdd shifted pointer (pointer + 1) register base (word <<< wordShiftAmount width) shiftedBase shiftedWord (by omega)
/-- Canonical updates to distinct registers commute. Flapjack infrastructure,
not a standalone HOL port. -/
theorem setVarCommute {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (first second : Nat)
    (a b : WordLocW width) (different : first ≠ second) :
    StackSemStateOps.setVar first a (StackSemStateOps.setVar second b state) =
      StackSemStateOps.setVar second b (StackSemStateOps.setVar first a state) := by
  have maps : (state.regs.updateEq (second,b)).updateEq (first,a) =
      (state.regs.updateEq (first,a)).updateEq (second,b) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases eqFirst : query = first
    · subst query; simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different]
    · by_cases eqSecond : query = second <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eqFirst, eqSecond, Ne.symm different]
  simp [StackSemStateOps.setVar, maps]
/-- Full original StackSetSize case, with precisely the original four premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackSetSize {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackSetSize register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.stackSetSize register : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackSetSize register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackSetSize] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun

  cases lookup : StackSemStateOps.getVar register source with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    cases value with
    | loc first second =>
      rw [lookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word word =>
      rw [lookup] at sourceRun
      simp only [] at sourceRun
      by_cases outsideBounds : source.stack.length ≤ word.toNat
      · rw [if_pos outsideBounds] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      · rw [if_neg outsideBounds] at sourceRun
        have resultEq := (Prod.mk.inj sourceRun).1.symm
        have sourceEq := (Prod.mk.inj sourceRun).2.symm
        subst result
        subst postSource
        obtain ⟨base, baseLookup, postRelation⟩ := stateRelSizeStep jump bounds pointer word.toNat source target
          relation (by omega)
        have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have targetLookup : target.regs.lookup register = some (.word word) := by
          change StackSemStateOps.getVar register target = some (.word word)
          rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower⟩]
          exact lookup
        have shiftEq : word <<< wordShiftAmount width = bytesInWord width * BitVec.ofNat width word.toNat := by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, WordAddressArithmetic.lslWordShift word good, BitVec.mul_comm]
        let pointerTarget := StackSemStateOps.setVar pointer (.word (base + bytesInWord width * BitVec.ofNat width word.toNat)) target
        refine ⟨0, rfl, StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) pointerTarget, ?_, ?_⟩
        · simp only [Nat.zero_add]
          have execution := runSetSize target register pointer word base targetLookup baseLookup lower good
          rw [setVarCommute target pointer register _ _ (by omega), shiftEq] at execution
          simpa only [comp, pointerTarget, shiftEq] using execution
        · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register (.word (word <<< wordShiftAmount width)) {source with stackSpace := word.toNat}
            pointerTarget ⟨postRelation, lower⟩
theorem compCorrectBitmapLoad {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.bitmapLoad register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.bitmapLoad register index : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.bitmapLoad register index),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_bitmapLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_or] at sourceRun
  by_cases same : register = index
  · simp only [same, beq_self_eq_true, if_true] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, if_false] at sourceRun
    cases lookup : StackSemStateOps.getVar index source with
    | none =>
      rw [lookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some value =>
      cases value with
      | loc first second =>
        rw [lookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | word word =>
        rw [lookup] at sourceRun
        simp only [] at sourceRun
        by_cases outsideBounds : source.bitmaps.length ≤ word.toNat
        · rw [dif_pos outsideBounds] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        · rw [dif_neg outsideBounds] at sourceRun
          have resultEq := (Prod.mk.inj sourceRun).1.symm
          have sourceEq := (Prod.mk.inj sourceRun).2.symm
          subst result
          subst postSource
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          obtain ⟨bitmapWord, bitmapLookup, reads⟩ := bitmapReads jump bounds pointer source target relation
          obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
            StackPointer.stateRelGetVarK jump bounds pointer source target relation
          have firstRead := StoreHeapReads.memLoadLemma .bitmapBase source target (.word bitmapWord) base
            ⟨by simp [storeList], by simpa only [StackSemRegisterTransfers.storeOfSyntax] using bitmapLookup,
              by simpa only [List.length_append, Nat.add_comm] using heap⟩
          have targetIndex : target.regs.lookup index = some (.word word) := by
            change StackSemStateOps.getVar index target = some (.word word)
            rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
            exact lookup
          have addressEq : (bitmapWord + word) <<< wordShiftAmount width =
              (bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width word.toNat := by
            simp only [BitVec.shiftLeft_add_distrib, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rw [WordAddressArithmetic.lslWordShift word good, BitVec.mul_comm word]
          have bound : word.toNat < source.bitmaps.length := by omega
          have read := reads word.toNat bound
          rw [← addressEq] at read
          refine ⟨0, rfl, StackSemStateOps.setVar register (.word source.bitmaps[word.toNat]) target, ?_, ?_⟩
          · simp only [Nat.zero_add]
            have execution := runBitmap target register index pointer base bitmapWord word source.bitmaps[word.toNat]
              baseLookup targetIndex (Ne.symm same) firstRead read good
            simpa only [comp] using execution
          · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
              (.word source.bitmaps[word.toNat]) source target ⟨relation, lower.1⟩
theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (first second : Nat)
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.dataBufferWrite first second : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.dataBufferWrite first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStack := relation.1
  rw [StackSemEvaluate.evaluate_dataBufferWrite] at sourceRun
  simp only [useStack, not_true_eq_false, ite_false] at sourceRun
  cases firstLookup : StackSemStateOps.getVar first source with
  | none =>
    simp only [firstLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some firstValue =>
    cases firstValue with
    | loc block offset =>
      simp only [firstLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word address =>
      cases secondLookup : StackSemStateOps.getVar second source with
      | none =>
        simp only [firstLookup, secondLookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some secondValue =>
        cases secondValue with
        | loc block offset =>
          simp only [firstLookup, secondLookup] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        | word value =>
          simp only [firstLookup, secondLookup] at sourceRun
          cases written : wordSemBufferWrite source.dataBuffer address value with
          | none =>
            rw [written] at sourceRun
            exact (notError (Prod.mk.inj sourceRun).1.symm).elim
          | some updated =>
            rw [written] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
            subst result
            subst postSource
            refine ⟨0, rfl, {target with memory := fun key => if key = address then .word value else target.memory key}, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                bufferWriteTargetExecution jump bounds pointer first second source target address value updated
                  relation bound.1 bound.2 firstLookup secondLookup written
            · simpa only [useStack] using bufferWriteStateRel jump bounds pointer source target address value updated relation written

theorem compCorrectFFI {width : Nat} [NeZero width] {C F : Type}
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.ffi name ptr len ptr2 len2 ret, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.ffi name ptr len ptr2 len2 ret : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.ffi name ptr len ptr2 len2 ret),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change ptr < pointer ∧ len < pointer ∧ ptr2 < pointer ∧ len2 < pointer ∧ ret < pointer at bound
  have ptrEq := RelationLaws.stateRelGetVar jump bounds pointer ptr source target ⟨relation,bound.1⟩
  have lenEq := RelationLaws.stateRelGetVar jump bounds pointer len source target ⟨relation,bound.2.1⟩
  have ptr2Eq := RelationLaws.stateRelGetVar jump bounds pointer ptr2 source target ⟨relation,bound.2.2.1⟩
  have len2Eq := RelationLaws.stateRelGetVar jump bounds pointer len2 source target ⟨relation,bound.2.2.2.1⟩
  have ffiEq : target.ffi = source.ffi :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  rw [evaluate_ffi] at sourceRun
  cases readLen : getVar len source with
  | none =>
    simp only [readLen] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some value =>
    cases value with
    | loc block offset =>
      simp only [readLen] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word length1 =>
      cases readPtr : getVar ptr source with
      | none =>
        simp only [readLen, readPtr] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | loc block offset =>
          simp only [readLen, readPtr] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word address1 =>
          cases readLen2 : getVar len2 source with
          | none =>
            simp only [readLen, readPtr, readLen2] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some value =>
            cases value with
            | loc block offset =>
              simp only [readLen, readPtr, readLen2] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | word length2 =>
              cases readPtr2 : getVar ptr2 source with
              | none =>
                simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
              | some value =>
                cases value with
                | loc block offset =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                | word address2 =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  cases read1 : readBytearrayWordHOL address1 length1.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                  | none =>
                    simp only [read1] at sourceRun
                    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                  | some config =>
                    cases read2 : readBytearrayWordHOL address2 length2.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                    | none =>
                      simp only [read1,read2] at sourceRun
                      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                    | some bytes =>
                      have targetRead1 := BytearrayReads.readBytearrayImp jump bounds pointer length1.toNat address1 source target config ⟨relation,read1⟩
                      have targetRead2 := BytearrayReads.readBytearrayImp jump bounds pointer length2.toNat address2 source target bytes ⟨relation,read2⟩
                      simp only [read1,read2] at sourceRun
                      cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                      | final outcome =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        refine ⟨0, rfl, target,?_,ffiEq⟩
                        simpa only [comp,Nat.zero_add] using
                          (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                            simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                      | ret newFfi newBytes =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        have returnedLength := callFFILengthHOL source.ffi (.extCall name) config bytes newBytes newFfi call
                        have readLength := readBytearrayWordHOL_length address2 length2.toNat
                          (memLoadByteAuxExact source.memory source.mdomain source.be) bytes read2
                        have writeRead : readBytearrayWordHOL address2 newBytes.length
                            (memLoadByteAuxExact source.memory source.mdomain source.be) = some bytes := by
                          rw [returnedLength,readLength]
                          exact read2
                        refine ⟨0, rfl, {target with
                          memory := writeBytearrayExact address2 newBytes target.memory target.mdomain target.be
                          regs := restrictIn target.regs target.ffiSaveRegs
                          fpRegs := HolFiniteMapExact.empty
                          ffi := newFfi},?_,?_⟩
                        · simpa only [comp,Nat.zero_add] using
                            (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                              simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                        · exact stateRelFfiWriteback jump bounds pointer source target address2 newBytes bytes newFfi relation writeRead

theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.get register name, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.get register name : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.get register name),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_get] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : source.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, rfl, StackSemStateOps.setVar register value target, ?_, ?_⟩
    · by_cases current : name = .currHeap
      · subst name
        have heapLookup := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [StackSemRegisterTransfers.storeOfSyntax] at lookup
        rw [lookup] at heapLookup
        simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, heapLookup]
      · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        dsimp only at heaps
        cases baseLookup : target.regs.lookup (pointer + 1) with
        | none => simp only [baseLookup] at heaps; exact heaps.2.elim
        | some baseValue =>
          cases baseValue with
          | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
          | word base =>
            simp only [baseLookup] at heaps
            have load := StoreHeapReads.memLoadLemma name source target value base
              ⟨StoreNames.nameCases name current, lookup, by
                simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
            have expression : StackSemExpressions.wordExp target
                (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
                some (base + storeOffset name) := by
              simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
            simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, load]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register value source target
        ⟨relation, bound⟩

/-- Full genuine Set case: the original bound excludes BitmapBase. CurrHeap
updates the reserved target register; every other name uses the full native
store heap write law. Target execution and all post-state relation conjuncts
are derived. The total evaluator retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.set name register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.set name register : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.set name register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_set] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : StackSemStateOps.getVar register source with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have getVarEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
      ⟨relation, bound.1⟩
    have targetLookup : target.regs.lookup register = some value := by
      simpa only [StackSemStateOps.getVar] using getVarEq.symm.trans lookup
    by_cases current : name = .currHeap
    · subst name
      refine ⟨0, rfl, StackSemStateOps.setVar (pointer + 2) value target, ?_, ?_⟩
      · simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, targetLookup]
      · exact stateRelSetCurrHeap jump bounds pointer value source target relation
    · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      dsimp only at heaps
      cases baseLookup : target.regs.lookup (pointer + 1) with
      | none => simp only [baseLookup] at heaps; exact heaps.2.elim
      | some baseValue =>
        cases baseValue with
        | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
        | word base =>
          simp only [baseLookup] at heaps
          have domain := StoreHeapReads.memLoadLemma2 name source target base
            ⟨StoreNames.nameCases name current, by
              simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
          have expression : StackSemExpressions.wordExp target
              (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
              some (base + storeOffset name) := by
            simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
          refine ⟨0, rfl, {target with memory := fun key =>
            if key = base + storeOffset name then value else target.memory key}, ?_, ?_⟩
          · simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, StackSemStateOps.getVar,
              targetLookup, StackSemStateOps.memStore, domain]
          · exact stateRelSetStore jump bounds pointer name value base source target
              current bound.2 baseLookup relation

theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (first second third fourth fifth : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.install first second third fourth fifth, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.install first second third fourth fifth : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.install first second third fourth fifth),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer ∧ third < pointer ∧ fourth < pointer ∧ fifth < pointer at bound
  have firstRead := (RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩).symm
  have secondRead := (RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2.1⟩).symm
  have thirdRead := (RelationLaws.stateRelGetVar jump bounds pointer third source target ⟨relation, bound.2.2.1⟩).symm
  have fourthRead := (RelationLaws.stateRelGetVar jump bounds pointer fourth source target ⟨relation, bound.2.2.2.1⟩).symm
  rw [evaluate_install] at sourceRun
  split at sourceRun
  next _ _ _ _ w1 w2 w3 w4 lookup1 lookup2 lookup3 lookup4 =>
    rcases oracle : source.compileOracle 0 with ⟨cfg, programs, bitmaps⟩
    simp only [oracle, if_pos relation.1] at sourceRun
    split at sourceRun
    next _ _ bytes codeBuffer data dataBuffer codeFlush dataFlush =>
      split at sourceRun
      next _ _ _ compiledBytes nextConfig entry program rest compileRun =>
        split at sourceRun
        next condition =>
          have dataEq : data = bitmaps := by simpa only [oracle] using condition.2.1
          rw [dataEq] at dataFlush
          have programsEq : (entry, program) :: rest = (source.compileOracle 0).2.1 := by
            rw [oracle]
          have compileTransport := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have oracleTransport := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have targetCompile : target.compile cfg
              (((entry, program) :: rest).map (progComp jump bounds pointer)) =
              some (compiledBytes, nextConfig) :=
            (congrFun (congrFun compileTransport cfg) ((entry, program) :: rest)).symm.trans compileRun
          have targetCompileCons := targetCompile
          simp only [List.map_cons, progComp] at targetCompileCons
          have targetOracle : target.compileOracle 0 =
              (cfg, (((entry, program) :: rest).map (progComp jump bounds pointer)), bitmaps) := by
            rw [oracleTransport]
            simp only [oracle]
          have nextConfigEq : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig := by
            simpa only [holShiftSeq, oracleTransport] using condition.2.2
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          refine ⟨0, rfl, installedState first entry
            (((entry, program) :: rest).map (progComp jump bounds pointer)) bitmaps
            codeBuffer target.dataBuffer target, ?_, ?_⟩
          · simpa only [comp, Nat.zero_add] using
              (evaluate_install first second third fourth fifth target).trans (by
                simp only [firstRead, secondRead, thirdRead, fourthRead,
                  lookup1, lookup2, lookup3, lookup4, targetOracle,
                  relation.2.2.1, Bool.false_eq_true, if_false,
                  relation.2.2.2.2.2.2.2.2.2.2.2.2.1, codeFlush,
                  targetCompileCons, List.map_cons, progComp, condition.1, nextConfigEq,
                  and_self, if_true, installedState])
          · exact stateRelInstall jump bounds pointer first entry source target
              ((entry, program) :: rest) bitmaps codeBuffer dataBuffer w3 w4
              relation bound.1 programsEq dataFlush
        next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
open Flapjack.Compiler.Backend.StackRemove.StackFreeSimulation
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.ShMemOp
theorem evaluateStackFree_zero {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (stackFree pointer count,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨sourceRun, notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackFree] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases safe : source.stack.length < source.stackSpace + count
  · rw [if_pos safe] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · rw [if_neg safe] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, _baseLookup, _lower, _upper, pointerLookup, _heap⟩ :=
      StackPointer.stateRelGetVarK jump bounds pointer source target relation
    have lookup : target.regs.lookup pointer =
        some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := pointerLookup
    refine ⟨0, rfl, StackSemStateOps.setVar pointer
      (.word ((base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count)) target, ?_, ?_⟩
    · simpa only [Nat.zero_add] using runFree count pointer target _ lookup
    · simpa only [lookup, relation.1] using stateRelFreeStep jump bounds pointer count source target relation (Nat.le_of_not_gt safe)
theorem compCorrectStackFree {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.stackFree count) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  obtain ⟨clock, zero, postTarget, targetRun, postRelation⟩ :=
    evaluateStackFree_zero jump bounds pointer count source target postSource result
      ⟨sourceRun, notError, relation⟩
  refine ⟨clock, zero, postTarget, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => exact postRelation
    | some result =>
      cases result <;> first | exact postRelation | exact postRelation.2.2.2.2.2.2.2.2.2.1

theorem compCorrectShMemOp {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (register base : Nat) (offset : BitVec width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.shMemOp op register (.addr base offset), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.shMemOp op register (.addr base offset) : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.shMemOp op register (.addr base offset)),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change register < pointer ∧ base < pointer at bound
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_shMemOp] at sourceRun
  cases addressRun : StackSemExpressions.wordExp source (.op .add [.var base, .const offset]) with
  | none =>
    simp only [addressRun] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some address =>
    have targetAddress := ExpressionSimulation.stateRelWordExp jump bounds pointer source target
      (.op .add [.var base, .const offset]) address
      ⟨relation, by simpa [Flapjack.Compiler.Backend.StackProps.regBoundExp] using bound.2, addressRun⟩
    simp only [addressRun] at sourceRun
    by_cases zero : source.clock = 0
    · simp only [zero, ite_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, rfl, emptyEnv target, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
    · simp only [zero, ite_false] at sourceRun
      obtain ⟨postTarget, targetRun, postRelation⟩ := shMemOpSimulation jump bounds pointer register
        op address (decClock source) (decClock target) postSource result
        (RelationLaws.stateRelDecClock jump bounds pointer source target relation)
        bound.1 sourceRun notError
      refine ⟨0, rfl, postTarget, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_false]; exact targetRun)
      · cases result with
        | none => exact postRelation
        | some outcome => cases outcome <;> exact postRelation

#print axioms compCorrectStackFree
#print axioms compCorrectShMemOp
#print axioms compCorrectStackLoad
#print axioms compCorrectStackStore
#print axioms compCorrectStackLoadAny
#print axioms compCorrectStackStoreAny
#print axioms compCorrectStackGetSize
#print axioms compCorrectStackSetSize
#print axioms compCorrectBitmapLoad
#print axioms compCorrectDataBufferWrite
#print axioms compCorrectFFI
#print axioms compCorrectGet
#print axioms compCorrectSet
#print axioms compCorrectInstall
end InitECandidate.Runtime.StackRemove.MemoryZero
