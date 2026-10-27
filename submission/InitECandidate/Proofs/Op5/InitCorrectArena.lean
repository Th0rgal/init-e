import InitECandidate.Proofs.Op5.InitPreArena
import InitECandidate.Proofs.Op5.InitPropArena

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect

/-! Scratch extension of the pinned initializer correctness proof. Scalar
pointer computations are unchanged; the independent scratch graph is retained
through symbolic execution and merged into the source relation's memory. -/
theorem initCodeThmWithArena {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (s : StackSemStateFiniteExact width C F) (arena : BitVec width → Prop) (jump : Bool) (bounds : BitVec width × BitVec width)
    (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hyp : initCodePreWithArena pointer bitmaps dataSpace s arena ∧
      codeRelHOL jump bounds pointer code s.code ∧
      s.compileOracle = (fun index =>
        let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        Compiler.Backend.StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      maxStackAlloc ≤ maxHeap) :
    match StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
    | (some _, _) => False
    | (none, t) =>
      (∃ w2 w3 w4 : BitVec width,
        s.regs.lookup 2 = some (.word w2) ∧ holByteAligned w2 = true ∧
        t.regs.lookup (pointer + 2) = some (.word w2) ∧
        s.regs.lookup 4 = some (.word w4) ∧ holByteAligned w4 = true ∧ w2 < w4 ∧
        t.regs.lookup pointer = some (.word (w4 - bytesInWord width)) ∧
        (w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3 ∧
          w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width ∧
          (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat ∧
          (bytesInWord width).toNat * maxHeap < 2 ^ width →
          t.regs.lookup (pointer + 1) =
            some (.word ((((w3 + -1 * w2) >>> (wordShiftAmount width + 1)) <<<
              (wordShiftAmount width + 1)) + w2 +
              bytesInWord width * BitVec.ofNat width storeList.length))) ∧
        s.regs.lookup 3 = some (.word w3)) ∧
      stateRelHOL jump bounds pointer
        (withArena arena (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t)) t ∧
      t.ffi = s.ffi ∧
      initPropWithArena generateGc maxHeap dataSpace
        (InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s))
        (withArena arena (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t)) arena ∧
      s.mdomain = t.mdomain ∧ s.shMdomain = t.shMdomain ∧
      (let t0 := withArena arena (InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t)
       SetSep.fun2Set (s.memory, fun a => t0.mdomain a = true) =
         SetSep.fun2Set (t.memory, fun a => t0.mdomain a = true)) := by
  classical
  obtain ⟨pre, codeRel, oracleEq, oracleBound, errLab, maxOk⟩ := hyp
  obtain ⟨p2, p3, p4, bp, good, k8, entry, saveRegs, noStack, noStore, noAlloc, read2, read3,
    read4, mem0, mem1, mem2, mem3, mem4, le, big, al2, al4, albp, cbEmpty, heap⟩ := pre
  have a2 := (byteAligned_iff good p2).mp al2
  have a4 := (byteAligned_iff good p4).mp al4
  have bnat : (bytesInWord width).toNat = width / 8 := by
    rcases good with h | h <;> subst h <;> rfl
  have diff : (p4 - p2).toNat = p4.toNat - p2.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact le)]
  have big' : 1024 * (width / 8) ≤ p4.toNat - p2.toNat := by
    rw [← diff]
    have : (1024 * bytesInWord width).toNat = 1024 * (width / 8) := by
      rcases good with h | h <;> subst h <;> rfl
    omega
  have bpos : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  obtain ⟨adjLe, shrLe, heapLength, stackLength, regEqN, endEqN, even, heapLe, heapLow,
    stackLow⟩ := initLayout good maxHeap maxOk p2 p3 p4 le big' a2 a4
  set reg3 := roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
    (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap)) with hreg3
  have regEq := addMulOfNat good p2 reg3 heapLength regEqN
  have endEq := addMulOfNat good reg3 p4 stackLength endEqN
  have count : (p4 - p2).toNat / (bytesInWord width).toNat = heapLength + stackLength := by
    rw [diff, bnat, endEqN, regEqN]
    rw [show p2.toNat + heapLength * (width / 8) + stackLength * (width / 8) - p2.toNat =
      (heapLength + stackLength) * (width / 8) by rw [Nat.add_mul]; omega]
    exact Nat.mul_div_cancel _ bpos
  rw [count] at heap
  have long : storeList.length + 1 ≤ stackLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at stackLow; omega
  obtain ⟨heapValues, storeValues, restValues, last, hlen, slen, rlen, split⟩ :=
    initHeapSplit _ p2 reg3 p4 heapLength stackLength _ _ regEq endEq long heap
  set B := SetSep.star (Misc.wordList bp (bitmaps.map WordLocW.word))
    (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
      dataSpace) with hB
  set A := memoryHOL s.memory arena with hA
  set P0 := SetSep.star B A with hP0
  set H := Misc.wordList p2 heapValues with hH
  set S := Misc.wordList reg3 storeValues with hS
  set R := Misc.wordList (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)
    restValues with hR
  set D : BitVec width → Prop := fun a => s.mdomain a = true with hD
  -- header reads and domain
  have headerSplit : SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H (SetSep.fun2Set (s.memory, D)) := by
    rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, last)) by ac_rfl]
    exact split
  have heapBig : 5 ≤ heapLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at heapLow; omega
  have domain5 : ∀ i, i < 5 →
      s.mdomain (p2 + BitVec.ofNat width i * bytesInWord width) = true := by
    intro i hi
    have := (framedListRead _ p2 heapValues s.memory D headerSplit i (by omega)).2
    rw [BitVec.mul_comm] at this
    exact this
  -- the final stack word
  have lastDomain : s.mdomain (p4 - bytesInWord width) = true := by
    obtain ⟨part, single, sub⟩ := starRightMember _ _ _ split
    have member := sub (p4 - bytesInWord width, last) (by rw [single])
    exact ((SetSep.fun2SetThm _ _ _ _).mp member).2
  have written := StoreListCodeThm.writeWord (.word 0) last (p4 - bytesInWord width)
    (SetSep.star (SetSep.star (SetSep.star P0 H) S) R) s.memory D
    (by rw [SetSep.starComm]; exact split)
  have storeHeap : SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0)))
      (SetSep.fun2Set ((fun key => if key = p4 - bytesInWord width then .word 0
        else s.memory key), D)) := by
    rw [show SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, .word 0)) by ac_rfl]
    exact written
  obtain ⟨t, run, shape, t0, t1, t2, t3, t4, t5, t6, t7, tk, tk1, tk2, tOther, tHeap⟩ :=
    runInitCode generateGc maxHeap pointer s p2 p3 p4 bp _ _ _ _ good k8 read2 read3 read4
      domain5 mem0 rfl rfl rfl rfl lastDomain entry storeValues _ slen storeHeap
  rw [run]
  dsimp only
  -- computed initializer pointers in the post-state
  have sl48 : storeList.length = 48 := rfl
  have basePtr : wordSemTheWord (holFapply t.regs (pointer + 1)) =
      reg3 + bytesInWord width * BitVec.ofNat width storeList.length := by
    rw [holFapply_of_lookup tk1]; rfl
  have heapPtr : wordSemTheWord (holFapply t.regs (pointer + 2)) = p2 := by
    rw [holFapply_of_lookup tk2]; rfl
  have stackPtr : wordSemTheWord (holFapply t.regs pointer) = p4 - bytesInWord width := by
    rw [holFapply_of_lookup tk]; rfl
  have heapSpace : ((reg3 + bytesInWord width * BitVec.ofNat width storeList.length) - p2).toNat /
      (width / 8) - storeList.length = heapLength := by
    rw [sl48]
    exact (spaceCounts good p2 reg3 p4 heapLength stackLength regEqN endEqN (by omega)).1
  have stackSpace : ((p4 - bytesInWord width) -
      (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)).toNat / (width / 8) =
      stackLength - (storeList.length + 1) := by
    rw [sl48]
    exact (spaceCounts good p2 reg3 p4 heapLength stackLength regEqN endEqN (by omega)).2
  have ffiEq : t.ffi = s.ffi := (congrArg (·.ffi) shape).trans rfl
  have mdomEq : t.mdomain = s.mdomain := (congrArg (·.mdomain) shape).trans rfl
  have shmEq : t.shMdomain = s.shMdomain := (congrArg (·.shMdomain) shape).trans rfl
  have codeEq : t.code = s.code := (congrArg (·.code) shape).trans rfl
  have cbEq : t.codeBuffer = s.codeBuffer := (congrArg (·.codeBuffer) shape).trans rfl
  have oracleT : t.compileOracle = s.compileOracle := (congrArg (·.compileOracle) shape).trans rfl
  have saveT : t.ffiSaveRegs = s.ffiSaveRegs := (congrArg (·.ffiSaveRegs) shape).trans rfl
  have flagsT : t.useStack = s.useStack ∧ t.useStore = s.useStore ∧ t.useAlloc = s.useAlloc :=
    ⟨(congrArg (·.useStack) shape).trans rfl, (congrArg (·.useStore) shape).trans rfl,
      (congrArg (·.useAlloc) shape).trans rfl⟩
  set T0 := InitReduce.initReduce generateGc jump bounds pointer code bitmaps dataSpace oracle t
    with hT0
  have heapDom : ∀ a, T0.mdomain a = true ↔ addresses p2 heapLength a := by
    intro a
    simp only [hT0, InitReduce.initReduce]
    erw [heapPtr, basePtr, heapSpace, decide_eq_true_iff]
  set NS := Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
    (MemVal.memVal t.regs)) with hNS
  have tHeapLast : SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) H (SetSep.fun2Set (t.memory, D)) := by
    rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) H =
      SetSep.star NS (SetSep.star (SetSep.star (SetSep.star P0 H) R)
        (SetSep.one (p4 - bytesInWord width, .word 0))) by ac_rfl]
    exact tHeap
  -- the stored initial values
  have storeVal : ∀ name, name ∈ StoreName.currHeap :: storeList →
      T0.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) =
        some (MemVal.memVal t.regs (storeInit generateGc pointer name)) := by
    intro name member
    simp only [hT0, InitReduce.initReduce, HolFiniteMapExact.lookup_updateListEq]
    apply foldUpdate_lookup_mem
    · rw [List.map_map]
      convert storeKeysNodup using 2
      funext n
      simp only [Function.comp_apply]
      split <;> rfl
    · refine List.mem_map.mpr ⟨name, member, ?_⟩
      split <;> rename_i h <;> simp [h, MemVal.memVal]
  have bitmapBaseLookup : T0.store.lookup .bitmapBase =
      some (.word (bp >>> wordShiftAmount width)) := by
    have := storeVal .bitmapBase (by decide)
    simpa [storeInit, MemVal.memVal, holFapply_of_lookup t3,
      StackSemRegisterTransfers.storeOfSyntax] using this
  have currLookup : T0.store.lookup .currHeap = some (.word p2) := by
    have := storeVal .currHeap (by decide)
    simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
      StackSemRegisterTransfers.storeOfSyntax] using this
  have bitmapBack : (bp >>> wordShiftAmount width) <<< wordShiftAmount width = bp :=
    alignedShift good bp albp
  -- the initial stack
  set base := reg3 + bytesInWord width * BitVec.ofNat width storeList.length with hbase
  have lastAddr : base + bytesInWord width * BitVec.ofNat width restValues.length =
      p4 - bytesInWord width := by
    rw [rlen, hbase, sl48, endEq, lastWordAddress reg3 stackLength (by omega)]
  have stackHeap : Misc.wordList base (restValues ++ [.word 0]) =
      SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0)) := by
    rw [StackHeap.wordListAppend, wordListSingleton, lastAddr]
  have stackSp : T0.stackSpace = stackLength - (storeList.length + 1) := by
    simp only [hT0, InitReduce.initReduce]
    erw [stackPtr, basePtr, stackSpace]
  have stackVal : T0.stack = restValues ++ [.word 0] := by
    have read := InitReadMemory.wordListImpReadMem t.memory D (restValues ++ [.word 0]) base
      (SetSep.star (SetSep.star NS P0) H) (by
        rw [stackHeap]
        rw [show SetSep.star (SetSep.star (SetSep.star NS P0) H)
          (SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0))) =
          SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
            (SetSep.one (p4 - bytesInWord width, .word 0))) H by ac_rfl]
        exact tHeapLast)
    have lenEq : (restValues ++ [WordLocW.word 0]).length = T0.stackSpace + 1 := by
      rw [stackSp]; simp [rlen]
    rw [lenEq] at read
    simp only [hT0, InitReduce.initReduce] at read ⊢
    erw [stackPtr, basePtr] at read ⊢
    exact read
  have baseNat : base.toNat = reg3.toNat + storeList.length * (width / 8) :=
    addWordsNat good reg3 storeList.length (by
      have := p4.isLt
      have : storeList.length * (width / 8) ≤ stackLength * (width / 8) :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  have arenaHeap : SetSep.star A
      (SetSep.star NS (SetSep.star (SetSep.star (SetSep.star B H) R)
        (SetSep.one (p4 - bytesInWord width,.word 0))))
      (SetSep.fun2Set (t.memory,D)) := by
    rw [show SetSep.star A
      (SetSep.star NS (SetSep.star (SetSep.star (SetSep.star B H) R)
        (SetSep.one (p4 - bytesInWord width,.word 0)))) =
      SetSep.star NS (SetSep.star (SetSep.star (SetSep.star P0 H) R)
        (SetSep.one (p4 - bytesInWord width,.word 0))) by dsimp only [P0]; ac_rfl]
    exact tHeap
  have scratchAgree : ∀ a, arena a → t.memory a = s.memory a := by
    intro a ha
    exact (MemoryReads.memoryFun2SetImpRead s.memory t.memory arena D _ a ⟨arenaHeap,ha⟩).2
  have arenaEq : memoryHOL T0.memory arena = A := by
    have graphs : SetSep.fun2Set (T0.memory,arena) = SetSep.fun2Set (s.memory,arena) := by
      funext entry
      rcases entry with ⟨a,v⟩
      apply propext
      simp only [SetSep.fun2SetThm]
      by_cases ha : arena a
      · rw [show T0.memory a = s.memory a from scratchAgree a ha]
      · simp [ha]
    change (fun heap => heap = SetSep.fun2Set (T0.memory,arena)) =
      (fun heap => heap = SetSep.fun2Set (s.memory,arena))
    rw [graphs]
  have memEq : memoryHOL T0.memory (fun a => T0.mdomain a = true) = H := by
    have domEq : (fun a => T0.mdomain a = true) = addresses p2 heapLength := by
      funext a; exact propext (heapDom a)
    rw [domEq]
    have framed : SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star NS P0) R)
        (SetSep.one (p4 - bytesInWord width, .word 0))) H) SetSep.emp
        (SetSep.fun2Set (t.memory, D)) := by
      rw [SetSep.starComm _ SetSep.emp, StackHeap.starEmptyLeft]; exact tHeapLast
    have inMem := WordListMemory.wordListInMemory p2 heapValues _ _ t.memory D
      ⟨framed, good, by
        rw [hlen, bnat]
        have := p4.isLt
        have : heapLength * (width / 8) ≤ heapLength * (width / 8) + stackLength * (width / 8) :=
          Nat.le_add_right _ _
        omega⟩
    rw [hlen] at inMem
    exact inMem
  have disjoint : ∀ a, ¬ (T0.mdomain a = true ∧ arena a) := by
    apply memory_domains_disjoint T0.memory (fun a => T0.mdomain a = true) arena
      (SetSep.star B (SetSep.star NS (SetSep.star R (SetSep.one (p4 - bytesInWord width,.word 0)))))
      (SetSep.fun2Set (t.memory,D))
    rw [memEq,arenaEq]
    rw [show SetSep.star H (SetSep.star A
      (SetSep.star B (SetSep.star NS (SetSep.star R (SetSep.one (p4 - bytesInWord width,.word 0)))))) =
      SetSep.star NS (SetSep.star (SetSep.star (SetSep.star P0 H) R)
        (SetSep.one (p4 - bytesInWord width,.word 0))) by dsimp only [P0]; ac_rfl]
    exact tHeap
  have unionMemEq : memoryHOL T0.memory
      (fun a => (T0.mdomain a || decide (arena a)) = true) = SetSep.star H A := by
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    rw [memory_union_split T0.memory _ arena disjoint,memEq,arenaEq]
  refine ⟨⟨p2, p3, p4, read2, al2, tk2, read4, al4, ?lt, tk, ?impl, read3⟩, ?rel, ffiEq, ?prop,
    mdomEq.symm, shmEq.symm, ?mem⟩
  case lt =>
    rw [BitVec.lt_def]; omega
  case impl =>
    rintro ⟨lo, hi, hm, hb⟩
    rw [tk1, ← thirdInRange good maxHeap p2 p3 p4 lo hi hm hb]
  case mem =>
    have agree : ∀ a, addresses p2 heapLength a → s.memory a = t.memory a := by
      intro a member
      obtain ⟨i, hi, rfl⟩ := (mem_addresses heapLength p2 a).mp member
      rw [BitVec.mul_comm]
      rw [(framedListRead _ p2 heapValues s.memory D headerSplit i (by omega)).1,
        (framedListRead _ p2 heapValues t.memory D tHeapLast i (by omega)).1]
    funext entry
    rcases entry with ⟨a, v⟩
    apply propext
    simp only [SetSep.fun2SetThm,withArena,Bool.or_eq_true,decide_eq_true_eq,heapDom]
    constructor
    · rintro ⟨eq, dom⟩
      refine ⟨?_,dom⟩
      rcases dom with h | h
      · exact (agree a h).symm.trans eq
      · exact (scratchAgree a h).trans eq
    · rintro ⟨eq, dom⟩
      refine ⟨?_,dom⟩
      rcases dom with h | h
      · exact (agree a h).trans eq
      · exact (scratchAgree a h).symm.trans eq
  case rel =>
    have storeEq : wordStoreHOL base T0.store = NS := by
      unfold wordStoreHOL
      rw [hNS, WordListReverse.wordListEqRev]
      simp only [List.length_map, List.length_reverse]
      rw [BitVec.mul_comm (BitVec.ofNat width storeList.length)]
      congr 1
    have stackEq : Misc.wordList base T0.stack =
        SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0)) := by
      rw [stackVal, stackHeap]
    have positionEq : T0.dataBuffer.position = bp + bytesInWord width *
        BitVec.ofNat width bitmaps.length := by
      simp only [hT0, InitReduce.initReduce]
      erw [holFapply_of_lookup t3]
      exact congrArg (· + _) bitmapBack
    unfold stateRelHOL
    simp only [withArena]
    refine ⟨by simp [hT0, InitReduce.initReduce], by simp [hT0, InitReduce.initReduce],
      flagsT.1.trans noStack, flagsT.2.1.trans noStore, flagsT.2.2.trans noAlloc,
      by simp [hT0, InitReduce.initReduce], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      oracleT.trans oracleEq, oracleBound, good, fun _ _ => rfl, codeEq ▸ codeRel,
      codeEq ▸ errLab, tk2.trans currLookup.symm, saveT ▸ saveRegs,
      by rw [bitmapBaseLookup]; rfl, InitReduce.initReduceStackSpace _ _ _ _ _ _ _ _ t, ?_⟩
    rw [bitmapBaseLookup]
    simp only [Option.map_some, wordLocWToGeneric, theSomeWord, bitmapBack]
    refine ⟨by rw [positionEq]; rfl, ?_⟩
    rw [tk1]
    simp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [baseNat, regEqN]; simp only [maxStackAlloc] at heapLow ⊢
      have : 255 * (width / 8) ≤ (heapLength + storeList.length) * (width / 8) :=
        Nat.mul_le_mul_right _ heapLow
      rw [Nat.add_mul] at this; omega
    · rw [stackVal, baseNat, bnat]
      simp only [List.length_append, List.length_singleton, rlen]
      have := p4.isLt
      have split : stackLength = storeList.length + (stackLength - (storeList.length + 1)) + 1 := by
        omega
      have : (width / 8) * (stackLength - (storeList.length + 1) + 1) +
          storeList.length * (width / 8) = stackLength * (width / 8) := by
        conv => rhs; rw [split]
        ring
      omega
    · rw [tk, stackSp, ← rlen, lastAddr]
    · rw [unionMemEq, stackEq, storeEq, mdomEq]
      simp only [hT0, InitReduce.initReduce, List.append_nil]
      rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star (SetSep.star H A)
          (Misc.wordList bp (bitmaps.map WordLocW.word)))
          (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
            dataSpace)) NS) (SetSep.star R (SetSep.one (p4 - bytesInWord width, .word 0))) =
        SetSep.star NS (SetSep.star (SetSep.star (SetSep.star P0 H) R)
          (SetSep.one (p4 - bytesInWord width, .word 0))) by rw [hP0,hB]; ac_rfl]
      exact tHeap
  case prop =>
    have half := halfHeapWord good p2 reg3 heapLength regEqN even
    have pointers : InitLimits.readPointers s = (p2, p3, p4) := by
      simp [InitLimits.readPointers, read2, read3, read4, holThe, wordSemTheWord]
    have limits : InitLimits.getStackHeapLimit maxHeap (InitLimits.readPointers s) =
        (stackLength - storeList.length, heapLength / 2) := by
      rw [pointers, getStackHeapLimit_eq, ← hreg3, InitLimitsDouble.getStackHeapLimitDouble,
        endEqN, regEqN]
      have d2 : p2.toNat / (width / 8) * (width / 8) = p2.toNat := Nat.div_mul_cancel
        (Nat.dvd_of_mod_eq_zero a2)
      rw [Nat.add_mul_div_right _ _ bpos, Nat.add_mul_div_right _ _ bpos]
      congr 1 <;> omega
    have stackLen : T0.stack.length = stackLength - storeList.length := by
      rw [stackVal]; simp [rlen]; omega
    have word2 : p2 + bytesInWord width + bytesInWord width = p2 + 2 * bytesInWord width := by
      ring
    have word3 : p2 + bytesInWord width + bytesInWord width + bytesInWord width =
        p2 + 3 * bytesInWord width := by ring
    have word4 : p2 + bytesInWord width + bytesInWord width + bytesInWord width +
        bytesInWord width = p2 + 4 * bytesInWord width := by ring
    rw [word2, mem2] at t6
    rw [word3, mem3] at t7
    rw [word4, mem4] at t1
    rw [mem1] at t4
    have halfX := half
    rw [hreg3] at halfX
    have positionEq : T0.dataBuffer.position = bp + bytesInWord width *
        BitVec.ofNat width bitmaps.length := by
      simp only [hT0, InitReduce.initReduce]
      erw [holFapply_of_lookup t3]
      exact congrArg (· + _) bitmapBack
    have look : ∀ name, name ∈ StoreName.currHeap :: storeList →
        T0.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) =
          some (MemVal.memVal t.regs (storeInit generateGc pointer name)) := storeVal
    -- the bitmap/data lists fit in the address space
    have fits : bitmaps.length + dataSpace + 1 < 2 ^ width := by
      set X := SetSep.star A (SetSep.star (SetSep.star (SetSep.star H S) R)
        (SetSep.one (p4 - bytesInWord width, last))) with hX
      have pre : SetSep.star (SetSep.star X (Misc.wordList bp (bitmaps.map WordLocW.word)))
          (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
            dataSpace) (SetSep.fun2Set (s.memory, D)) := by
        rw [show SetSep.star (SetSep.star X (Misc.wordList bp (bitmaps.map WordLocW.word)))
          (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
            dataSpace) =
          SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
            (SetSep.one (p4 - bytesInWord width, last)) by rw [hX, hP0,hB]; ac_rfl]
        exact split
      obtain ⟨ds, dlen, listed⟩ := (starWordListExists _ _ _ _).mp pre
      have joined : SetSep.star X (Misc.wordList bp (bitmaps.map WordLocW.word ++ ds))
          (SetSep.fun2Set (s.memory, D)) := by
        rw [StackHeap.wordListAppend, List.length_map, SetSep.starAssoc]
        exact listed
      have bound := wordListNoWrap good X bp _ s.memory D joined
      simp only [List.length_append, List.length_map, dlen] at bound
      have : 2 ^ width / (width / 8) ≤ 2 ^ width / 4 :=
        Nat.div_le_div_left (by rcases good with h | h <;> subst h <;> decide) (by decide)
      have : 2 ^ width / 4 + 1 < 2 ^ width := by
        rcases good with h | h <;> subst h <;> norm_num
      omega
    have spaceLeft : T0.dataBuffer.spaceLeft = dataSpace := by
      simp [hT0, InitReduce.initReduce]
    have bufferNil : T0.dataBuffer.buffer = [] := by simp [hT0, InitReduce.initReduce]
    have cbT0 : T0.codeBuffer = s.codeBuffer := cbEq
    have stackSpEq : T0.stack.length = T0.stackSpace + 1 := by
      rw [stackLen, stackSp]; omega
    have heapHalf : SetSep.star (Misc.wordListExists p2 (heapLength / 2))
        (Misc.wordListExists (p2 + (reg3 - p2) >>> (1 : Nat)) (heapLength / 2))
        (SetSep.fun2Set (T0.memory, fun a => T0.mdomain a = true)) := by
      have domEq : (fun a => T0.mdomain a = true) = addresses p2 heapLength := by
        funext a; exact propext (heapDom a)
      rw [domEq, half, BitVec.mul_comm, ← WordListMemory.wordListExistsAdd,
        show heapLength / 2 + heapLength / 2 = heapLength by omega]
      exact WordListMemory.wordListExistsAddresses T0.memory heapLength p2
        ⟨by rw [Nat.mul_comm]; have := reg3.isLt; omega, good⟩
    unfold initPropWithArena
    simp only [withArena]
    refine ⟨p2, p2 + (reg3 - p2) >>> (1 : Nat), bp >>> wordShiftAmount width, heapLength / 2,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
        StackSemRegisterTransfers.storeOfSyntax] using look .currHeap (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
        StackSemRegisterTransfers.storeOfSyntax] using look .nextFree (by decide)
    · cases generateGc <;>
        simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2, holFapply_of_lookup t2,
          StackSemRegisterTransfers.storeOfSyntax] using look .triggerGC (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t2,
        StackSemRegisterTransfers.storeOfSyntax] using look .endOfHeap (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t2,
        StackSemRegisterTransfers.storeOfSyntax] using look .otherHeap (by decide)
    · exact bitmapBaseLookup
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t5, halfX,
        StackSemRegisterTransfers.storeOfSyntax] using look .heapLength (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .progStart (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .allocSize (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .globals (by decide)
    · simpa [storeInit, MemVal.memVal, holFapply_of_lookup tk2,
        StackSemRegisterTransfers.storeOfSyntax] using look .globReal (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .handler (by decide)
    · simpa [storeInit, MemVal.memVal,
        StackSemRegisterTransfers.storeOfSyntax] using look .genStart (by decide)
    · rw [cbT0]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t7,
        StackSemRegisterTransfers.storeOfSyntax] using look .codeBuffer (by decide)
    · rw [cbT0]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t1,
        StackSemRegisterTransfers.storeOfSyntax] using look .codeBufferEnd (by decide)
    · rw [positionEq]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t4,
        StackSemRegisterTransfers.storeOfSyntax] using look .bitmapBuffer (by decide)
    · rw [positionEq, spaceLeft]
      simpa [storeInit, MemVal.memVal, holFapply_of_lookup t6,
        StackSemRegisterTransfers.storeOfSyntax] using look .bitmapBufferEnd (by decide)
    · rw [limits]
      refine ⟨?_, ?_, stackLen.symm⟩
      · simpa [storeInit, MemVal.memVal, holFapply_of_lookup t5, halfX,
          StackSemRegisterTransfers.storeOfSyntax] using look .heapLength (by decide)
      · show heapLength / 2 * (width / 8) < 2 ^ width
        have := reg3.isLt
        have : heapLength / 2 * (width / 8) ≤ heapLength * (width / 8) :=
          Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
        omega
    · rw [cbT0]; exact cbEmpty
    · exact bufferNil
    · simp [hT0, InitReduce.initReduce]
    · simp [hT0, InitReduce.initReduce]
    · exact t0
    · exact fits
    · rw [stackLen]; have := p4.isLt
      have : stackLength ≤ stackLength * (width / 8) := Nat.le_mul_of_pos_right _ bpos
      omega
    · rw [half, BitVec.mul_comm]
    · exact al2
    · rw [stackVal]; exact holLast_append_singleton _ _
    · exact stackSpEq
    · rw [stackLen]; have := p4.isLt
      have : (stackLength - storeList.length) * (width / 8) ≤ stackLength * (width / 8) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
    · omega
    · simpa only [Bool.or_eq_true,decide_eq_true_eq] using
        assertion_arena_extend T0.memory _ arena _ heapHalf disjoint


#print axioms initCodeThmWithArena
end InitE.Op5
