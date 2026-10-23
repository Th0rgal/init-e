import InitECandidate.Proofs.Op5.WordInitArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyPanToWord

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Pancake.Proofs.PanToTarget

theorem readPointers_s2_withArena {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {t : LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {arena : BitVec width → Prop}
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena)
    {w2 w3 w4 : BitVec width} (h2 : t.regs t.lenReg = .word w2)
    (h3 : t.regs t.ptr2Reg = .word w3) (h4 : t.regs t.len2Reg = .word w4) :
    StackRemove.Proofs.InitLimits.readPointers
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = (w2, w3, w4) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n4, n3, n2, -, -, hbij⟩ := id hA
  simp only [StackRemove.Proofs.InitLimits.readPointers, s2_regs_lookup hbij (.inl rfl),
    s2_regs_lookup hbij (.inr (.inl rfl)), s2_regs_lookup hbij (.inr (.inr rfl)), n2, n3, n4,
    h2, h3, h4, holThe, wordSemTheWord]

open StackToLab.Proofs.FullMakeInitSemantics in
/-- The pan_to_word stage of the HOL proof (lines 2103-2284) with its stack-state
premises discharged: on a successful `full_make_init` from the lab state `t`
(under `full_make_init_semantics`' hypotheses), the source-code word state built by
`word_to_stack`'s `make_init` runs as the Pancake program. The facts about `t` are
those of `lab_to_target$make_init` over `pan_installed`'s memory `m` (heap words,
the source memory on `s.memaddrs`, shared domain, endianness, FFI) and its initial
`len`/`ptr2`/`len2` registers; the rest are the top theorem's hypotheses, with
HOL's `byte_aligned s.top_addr` and the `HeapLength` value derived here. -/
theorem panToWordFromInitWithArena {width : Nat} [NeZero width] {C σ : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {t : LabSem.State width C σ}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C σ}
    (ac : AsmConfigExact width) (k : Nat) (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize heapLen : Nat)
    (w3 w4 : BitVec width)
    {arena : BitVec width → Prop}
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle arena)
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle arena = (sst, some x))
    (h2 : t.regs t.lenReg = .word s.baseAddr) (h3 : t.regs t.ptr2Reg = .word w3)
    (h4 : t.regs t.len2Reg = .word w4) (hlt : s.baseAddr < w3)
    (hlo : s.baseAddr + BitVec.ofNat width StackRemove.maxStackAlloc *
      StackRemove.bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width StackRemove.maxStackAlloc *
      StackRemove.bytesInWord width)
    (hheap : (-1 * s.baseAddr + w3).toNat ≤ maxHeap * (StackRemove.bytesInWord width).toNat)
    (hheapLt : (StackRemove.bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * s.baseAddr) = true)
    (htmem : ∀ a, s.memaddrs a → t.memory a = wlabWlocExact (s.memory a))
    (htword : ∀ a, a.toNat % (width / 8) = 0 → ∃ w, t.memory a = .word w)
    (htsh : (fun a => t.sharedMemDomain a = true) = s.shMemaddrs)
    (htbe : t.be = s.be) (htffi : t.ffi = s.ffi)
    (hheapLen : heapLen = (w3 + -1 * s.baseAddr).toNat / (width / 8))
    (hglobLe : globalsSize ≤ heapLen)
    (hmemaddrs : s.memaddrs = fun a =>
      StackRemove.addresses s.baseAddr (heapLen - globalsSize) a ∨ arena a)
    (arenaAligned : ∀ a, arena a → a.toNat % (width / 8) = 0)
    (htop : s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heapLen -
      BitVec.ofNat width (globalsSize * width / 8))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail) :
    let wst := WordToStack.Native.Initialization.makeInit ac k sst wcode worac
    let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    WordSemStateFiniteExact.semantics wst0 BvlToBvi.initGlobalsLocation =
      PanSemStateFiniteExact.semanticsDecls s start panCode := by
  classical
  intro wst wst0
  have good : goodDimindex width := hA.1
  have hd : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  -- init_code_thm's alignment of the heap base
  obtain ⟨t', v2, -, -, -, g2, -, -, a2, -⟩ := initCodeRunWithArena hA
  rw [h2] at g2; cases g2
  have hbase : s.baseAddr.toNat % (width / 8) = 0 :=
    (holByteAligned_iff_mod good _).1 a2
  -- the store
  obtain ⟨w2, g2', hcurr, hheapLW⟩ :=
    wordInitStoreWithArena (ac := ac) (k := k) (wcode := wcode) (worac := worac) hA hfmi
  rw [h2] at g2'; cases g2'
  rw [readPointers_s2_withArena hA h2 h3 h4] at hheapLW
  have hsnd := panToTargetHeapLimitSnd good maxHeap s.baseAddr w3 w4 a2 hlt hlo hhi hheap
    hheapLt halign
  rw [BitVec.add_comm (-1 * s.baseAddr), ← hheapLen] at hsnd
  -- the memory domain
  have hmd := wordInitMdomainWithArena (ac := ac) (k := k) (wcode := wcode) (worac := worac)
    s.baseAddr w3 w4 hA hfmi h2 h3 h4 hlo hhi hheap hheapLt halign
  rw [← hheapLen] at hmd
  have hmdP : (fun a => wst.mdomain a = true) = (fun a => StackRemove.addresses s.baseAddr heapLen a ∨ arena a) := by
    funext a; rw [hmd a, decide_eq_true_eq]
  obtain ⟨hffi, hbe, hsh, hmem⟩ := wordInitMemoryWithArena (ac := ac) (k := k)
    (wcode := wcode) (worac := worac) hA hfmi
  have hin : ∀ a, s.memaddrs a → wst.mdomain a = true := by
    intro a ha
    have : StackRemove.addresses s.baseAddr heapLen a ∨ arena a := by
      rw [hmemaddrs] at ha
      rcases ha with hh | ha
      · left
        rw [← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe]
        exact .inl hh
      · exact .inr ha
    exact (congrFun hmdP a).mpr this
  -- byte_aligned s.top_addr
  have htopAl : panGlobalsByteAlignedHOL s.topAddr := by
    apply panGlobalsByteAligned_of_mod good
    rw [htop, good_dimindex_div_mul width globalsSize good]
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, bytesInWord_toNat good]
    simp only [BitVec.toNat_ofNat]
    rcases good with h | h
    all_goals
      subst h
      simp at hbase ⊢
      omega
  refine panToTargetPanToWordStage ac k sst wcode worac s isa panCode start globalsSize
    (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit maxHeap
      (s.baseAddr, w3, w4)).2 * StackRemove.bytesInWord width)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstart hsize hparams ?_ hnodup htopAl halloc hcode hglobals hlocals
    heids heshapes good hfail
  · intro a ha
    exact (hmem a (hin a ha)).trans (htmem a ha)
  · intro a ha
    have hadr : StackRemove.addresses s.baseAddr heapLen a ∨ arena a := by
      exact (congrFun hmdP a).mp ha
    have aligned : a.toNat % (width / 8) = 0 := hadr.elim
      (addresses_mod good s.baseAddr hbase heapLen a) (arenaAligned a)
    obtain ⟨w, hw⟩ := htword a aligned
    exact ⟨w, (hmem a ha).trans hw⟩
  · show (fun a => wst.mdomain a = true) = _
    rw [hmdP, ← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe, hmemaddrs,
      htop]
    funext a
    apply propext
    exact or_assoc.trans (or_congr_right or_comm) |>.trans or_assoc.symm
  · show (fun a => wst.shMdomain a = true) = _
    rw [hsh]; exact htsh
  · exact hbe.trans htbe
  · exact hffi.trans htffi
  · simpa [wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hcurr
  · simpa [wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hheapLW
  · rw [htop, good_dimindex_div_mul width globalsSize good]
    have e1 : (2 : BitVec width) * (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit
        maxHeap (s.baseAddr, w3, w4)).2 * StackRemove.bytesInWord width) =
        StackRemove.bytesInWord width * BitVec.ofNat width heapLen := by
      rw [← hsnd, BitVec.ofNat_mul, BitVec.mul_comm (StackRemove.bytesInWord width),
        ← BitVec.mul_assoc]
      rfl
    have e2 : BitVec.ofNat width (globalsSize * (width / 8)) =
        panBytesInWord width * BitVec.ofNat width globalsSize := by
      rw [BitVec.ofNat_mul, BitVec.mul_comm]; rfl
    rw [e1, e2]

open Classical in
theorem panToWordStageLabWithArena {width : Nat} [NeZero width] {S Q C σ : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C σ}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (tAsm : AsmState width)
    (m : BitVec width → WordLocW width) (dm dm' sdm : BitVec width → Bool) (ms : S)
    (lcode : LabSem.LabProgHOL width)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (lorac : Nat → C × LabSem.LabProgHOL width)
    (bytes : List (BitVec 8))
    (ac : AsmConfigExact width) (k : Nat) (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize heapLen : Nat)
    (arena : BitVec width → Prop)
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle arena)
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset
      bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle arena = (sst, some x))
    (hmc : LabToTarget.mcConfOk mc)
    (hpm : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a))
    (hgi : goodInitState mc ms bytes cbspace tAsm m dm' sdm)
    (hsdm : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a)
    (hbase : mc.target.getReg ms mc.lenReg = s.baseAddr)
    (hlt : mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg)
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * maxHeap)
    (hheapLt : (StackRemove.bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true)
    (hbe : mc.target.config.bigEndian = s.be) (hffi : s.ffi = ffi)
    (hheapLen : heapLen = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8))
    (hglobLe : globalsSize ≤ heapLen)
    (hmemaddrs : s.memaddrs =
      (fun a => StackRemove.addresses (mc.target.getReg ms mc.lenReg)
        (heapLen - globalsSize) a ∨ arena a))
    (arenaAligned : ∀ a, arena a → a.toNat % (width / 8) = 0)
    (htop : s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heapLen -
      BitVec.ofNat width (globalsSize * width / 8))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail) :
    let wst := WordToStack.Native.Initialization.makeInit ac k sst wcode worac
    let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    WordSemStateFiniteExact.semantics wst0 BvlToBvi.initGlobalsLocation =
      PanSemStateFiniteExact.semanticsDecls s start panCode := by
  have good : goodDimindex width := hmc.1
  have hregs := hgi.1.2.2.2.1
  have hreg : ∀ r, asmRegOkExact r mc.target.config = true →
      tAsm.regs r = mc.target.getReg ms r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact (hregs r hr).symm
  have r2 := hreg _ hmc.2.2.2.1
  have r3 := hreg _ hmc.2.2.2.2.1
  have r4 := hreg _ hmc.2.2.2.2.2.1
  have hmword := hgi.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine panToWordFromInitWithArena ac k wcode worac s isa panCode start globalsSize heapLen
    (mc.target.getReg ms mc.ptr2Reg) (mc.target.getReg ms mc.len2Reg) hA hfmi
    ?_ ?_ ?_ (hbase ▸ hlt) ?_ ?_ ?_ hheapLt (hbase ▸ halign) ?_ ?_ ?_ ?_ ?_ hheapLen hglobLe
    (hbase ▸ hmemaddrs) arenaAligned htop hstart hsize hparams hnodup halloc hcode hglobals hlocals heids
    heshapes hfail
  · simp [LabToTarget.makeInit, r2, hbase]
  · simp [LabToTarget.makeInit, r3]
  · simp [LabToTarget.makeInit, r4]
  · rw [← hbase, BitVec.mul_comm]; exact hlo
  · rw [BitVec.mul_comm]; exact hhi
  · rw [← hbase, BitVec.add_comm, Nat.mul_comm]; exact hheap
  · intro a ha
    exact hpm a (decide_eq_true ha)
  · intro a ha
    obtain ⟨w, -, hw⟩ := hmword a
    rw [Compiler.Backend.LabToTarget.holByteAlign_of_aligned good a ha] at hw
    exact ⟨w, hw⟩
  · funext a
    have := congrFun hsdm a
    simp only [LabToTarget.makeInit] at this ⊢
    rw [← this, decide_eq_true_eq]
  · exact hbe
  · exact hffi.symm

#print axioms panToWordStageLabWithArena
#print axioms panToWordFromInitWithArena
end InitE.Op5
