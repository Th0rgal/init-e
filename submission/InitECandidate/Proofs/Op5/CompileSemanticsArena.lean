import InitECandidate.Proofs.Op5.LabResourceArena
import InitECandidate.Proofs.Op5.MachineLabArena
import InitECandidate.Proofs.Op5.PanInstallation
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTop

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Pancake.Proofs.PanToTarget
open Classical

def compileSemanticsWithArenaStatement {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS)
    (byteArena : BitVec width → Bool) (arena : BitVec width → Prop) : Prop :=
  let getReg := mc.target.getReg ms
  (∀ a, arena a ↔ byteArena a = true ∧ holByteAligned a = true) ∧
  (∀ a, arena a → ¬(getReg mc.lenReg ≤ a ∧ a < getReg mc.len2Reg)) ∧
  compileProgMax c mc pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
  pancakeGoodCodeHOL pan_code = true ∧
  distinctParamsHOL (functionsHOL pan_code) ∧
  ((functionsHOL pan_code).map Prod.fst).Nodup ∧
  s.code = HolFiniteMapExact.empty ∧
  s.locals = HolFiniteMapExact.empty ∧
  s.globals = HolFiniteMapExact.empty ∧
  sizeOfEidsHOL pan_code < 2 ^ width ∧
  s.eshapes = HolFiniteMapExact.empty ∧
  backendConfigOk mc.target.config c ∧ LabToTarget.mcConfOk mc ∧
  mcInitOk mc.target.config c mc ∧ mc.target.config.isa ≠ .ag32 ∧
  (0 : BitVec width) < getReg mc.lenReg ∧
  globals_size =
    (let dec_shs := decShapesHOL pan_code
     let struct_ctxt := decsStcnamesHOLExact (width := width) [] pan_code
     (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
  getReg mc.lenReg < getReg mc.ptr2Reg ∧
  getReg mc.lenReg = s.baseAddr ∧
  globalsAllocatableHOL s pan_code ∧
  heap_len = (getReg mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8) ∧
  s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heap_len -
    BitVec.ofNat width (globals_size * width / 8) ∧
  globals_size ≤ heap_len ∧
  s.memaddrs = (fun a => StackRemove.addresses (getReg mc.lenReg) (heap_len - globals_size) a ∨ arena a) ∧
  holAligned (wordShiftAmount width + 1) (getReg mc.ptr2Reg + -1 * getReg mc.lenReg) = true ∧
  adj_ptr2 = getReg mc.lenReg +
    StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
  adj_ptr4 = getReg mc.len2Reg -
    StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
  adj_ptr2 ≤ getReg mc.ptr2Reg ∧
  getReg mc.ptr2Reg ≤ adj_ptr4 ∧
  (getReg mc.ptr2Reg + -1 * getReg mc.lenReg).toNat ≤
    (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) ∧
  (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
    2 ^ width ∧
  s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
  (match c.labConf.ffiNames with
    | none => True
    | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) ∧
  panInstalledWithArena bytes cbspace bitmaps data_sp c'.labConf.ffiNames
    (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms
    (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs byteArena ∧
  start = ofString "main" ∧
  PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
  ∀ b, machineSemHOL mc ffi ms b →
    extendWithResourceLimitPrimeHOL
      (optionLt stack_max (some (readLimits mc.target.config c mc ms).1))
      (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b


theorem compileSemanticsWithArena {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS)
    (byteArena : BitVec width → Bool) (arena : BitVec width → Prop) :
    compileSemanticsWithArenaStatement c mc pan_code bytes bitmaps c' stack_max s ffi ms
      globals_size heap_len adj_ptr2 adj_ptr4 cbspace data_sp start byteArena arena := by
  rintro ⟨wordArenaEq, arenaHeapMachine, hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hcfg, hmc,
    hinit, hisa, -, hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign,
    rfl, rfl, hlo, hhi, hheap, hheapLt, hffi, hbe, hffiOk, hinst, hstart, hfail⟩ b hb
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, rfl, hmax⟩ :=
    compileProgMax_some c mc pan_code bytes bitmaps _ stack_max hcomp
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, hpm, hgi, hsdm, a1, a2, a3, hle, hbig, hdisj, m0, m1,
    m2, m3, m4, hstar, hffiN, hmmio⟩ := hinst
  have arenaBitmap : ∀ a, arena a → bitmapsDm a ≠ true := by
    intro a ha hb
    exact hdisj a ⟨Or.inr ((wordArenaEq a).mp ha).1, hb⟩
  have arenaHeap : ∀ a, arena a →
      ¬(t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
        a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) := by
    intro a ha
    have r2 : t.regs mc.lenReg = mc.target.getReg ms mc.lenReg := by
      have hr := hmc.2.2.2.1
      simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
      exact (hgi.1.2.2.2.1 _ hr).symm
    have r4 : t.regs mc.len2Reg = mc.target.getReg ms mc.len2Reg := by
      have hr := hmc.2.2.2.2.2.1
      simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
      exact (hgi.1.2.2.2.1 _ hr).symm
    rw [hinit.2.2.2.1, hinit.2.1, r2, r4]
    exact arenaHeapMachine a ha
  -- `pan_to_word_every_inst_ok_less` (stage .20), from `pancake_good_code`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hao, -, hbo, -⟩ := id hcfg
  have hz := good_dimindex_0w_8w hmc.1
  have hevery := PanToWord.panToWordEveryInstOkLess mc.target.config pan_code _ rfl
    (hbo 0 ⟨hz.2, hz.1⟩) hao hgood
  -- the machine-to-lab stage (`lab_to_target` `semantics_compile`)
  have hA4 := machineLabWithArena c mc ffi t m byteArena bitmapsDm sdm ms bytes cbspace pan_code col
    wprog bitmaps wconf fs p ltconf hcfg hmc hisa hwtw hwts hlab hnodup hffiOk hgi hffiN hmmio
    hevery
  -- the lab-state chain with the resource-limit stage
  have hres := labSemanticsResourceWithArena (C := LabToTarget.Config) c mc ffi t m bitmapPtr
    bitmapsDm sdm ms (LabToTarget.compile mc.target.config) bytes cbspace ltconf pan_code col wprog
    bitmaps wconf fs p data_sp s start globals_size heap_len stack_max byteArena arena
    wordArenaEq arenaHeap arenaBitmap hcfg hmc hinit hisa hwtw
    hwts hmax hnodup (fun a h => hpm a (of_decide_eq_true h)) hgi
    (by
      funext a
      rw [hsdm]
      simp only [Bool.decide_and, Bool.decide_eq_true])
    ⟨a1, a2, a3, hle, hbig, (fun a h => hdisj a ⟨Or.inl h.1, h.2⟩),
      m0, m1, m2, m3, m4, hstar⟩ hbase
    hlt hlo hhi hheap hheapLt halign hbe hffi hheapLen hglobLe hmemaddrs htop hstart hsize hparams
    halloc hcode hglobals hlocals heids heshapes hfail
  have hlabne := extendPrime_singleton_ne_fail _ _ _ hres hfail
  have hb' := hA4 (fun h => hlabne h.symm) b hb
  simp only [extendWithResourceLimitPrimeHOL, if_true] at hb'
  rw [hb']
  exact hres

#print axioms compileSemanticsWithArena
end InitE.Op5
