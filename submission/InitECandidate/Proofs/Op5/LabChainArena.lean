import InitECandidate.Proofs.Op5.MachineAssumptionsArena
import InitECandidate.Proofs.Op5.WordToStackInitArena
import InitECandidate.Proofs.Op5.PanToWordArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabChain

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.LabToTarget
open Classical

theorem labSemanticsWithArena {width : Nat} [NeZero width] {S Q C σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltc : C)
    (panCode : List (DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat) (s : PanSemStateFiniteExact width σ) (start : MlS)
    (globalsSize heapLen : Nat) (byteArena : BitVec width → Bool) (arena : BitVec width → Prop)
    (wordArenaEq : ∀ a, arena a ↔ byteArena a = true ∧ holByteAligned a = true)
    (arenaHeap : ∀ a, arena a → ¬(t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
      a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)))
    (arenaBitmap : ∀ a, arena a → bitmapsDm a ≠ true)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, c'', fs, p))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    -- `pan_installed`'s components
    (hpm : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a))
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || byteArena w || bitmapsDm w) sdm)
    (hsdm : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a)
    (hpi :
      let regNames := c.stackConf.regNames
      let r1 := StackNames.findNameSpt regNames 2
      let r2 := StackNames.findNameSpt regNames 4
      let biw := StackRemove.bytesInWord width
      let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
      holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
      holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
      1024 * biw ≤ t.regs r2 - t.regs r1 ∧
      (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
      m (t.regs r1) = .word bitmapPtr ∧
      m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)))
    -- the top theorem's register, bound and memory hypotheses
    (hbase : mc.target.getReg ms mc.lenReg = s.baseAddr)
    (hlt : mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg)
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (StackRemove.bytesInWord width).toNat *
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true)
    (hbe : mc.target.config.bigEndian = s.be) (hffi : s.ffi = ffi)
    (hheapLen : heapLen = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8))
    (hglobLe : globalsSize ≤ heapLen)
    (hmemaddrs : s.memaddrs =
      (fun a => StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heapLen - globalsSize) a ∨ arena a))
    (htop : s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heapLen -
      BitVec.ofNat width (globalsSize * width / 8))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
    let labst := LabToTarget.makeInit (C := C) mc ffi t m
      (fun a => ((heapStackDm a || byteArena a) || bitmapsDm a) && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
    let sst := (fullMakeInitWithArena c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
      dataSp (fun _ => (ltc, [], [])) arena).1
    let wst := WordToStack.Native.Initialization.makeInit mc.target.config
      (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
      (sptFromAList wprog)
      (fun _ => ((bitmaps.length, ltc), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width)))))
    SemanticsPropsHOL.extendWithResourceLimitPrimeHOL
      (decide (WordSemStateFiniteExact.wordLangSafeForSpace wst BvlToBvi.initGlobalsLocation))
      (fun b => b = PanSemStateFiniteExact.semanticsDecls s start panCode)
      (LabSem.semantics labst) ∧
    WordSemStateFiniteExact.semantics wst BvlToBvi.initGlobalsLocation =
      PanSemStateFiniteExact.semanticsDecls s start panCode ∧
    ∃ x, fullMakeInitWithArena c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
      dataSp (fun _ => (ltc, [], [])) arena = (sst, some x) := by
  intro regNames r1 r2 heapStackDm sp maxHeap labst sst wst
  have good : goodDimindex width := hmc.1
  have hA := fullMakeInitAssumptionsWithArena (C := C) c mc ffi t m bitmapPtr bitmapsDm sdm ms
    comp bytes cbspace ltc panCode col wprog bitmaps c'' fs p dataSp byteArena arena wordArenaEq arenaHeap arenaBitmap
    hcfg hmc hinit hisa hwtw hwts
    hnodup hpi
  -- `full_make_init` succeeds
  rcases hfm : fullMakeInitWithArena c.stackConf c.dataConf
    maxHeap sp mc.target.config.addrOffset bitmaps p labst
    (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (ltc, [], [])) arena with ⟨sst', opt⟩
  have e : sst = sst' := by simp only [sst, hfm]
  obtain ⟨hopt, -⟩ := fullMakeInitWithArena_semantics (s := sst') (opt := opt) hfm hA
  obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp hopt
  let k := mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)
  let worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
    fun _ => ((bitmaps.length, ltc), [])
  -- word_to_stack and word_to_word premises (HOL lines 1606-1736)
  obtain ⟨hbmS, hcodeS⟩ := fullMakeInitWithArena_bitmaps_code c.stackConf c.dataConf maxHeap sp
    mc.target.config.addrOffset bitmaps p labst _ dataSp _ sst' x arena hfm
  have hinitS := initStateOkWithArena mc.target.config wprog bitmaps c'' fs p ltc c.stackConf
    c.dataConf maxHeap sp mc.target.config.addrOffset labst
    (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp sst' x good hcfg.2.2.2.1 hwts arena hfm
  rw [Nat.add_comm mc.target.config.avoidRegs.length 5] at hinitS
  obtain ⟨hgc, -, -, -⟩ := wordStateFactsWithArena mc.target.config k (sptFromAList wprog)
    worac c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset bitmaps p labst
    (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp _ sst' x arena hfm
  obtain ⟨hraise, hstore⟩ := panToTargetStubLocationsFree c.wordToWordConf mc.target.config
    panCode col wprog hisa hwtw
  have hconv := (BackendProof.compileToWordConventions2 c.wordToWordConf mc.target.config _ col
    wprog hwtw (fun _ _ => Or.inr hisa)).2.2
  have hchain := panToTargetWordChain mc.target.config c.wordToWordConf
    (panToWordCompileProgHOL mc.target.config.isa panCode) wprog col sst' worac
    BvlToBvi.initGlobalsLocation hwtw hgc
    (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl)
    (Flapjack.panToWordFirstCompileProgAllDistinctHOL _ panCode hnodup)
    (by rw [hwts, hcodeS]) hinitS hraise hstore (by rw [hwts, hbmS])
    (fun entry he => ⟨(hconv entry he).1, (hconv entry he).2.1⟩)
  -- the pan_to_word stage (HOL lines 2103-2284)
  have hstage := panToWordStageLabWithArena (C := C) mc ffi t m
    (fun w => (heapStackDm w || byteArena w) || bitmapsDm w)
    (fun w => (decide (t.regs r1 ≤ w ∧ w < t.regs r2) || byteArena w) || bitmapsDm w) sdm ms
    (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
    (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
      mc.target.config.addrOffset sp []))
    bytes mc.target.config k (sptFromAList wprog) worac s mc.target.config.isa panCode start
    globalsSize heapLen arena hA hfm hmc hpm hgi hsdm hbase hlt hlo hhi
    hheap hheapLt
    halign hbe hffi hheapLen hglobLe hmemaddrs
    (fun a ha => (holByteAligned_iff_mod good a).mp ((wordArenaEq a).mp ha).2) htop hstart hsize hparams hnodup halloc hcode
    hglobals hlocals heids heshapes hfail
  -- compose (HOL lines 1552-1560 and 1649-1736)
  have hstack := hchain (by rw [hstage]; exact hfail)
  rw [hstage] at hstack
  have key := (labStackLinkWithArena _ _ hfail ⟨hfm, hA⟩ hstack).2
  -- the word_to_word equality of the HOL proof (lines 1716-1736)
  have hww : WordSemStateFiniteExact.semantics
      { WordToStack.Native.Initialization.makeInit mc.target.config k sst' (sptFromAList wprog)
          worac with code := sptFromAList (panToWordCompileProgHOL mc.target.config.isa panCode) }
        BvlToBvi.initGlobalsLocation =
      WordSemStateFiniteExact.semantics
        (WordToStack.Native.Initialization.makeInit mc.target.config k sst' (sptFromAList wprog)
          worac) BvlToBvi.initGlobalsLocation :=
    WordToWord.word_to_word_compile_semantics c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) col wprog _ _ _
      ⟨hwtw, hgc, PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl,
        PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl,
        PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl,
        PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl,
        PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl,
        Flapjack.panToWordFirstCompileProgAllDistinctHOL _ panCode hnodup, rfl, rfl,
        by simp [WordToStack.Native.Initialization.makeInit]; rfl, rfl, rfl,
        by rw [hstage]; exact hfail⟩
  refine ⟨by simpa only [wst, e] using key, ?_, ⟨x, by rw [e]⟩⟩
  simp only [wst, e]
  rw [← hww]
  exact hstage

#print axioms labSemanticsWithArena
end InitE.Op5
