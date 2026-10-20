import InitECandidate.Runtime.SourceCostSourceTop
import InitECandidate.Runtime.SourceCostEntry
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The premises of the installed entry (`entry_loop_sharp_work`) for the
program `pan_to_crep` receives and its post-declaration state `T`: the pinned
`pan_to_crep` and `crep_to_loop` `state_rel_imp_semantics` premises, no inline
declarations, the `start` lookup and the replay-site certificate. -/
structure EntryPipeline {F : Type} (target : Compiler.Encoders.Asm.AsmArchitecture)
    (panCode : List (DeclHOL 64)) (start : MlS) (startProgram : CrepProgHOL 64)
    (T : PanSemStateFiniteExact 64 F) (tc : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F) :
    Prop where
  state : panToCrepStateRelFiniteExact T tc
  distinct : ((functionsHOL panCode).map Prod.fst).Nodup
  sourceCode : T.code = HolFiniteMapExact.empty.updateList (functionsHOL panCode).reverse
  noInline : (functionsHOL (panCode.filter inlinableHOL)).map Prod.fst = []
  emptyLocals : T.locals = HolFiniteMapExact.empty
  localised : ∀ entry ∈ functionsHOL panCode, localisedProgHOL entry.2.2.1 = true
  eidsSize : sizeOfEidsHOL panCode < 2 ^ 64
  eidsDomain : ∀ key, (T.eshapes.lookup key).isSome =
    ((getEidsFromDeclsHOL panCode).lookup key).isSome
  memaddrs : tc.memaddrs = (fun address => u.mdomain address = true)
  be : tc.be = u.be
  shMemaddrs : tc.shMemaddrs = (fun address => u.shMdomain address = true)
  ffi : tc.ffi = u.ffi
  baseAddr : tc.baseAddr = u.baseAddr
  topAddr : tc.topAddr = u.topAddr
  memory : crepToLoopMemRelHOLExact tc.memory u.memory tc.memaddrs
  globals : crepToLoopGlobalsRelHOLExact tc.globals u.globals
  crepDistinct : ((compileProgDeclsHOLW panCode).map Prod.fst).Nodup
  crepCode : tc.code = alistToFmapCodeExact (compileProgDeclsHOLW panCode)
  loopCode : u.code = sptFromAList (compileProgHOLExact target (compileProgDeclsHOLW panCode))
  crepLocals : tc.locals = HolFiniteMapExact.empty
  startLookup : holAlookup (compileProgDeclsHOLW panCode) start = some ([], startProgram)
  sites : ∀ entry ∈ functionsHOL panCode, sharpSitesProg sharpReplayBound entry.2.2.1 = true

/-- End-to-end whole-program transfer: the original entry run of the original
declarations (post-declaration state, any clock) is matched by the installed
Loop entry, whose executed Loop work is at most the sharp score of the original
canonical events plus the one-time `pan_globals` initialiser cost. The pipeline
premises are stated for the actual post-declaration state of the compiled
program. -/
theorem source_loop_top {F : Type} (decls : List (DeclHOL 64)) (start : MlS)
    (s0 t : PanSemStateFiniteExact 64 F) (clock : Nat)
    (mgs : BitVec 64) (freeAddrs : BitVec 64 → Prop)
    (tmem : BitVec 64 → HolWordLab 64) (tlocals : HolFiniteMapExact MlS (ValueHOL 64))
    (h : ((functionsHOL (panSimpDeclsHOL decls)).map Prod.fst).Nodup ∧
      t = { ({ s0 with clock := clock } : PanSemStateFiniteExact 64 F) with
        topAddr := s0.topAddr + mgs
        memaddrs := fun address => s0.memaddrs address ∨ freeAddrs address
        memory := tmem
        locals := tlocals } ∧
      s0.code = HolFiniteMapExact.empty ∧
      s0.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL s0.topAddr ∧
      goodDimindex 64 ∧
      mgs = panBytesInWord 64 *
        BitVec.ofNat 64 ((decShapesHOL (panSimpDeclsHOL decls)).map sizeOfShapeHOL).sum ∧
      freeAddrs = Flapjack.Compiler.Backend.StackRemove.addresses s0.topAddr
        ((decShapesHOL (panSimpDeclsHOL decls)).map sizeOfShapeHOL).sum ∧
      (∀ address, s0.memaddrs address → ¬ freeAddrs address) ∧
      (∀ address, s0.memaddrs address → s0.memory address = tmem address) ∧
      ¬ s0.memaddrs (s0.topAddr + mgs) ∧
      (panBytesInWord 64).toNat * ((decShapesHOL (panSimpDeclsHOL decls)).map sizeOfShapeHOL).sum <
        2 ^ 64 ∧
      (∀ d ∈ panSimpDeclsHOL decls,
        isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true))
    (structFree : Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL decls) =
      panSimpDeclsHOL decls)
    (body : ProgHOL 64) (rshape : ShapeHOL)
    (hstartLookup : (functionsHOL (panSimpDeclsHOL decls)).lookup start = some ([], body, rshape))
    (ready : ∀ entry ∈ functionsHOL (panSimpDeclsHOL decls),
      globalsReadyProg entry.2.2.1 = true ∧ globalsTemp ∉ entry.2.1.map Prod.fst)
    (constGlobals : constGlobalDecls ((panSimpDeclsHOL decls).filter isDeclHOL) = true)
    (target : Compiler.Encoders.Asm.AsmArchitecture) (startProgram : CrepProgHOL 64)
    (tc : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F)
    (pipeline : ∀ T, @evaluateDeclsHOLFinite 64 F _ { t with structs := [] }
        (fun a => Classical.propDecidable (t.memaddrs a))
        (compileTopExactHOL (panSimpDeclsHOL decls) start) = some T →
      EntryPipeline target (compileTopExactHOL (panSimpDeclsHOL decls) start) start startProgram T tc u)
    {s1 : PanSemStateFiniteExact 64 F}
    (hs1 : @evaluateDeclsHOLFinite 64 F _ { s0 with structs := [] }
      (fun a => Classical.propDecidable (s0.memaddrs a)) decls = some s1)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F} {ev : List WorkEvent}
    (run : StatementRun { s1 with clock := clock } (.call none start []) r post ev)
    (ok : r ≠ some .error) :
    ∃ T, @evaluateDeclsHOLFinite 64 F _ { t with structs := [] }
        (fun a => Classical.propDecidable (t.memaddrs a))
        (compileTopExactHOL (panSimpDeclsHOL decls) start) = some T ∧
      ∃ extra wl,
        LoopWork { u with clock := T.clock + 1 + extra }
          (compileHOLExact (entryLoopContext target (compileTopExactHOL (panSimpDeclsHOL decls) start)) .ln
            (crepSimpProgHOL (compileProgExactHOLW
              (entryPanContext (compileTopExactHOL (panSimpDeclsHOL decls) start)) (.call none start []))))
          (evaluate
            (compileHOLExact (entryLoopContext target (compileTopExactHOL (panSimpDeclsHOL decls) start)) .ln
              (crepSimpProgHOL (compileProgExactHOLW
                (entryPanContext (compileTopExactHOL (panSimpDeclsHOL decls) start)) (.call none start []))))
            { u with clock := T.clock + 1 + extra }) wl ∧
        wl ≤ sharpScore ev +
          globalsTopInit rshape ((panSimpDeclsHOL decls).filter isDeclHOL).length (callPayloadWords r) ∧
        LoopRunRel (entryLoopContext target (compileTopExactHOL (panSimpDeclsHOL decls) start)) .ln
          (evalCrepSemHOLProgExact (crepSimpMapcsHOL { tc with clock := T.clock + 1 })
            (crepSimpProgHOL (compileProgExactHOLW
              (entryPanContext (compileTopExactHOL (panSimpDeclsHOL decls) start)) (.call none start []))))
          (evaluate
            (compileHOLExact (entryLoopContext target (compileTopExactHOL (panSimpDeclsHOL decls) start)) .ln
              (crepSimpProgHOL (compileProgExactHOLW
                (entryPanContext (compileTopExactHOL (panSimpDeclsHOL decls) start)) (.call none start []))))
            { u with clock := T.clock + 1 + extra }) := by
  obtain ⟨T, hT, r', post', ev', run', ok', le'⟩ := source_top_entry decls start s0 t clock mgs freeAddrs
    tmem tlocals h structFree body rshape hstartLookup ready constGlobals hs1 run ok
  rw [structFree] at hT
  have p := pipeline T hT
  obtain ⟨extra, wl, work, bound, runRel⟩ := entry_loop_sharp_work target
    (compileTopExactHOL (panSimpDeclsHOL decls) start) start startProgram T tc u (T.clock + 1)
    p.state p.distinct p.sourceCode p.noInline p.emptyLocals p.localised p.eidsSize p.eidsDomain
    p.memaddrs p.be p.shMemaddrs p.ffi p.baseAddr p.topAddr p.memory p.globals p.crepDistinct
    p.crepCode p.loopCode p.crepLocals p.startLookup p.sites run' (by rw [ok']; exact ok)
  exact ⟨T, hT, extra, wl, work, by omega, runRel⟩

#print axioms source_loop_top
end InitECandidate.Runtime.FineCost
