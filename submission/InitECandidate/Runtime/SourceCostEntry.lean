import InitECandidate.Runtime.SourceCostSharpSource
import InitECandidate.Runtime.SourceCostCrepInlineId
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemanticsTop
import Flapjack.Pancake.CrepToLoop.Proofs.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
variable {fn : Flapjack.Pancake.PanLang.MlS}

/-! Installed whole-program entry: the program `pan_to_crep` receives, its
installed Crep code, and the installed Loop code (`crep_to_loop$compile_prog`
of the `crep_arith`-simplified bodies). The initial relations are those of the
pinned `state_rel_imp_semantics` theorems of both passes. -/

/-- The `pan_to_crep` entry context of the pinned top-level theorem. -/
def entryPanContext (panCode : List (DeclHOL 64)) : PanToCrepContextExact 64 :=
  mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL panCode)) 0
    (getEidsFromDeclsHOL panCode)

/-- The `crep_to_loop` entry context of the pinned top-level theorem. -/
noncomputable def entryLoopContext (target : Compiler.Encoders.Asm.AsmArchitecture) (panCode : List (DeclHOL 64)) :
    CrepToLoopContextExact :=
  mkCtxtExact target HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)) 0

theorem entry_source_crep_rel {F : Type} (panCode : List (DeclHOL 64))
    (s : PanSemStateFiniteExact 64 F) (t : CrepSemHOLState 64 F) (clock : Nat)
    (state : panToCrepStateRelFiniteExact s t)
    (distinct : ((functionsHOL panCode).map Prod.fst).Nodup)
    (sourceCode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL panCode).reverse)
    (targetCode : t.code = HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW panCode).reverse)
    (noInline : (functionsHOL (panCode.filter inlinableHOL)).map Prod.fst = [])
    (emptyLocals : s.locals = HolFiniteMapExact.empty)
    (localised : ∀ entry ∈ functionsHOL panCode, localisedProgHOL entry.2.2.1 = true)
    (eidsSize : sizeOfEidsHOL panCode < 2 ^ 64)
    (eidsDomain : ∀ key, (s.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome) :
    SourceCrepRel (entryPanContext panCode) { s with clock := clock } { t with clock := clock } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10⟩ := state
    exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8, h9, h10⟩
  · show codeRelExactHOLW (entryPanContext panCode) s.code t.code
    rw [sourceCode, targetCode, compileProgDecls_noInline panCode noInline]
    exact mkCtxtCodeImpCodeRelExactHOLW panCode distinct localised
  · exact getEidsImpExcpRelExact s.eshapes panCode ⟨eidsSize, eidsDomain⟩
  · show panToCrepLocalsRelFiniteExact (entryPanContext panCode) s.locals t.locals
    rw [emptyLocals]
    exact mkCtxtImpLocalsRelExact _ _ _

theorem entry_crep_loop_rel {F : Type} (target : Compiler.Encoders.Asm.AsmArchitecture) (panCode : List (DeclHOL 64))
    (start : MlS) (startProgram : CrepProgHOL 64)
    (t : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F) (clock : Nat)
    (memaddrs : t.memaddrs = (fun address => u.mdomain address = true))
    (be : t.be = u.be) (shMemaddrs : t.shMemaddrs = (fun address => u.shMdomain address = true))
    (ffi : t.ffi = u.ffi) (baseAddr : t.baseAddr = u.baseAddr) (topAddr : t.topAddr = u.topAddr)
    (memory : crepToLoopMemRelHOLExact t.memory u.memory t.memaddrs)
    (globals : crepToLoopGlobalsRelHOLExact t.globals u.globals)
    (distinct : ((compileProgDeclsHOLW panCode).map Prod.fst).Nodup)
    (crepCode : t.code = alistToFmapCodeExact (compileProgDeclsHOLW panCode))
    (loopCode : u.code = sptFromAList (compileProgHOLExact target (compileProgDeclsHOLW panCode)))
    (emptyLocals : t.locals = HolFiniteMapExact.empty)
    (startLookup : holAlookup (compileProgDeclsHOLW panCode) start = some ([], startProgram)) :
    CrepLoopRel (entryLoopContext target panCode) .ln (crepSimpMapcsHOL { t with clock := clock })
      { u with clock := clock } := by
  have code2 := mkCtxtCodeImpCodeRel2Exact target (compileProgDeclsHOLW panCode) start startProgram
    ⟨distinct, startLookup⟩
  rw [← crepCode, ← loopCode] at code2
  refine ⟨⟨memaddrs, shMemaddrs, rfl, be, ffi, baseAddr, topAddr⟩, memory, globals, code2, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y n m hx
    simp [entryLoopContext, mkCtxtExact, HolFiniteMapExact.empty] at hx
  · intro v m hv
    simp [entryLoopContext, mkCtxtExact, HolFiniteMapExact.empty] at hv
  · intro n hn
    simp [sptMem, sptDomain, sptLookup] at hn
  · intro vname value found
    simp [crepSimpMapcsHOL, emptyLocals, HolFiniteMapExact.empty] at found

#print axioms entry_source_crep_rel
#print axioms entry_crep_loop_rel
theorem entry_code_mem {β : Type} {entries : List (MlS × β)} {key : MlS} {value : β}
    (found : (HolFiniteMapExact.empty.updateList entries.reverse).lookup key = some value) :
    (key, value) ∈ entries := by
  rw [HolFiniteMapExact.lookup_updateList, PanGlobalsCompileTopSemanticsDecls.fupdateListLookup,
    List.reverse_reverse] at found
  split at found
  · rename_i v hv
    cases found
    exact PanGlobalsCompileTopSemanticsDecls.lookupMem entries key _ hv
  · simp [HolFiniteMapExact.empty] at found

/-- Installed entry at exact Loop prices: the source run of `start` from the
installed initial state (the state of the pinned `pan_to_crep`
`state_rel_imp_semantics`, at clock `clock`) is matched by the installed Loop
entry, whose executed work is at most the sharp score of the same canonical
source events. The program is the one `pan_to_crep` receives. -/
theorem entry_loop_sharp_work {F : Type} (target : Compiler.Encoders.Asm.AsmArchitecture)
    (panCode : List (DeclHOL 64)) (start : MlS) (startProgram : CrepProgHOL 64)
    (s : PanSemStateFiniteExact 64 F) (t : CrepSemHOLState 64 F) (u : LoopSemStateFiniteExact 64 F)
    (clock : Nat)
    (state : panToCrepStateRelFiniteExact s t)
    (distinct : ((functionsHOL panCode).map Prod.fst).Nodup)
    (sourceCode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL panCode).reverse)
    (noInline : (functionsHOL (panCode.filter inlinableHOL)).map Prod.fst = [])
    (emptyLocals : s.locals = HolFiniteMapExact.empty)
    (localised : ∀ entry ∈ functionsHOL panCode, localisedProgHOL entry.2.2.1 = true)
    (eidsSize : sizeOfEidsHOL panCode < 2 ^ 64)
    (eidsDomain : ∀ key, (s.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome)
    (memaddrs : t.memaddrs = (fun address => u.mdomain address = true))
    (be : t.be = u.be) (shMemaddrs : t.shMemaddrs = (fun address => u.shMdomain address = true))
    (ffi : t.ffi = u.ffi) (baseAddr : t.baseAddr = u.baseAddr) (topAddr : t.topAddr = u.topAddr)
    (memory : crepToLoopMemRelHOLExact t.memory u.memory t.memaddrs)
    (globals : crepToLoopGlobalsRelHOLExact t.globals u.globals)
    (crepDistinct : ((compileProgDeclsHOLW panCode).map Prod.fst).Nodup)
    (crepCode : t.code = alistToFmapCodeExact (compileProgDeclsHOLW panCode))
    (loopCode : u.code = sptFromAList (compileProgHOLExact target (compileProgDeclsHOLW panCode)))
    (crepLocals : t.locals = HolFiniteMapExact.empty)
    (startLookup : holAlookup (compileProgDeclsHOLW panCode) start = some ([], startProgram))
    (sites : ∀ entry ∈ functionsHOL panCode, sharpSitesProg sharpReplayBound entry.2.2.1 = true)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn { s with clock := clock } (.call none start []) r post events)
    (ok : r ≠ some .error) :
    let program := crepSimpProgHOL (compileProgExactHOLW (entryPanContext panCode) (.call none start []))
    let loopProgram := compileHOLExact (entryLoopContext target panCode) .ln program
    ∃ extra wl,
      LoopWork { u with clock := clock + extra } loopProgram
        (evaluate loopProgram { u with clock := clock + extra }) wl ∧
      wl ≤ sharpScore events ∧
      LoopRunRel (entryLoopContext target panCode) .ln
        (evalCrepSemHOLProgExact (crepSimpMapcsHOL { t with clock := clock }) program)
        (evaluate loopProgram { u with clock := clock + extra }) ∧
      (evaluate loopProgram { u with clock := clock + extra }).1 ≠ some .error := by
  have targetCode : t.code = HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW panCode).reverse := by
    rw [crepCode]; rfl
  have rel := entry_source_crep_rel panCode s t clock state distinct sourceCode targetCode noInline
    emptyLocals localised eidsSize eidsDomain
  have loopRel := entry_crep_loop_rel target panCode start startProgram t u clock memaddrs be shMemaddrs
    ffi baseAddr topAddr memory globals crepDistinct crepCode loopCode crepLocals startLookup
  have codeChecked : ∀ function shapes body returnShape,
      ({ s with clock := clock } : PanSemStateFiniteExact 64 F).code.lookup function =
        some (shapes, body, returnShape) → sharpSitesProg sharpReplayBound body = true := by
    intro function shapes body returnShape found
    rw [show ({ s with clock := clock } : PanSemStateFiniteExact 64 F).code = s.code from rfl,
      sourceCode] at found
    exact sites _ (entry_code_mem found)
  obtain ⟨extra, wl, work, bound, runRel, loopOk⟩ := source_loop_sharp_work run { t with clock := clock }
    (entryPanContext panCode) ok rel (by simp [localisedProgHOL, everyExpListHOL])
    (by simp [sharpSitesProg, sharpSitesList]) codeChecked { u with clock := clock }
    (entryLoopContext target panCode) .ln loopRel
  exact ⟨extra, wl, work, bound, runRel, loopOk⟩

#print axioms entry_loop_sharp_work
end InitECandidate.Runtime.FineCost
