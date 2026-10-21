import InitECandidate.Runtime.GuestCostSourceWord
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open InitE InitECandidate.Proofs.FrontendStages

/-! The pinned Word entry. `pan_to_word`'s `state_rel_imp_semantics` runs
`Call NONE (SOME firstLoopName) [0] NONE` from the Word target state. That
call is `loop_to_word`'s compilation of the installed Loop entry, and the
target state is related to the installed Loop state by the pinned argument. -/

/-- The installed Loop entry of a program whose `start` is the first Loop
function. -/
theorem entry_loop_program (panCode : List (DeclHOL 64)) (start : MlS) (arch : AsmArchitecture)
    (hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)).lookup start = some (firstLoopName, 0)) :
    compileHOLExact (entryLoopContext arch panCode) .ln
      (crepSimpProgHOL (compileProgExactHOLW (entryPanContext panCode) (.call none start []))) =
      .seq (.call none (some firstLoopName) [] none) .skip := by
  simp [compileProgExactHOLW, compileCallNoReturnExactHOLW, compileExpExactHOLWList, crepSimpProgHOL,
    compileHOLExact, compileExpsHOLExact, genTemps, loopNestedSeqHOL, findLabExact, entryLoopContext,
    mkCtxtExact, hmf]

/-- The pinned Loop-to-Word initial relation, at any common clock. -/
theorem entry_loop_word_rel {C F : Type} (G : PanSemStateFiniteExact 64 F) (panCode : List (DeclHOL 64))
    (arch : AsmArchitecture) (target : WordSemStateFiniteExact 64 C F) (heapLen : BitVec 64)
    (hdm : ∀ a, target.mdomain a = true ↔ G.memaddrs a)
    (hsh : ∀ a, target.shMdomain a = true ↔ G.shMemaddrs a)
    (hbe : target.be = G.be) (hffi : target.ffi = G.ffi)
    (hcurr : target.store.lookup .currHeap = some (.word G.baseAddr))
    (hheaplen : target.store.lookup .heapLength = some (.word heapLen))
    (htop : G.topAddr = G.baseAddr + (2 : BitVec 64) * heapLen)
    (hcode : target.code = sptFromAList (loopToWordCompileProgHOL (compileProgHOLExact arch (compileProgDeclsHOLW panCode))))
    (c : Nat) :
    loopToWordStateRelHOLExact
      { loopStateHOL (crepStateHOL G panCode G.memory) arch (compileProgDeclsHOLW panCode) target.clock
          target.memory with clock := c }
      { target with clock := c } := by
  classical
  have hparamsLoop := crepToLoopCompileProgDistinctParamsHOLExact (compileProgDeclsHOLW panCode) arch
    (compileProgDeclsHOLW_params_nodup panCode)
  refine ⟨heapLen, rfl, ?_, ?_, rfl, hbe, hffi, hcurr, hheaplen, htop, ?_, ?_⟩
  · funext a; apply Bool.eq_iff_iff.mpr; simp [loopStateHOL, crepStateHOL, hdm a]; exact decide_eq_true_iff.symm
  · funext a; apply Bool.eq_iff_iff.mpr; simp [loopStateHOL, crepStateHOL, hsh a]; exact decide_eq_true_iff.symm
  · intro name value hl
    simp [loopStateHOL, HolFiniteMapExact.empty] at hl
  · intro name params body hl
    constructor
    · show sptLookup name target.code = _
      rw [hcode]
      exact loopToWordLookupProgSomeLookupCompileProg _ name params body hl
    · apply of_decide_eq_true
      apply (List.all_eq_true.mp hparamsLoop) (name, params, body)
      apply sptAListLookup_mem name (compileProgHOLExact arch (compileProgDeclsHOLW panCode)) (params, body)
      simpa only [loopStateHOL, sptLookup_sptFromAList] using hl

/-- Guest source → pinned Word entry: the `pan_to_word` entry call
`Call NONE (SOME firstLoopName) [0] NONE`, from the Word target state of the
pinned `state_rel_imp_semantics` at a clock extension, executes Word work at
most `sharpScore ev + 20127` under `loopWordPrice`. Every target premise is a
premise of the pinned theorem. -/
theorem guest_word_entry (input : Guest.InputBlob) {C : Type}
    (target : WordSemStateFiniteExact 64 C Guest.HostMemory) (arch : AsmArchitecture) (clock : Nat)
    (heapLen : BitVec 64)
    (hmem : ∀ address, (sourceInitialState input).memaddrs address →
      target.memory address = wlabWlocExact ((sourceInitialState input).memory address))
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (hmdomain : (fun address => target.mdomain address = true) =
      (fun address => (sourceInitialState input).memaddrs address ∨
        Compiler.Backend.StackRemove.addresses (sourceInitialState input).topAddr guestGlobalsSize address))
    (hshdomain : (fun address => target.shMdomain address = true) = (sourceInitialState input).shMemaddrs)
    (hbe : target.be = (sourceInitialState input).be) (hffi : target.ffi = (sourceInitialState input).ffi)
    (hcurrheap : target.store.lookup .currHeap = some (.word (sourceInitialState input).baseAddr))
    (hheaplen : target.store.lookup .heapLength = some (.word heapLen))
    (htop : (sourceInitialState input).topAddr = (sourceInitialState input).baseAddr + (2 : BitVec 64) * heapLen -
      panBytesInWord 64 * BitVec.ofNat 64 guestGlobalsSize)
    (htcode : target.code = sptFromAList (panToWordCompileProgHOL arch InitE.sourceDeclarations))
    (hloc0 : sptLookup 0 target.locals = some (WordLocW.loc 1 0))
    {s1 : PanSemStateFiniteExact 64 Guest.HostMemory}
    (hs1 : @evaluateDeclsHOLFinite 64 Guest.HostMemory _ { sourceInitialState input with structs := [] }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      (Guest.guestAst.map declToHOL) = some s1)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {ev : List WorkEvent}
    (run : StatementRun { s1 with clock := clock } (.call none (Flapjack.Basis.Pure.MlString.ofString "main") [])
      r post ev)
    (ok : r ≠ some .error) :
    ∃ entryClock,
      wordExecutionCost loopWordPrice (.call none (some firstLoopName) [0] none)
        { target with clock := entryClock } ≤ sharpScore ev + 20127 := by
  classical
  obtain ⟨T, -, extra, word⟩ := guest_source_word input C target arch clock hmem hnolabels hmdomain hs1 run ok
  obtain ⟨body, rshape, hmain, -⟩ := guest_main_lookup
  have hmf := flookupMakeFuncsMainHOL (panSimpDeclsHOL InitE.sourceDeclarations)
    (Flapjack.Basis.Pure.MlString.ofString "main") body rshape hmain
  have hprog := entry_loop_program _ _ arch hmf
  have structFree := compileTop_structFree _ guest_simplified_struct_free
  have hcode : target.code = sptFromAList (loopToWordCompileProgHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL (panSimpDeclsHOL InitE.sourceDeclarations)
        (Flapjack.Basis.Pure.MlString.ofString "main"))))) := by
    rw [htcode]
    simp only [panToWordCompileProgHOL, loopToWordCompileHOL]
    rw [structFree]
  have rel := entry_loop_word_rel
    (initialGlobalState (sourceInitialState input) target guestGlobalsSize clock)
    (compileTopExactHOL (panSimpDeclsHOL InitE.sourceDeclarations) (Flapjack.Basis.Pure.MlString.ofString "main"))
    arch target heapLen
    (fun a => by
      have := congrFun hmdomain a
      simp only [initialGlobalState] at this ⊢
      exact Iff.of_eq this)
    (fun a => by
      have := congrFun hshdomain a
      simp only [initialGlobalState] at this ⊢
      exact Iff.of_eq this)
    hbe hffi hcurrheap hheaplen
    (by
      change (sourceInitialState input).topAddr + panBytesInWord 64 * BitVec.ofNat 64 guestGlobalsSize = _
      rw [htop]
      exact BitVec.sub_add_cancel _ _)
    hcode (T.clock + 1 + extra)
  have cost := word { target with clock := T.clock + 1 + extra } Spt.ln (WordLocW.loc 1 0) (0, 0) rel
    (by refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all [sptMem, sptDomain, sptLookup, loopStateHOL])
    hloc0 (Or.inr rfl) (by simp [wordSemIsWordLoc])
    (by intro k hk; rw [hprog] at hk; simp [accVarsHOL, sptMem, sptDomain, sptLookup] at hk)
  refine ⟨T.clock + 1 + extra, Nat.le_trans ?_ cost⟩
  rw [hprog]
  simp only [LoopToWord.compHOL, List.map_nil]
  rw [wordExecutionCost_seq]
  simp only [loopWordPrice]
  omega

#print axioms guest_word_entry
#print axioms entry_loop_program
#print axioms entry_loop_word_rel
end InitECandidate.Runtime.FineCost
