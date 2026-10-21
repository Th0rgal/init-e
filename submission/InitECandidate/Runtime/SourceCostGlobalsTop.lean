import InitECandidate.Runtime.SourceCostGlobalsTopBase
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.PanGlobalsCompileTopSemanticsDecls Flapjack.PanGlobalsCompileDecsStructural
open Flapjack.PanGlobalsDeclListExact

/-! Whole-program `pan_globals` entry. `compile_top` installs a new entry with
the original entry's name: it runs the global initialisers and then calls the
original entry under a fresh name. Following the pinned
`compile_top_semantics_decls` proof at run level, the compiled entry run costs
at most the source entry run plus a one-time initialiser cost. -/

/-- The one-time cost of the generated entry: its own call (call base, return
slots, exit with at most an exception's re-raise check and the payload copy)
and the constant initialiser stores. -/
def globalsTopInit (returnShape : ShapeHOL) (globalCount payload : Nat) : Nat :=
  343 + 19 * sizeOfShapeHOL returnShape + 289 * globalCount + 49 * payload

theorem callExitOverhead_le (r : Option (PanSemResultExact 64)) :
    callExitOverhead r ≤ 147 + 49 * callPayloadWords r := by
  rcases r with _ | r
  · simp [callExitOverhead, callPayloadWords, returnCopy]
  · cases r <;> simp [callExitOverhead, callPayloadWords, returnCopy] <;> omega

theorem globals_bvSubZero (x : BitVec 64) : x - 0 = x := by simp

theorem globals_compile_call_entry (context : PanGlobalsContextExact 64) (name : MlStringHOL) :
    compileProgExactHOL context (.call none name []) = .call none name [] := by
  simp [compileProgExactHOL, compileExpExactHOLList]

theorem globals_inits_length : ∀ (decls : List (DeclHOL 64)) (context : PanGlobalsContextExact 64),
    (compileDecsExactHOL context decls).1.length = (decls.filter isDeclHOL).length
  | [], _ => by simp [compileDecsExactHOL]
  | .decl shape name value :: rest, context => by
    rw [List.filter_cons_of_pos (by rfl)]
    simp [compileDecsExactHOL, globals_inits_length rest]
  | .function declaration :: rest, context => by
    simp [compileDecsExactHOL, isDeclHOL, globals_inits_length rest]
  | .exnDecl name shape :: rest, context => by
    simp [compileDecsExactHOL, isDeclHOL, globals_inits_length rest]
  | .name name shape :: rest, context => by
    simp [compileDecsExactHOL, isDeclHOL, globals_inits_length rest]

theorem globals_top_entry (B : Nat) {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (code : List (DeclHOL 64)) (start : MlS) (mgs : BitVec 64) (freeAddrs : BitVec 64 → Prop)
    (tmem : BitVec 64 → HolWordLab 64) (tlocals : HolFiniteMapExact MlS (ValueHOL 64))
    (h : ((functionsHOL code).map Prod.fst).Nodup ∧
      t = { s with
        topAddr := s.topAddr + mgs
        memaddrs := fun address => s.memaddrs address ∨ freeAddrs address
        memory := tmem
        locals := tlocals } ∧
      s.code = HolFiniteMapExact.empty ∧
      s.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL s.topAddr ∧
      goodDimindex 64 ∧
      mgs = panBytesInWord 64 *
        BitVec.ofNat 64 ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      freeAddrs = Flapjack.Compiler.Backend.StackRemove.addresses s.topAddr
        ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      (∀ address, s.memaddrs address → ¬ freeAddrs address) ∧
      (∀ address, s.memaddrs address → s.memory address = tmem address) ∧
      ¬ s.memaddrs (s.topAddr + mgs) ∧
      (panBytesInWord 64).toNat * ((decShapesHOL code).map sizeOfShapeHOL).sum < 2 ^ 64 ∧
      (∀ d ∈ code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true))
    (body : ProgHOL 64) (rshape : ShapeHOL)
    (hstartLookup : (functionsHOL code).lookup start = some ([], body, rshape))
    (ready : ∀ entry ∈ functionsHOL code,
      globalsReadyProg entry.2.2.1 = true ∧ globalsTemp ∉ entry.2.1.map Prod.fst)
    (constGlobals : constGlobalDecls (code.filter isDeclHOL) = true)
    {s1 : PanSemStateFiniteExact 64 F}
    (hs1 : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 F _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a)) code = some s1)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F} {ev : List WorkEvent}
    (run : StatementRun s1 (.call none start []) r post ev) (ok : r ≠ some .error) :
    ∃ T, @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 F _
        { t with structs := [] } (fun a => Classical.propDecidable (t.memaddrs a))
        (compileTopExactHOL code start) = some T ∧
      ∃ r' post' ev', StatementRun { T with clock := T.clock + 1 } (.call none start []) r' post' ev' ∧
        r' = r ∧ sharpSourceScore B ev' ≤ sharpSourceScore B ev +
          globalsTopInit rshape (code.filter isDeclHOL).length (callPayloadWords r) := by
  classical
  obtain ⟨hdistinct, ht, hcode, hglobals, halign, hgood, rfl, rfl, hdisj, hmem,
    htopNot, hbound, hkinds⟩ := h
  have hkindsB : code.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) =
      true := by
    apply List.all_eq_true.mpr
    intro d hd
    rcases hkinds d hd with h | h | h <;> simp [h]
  have hT1 := evaluateCompileTopOfSource _ s1 { t with structs := [] } code start _ hs1
    hstartLookup hkinds rfl (by rw [ht])
  refine ⟨_, hT1, ?_⟩
  have hs1orig := hs1
  have hres := Flapjack.resortDeclsEvaluate { s with structs := [] } code hkindsB
  -- Source evaluation in HOL's resorted order: exceptions, declarations, functions.
  have hpart : resortDeclsHOL code = code.filter isExnDeclHOL ++ code.filter isDeclHOL ++
      code.filter isFunctionHOL := by
    have hnames : code.filter isNameHOL = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro d hd
      rcases hkinds d hd with h | h | h <;> cases d <;>
        simp_all [isNameHOL, isFunctionHOL, isDeclHOL, isExnDeclHOL]
    simp [resortDeclsHOL, hnames]
  have hs1orig := hs1
  have hres := Flapjack.resortDeclsEvaluate { s with structs := [] } code hkindsB
  rw [← hres, hpart, Flapjack.evaluateDeclsHOLFinite_append,
    Flapjack.evaluateDeclsHOLFinite_append] at hs1
  cases hsE : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 F _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a))
      (code.filter isExnDeclHOL) with
  | none => simp [hsE] at hs1
  | some sE =>
  cases hsD : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 F _
      sE (fun a => Classical.propDecidable (sE.memaddrs a)) (code.filter isDeclHOL) with
  | none => simp [hsE, hsD] at hs1
  | some sD =>
  simp only [hsE, hsD, Option.bind_some] at hs1
  have hsEform := evalExnsForm _ _ sE (fun d hd => (List.mem_filter.mp hd).2) hsE
  have hs1form := evalFunsForm _ _ s1 (fun d hd => (List.mem_filter.mp hd).2) hs1
  have hsDcode : sD.code = sE.code := by
    have := evaluateDeclsHOLFinite_functions sE _ sD hsD
    rw [this, functionsHOL_filter_isDecl]
    rfl
  -- The compiler's declaration-list result and the explicit target code table.
  rcases hc : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64
           ((decShapesHOL code).map sizeOfShapeHOL).sum } : PanGlobalsContextExact 64)
      (fpermDecsHOL start (newMainNameHOL code) (resortDeclsHOL code)) with
    ⟨inits, funsC, exnsC, ctx⟩
  have hexplicit := PanGlobalsCompileTopSemanticsExact.evaluateDeclsCompileTopHOLFinite
    _ s1 code start [] body rshape inits funsC exnsC ctx ⟨hs1orig, hstartLookup, hkinds, hc⟩
  have hgeneric := evaluateCompileTopOfSource _ s1 { s with structs := [] } code start _ hs1orig
    hstartLookup hkinds rfl rfl
  rw [hgeneric] at hexplicit
  have htable := congrArg PanSemStateFiniteExact.code (Option.some.inj hexplicit)
  simp only at htable
  clear hexplicit hgeneric hres
  subst hsEform
  clear hsE hpart
  simp only at hsD hsDcode
  obtain ⟨N, hNdef⟩ : ∃ N, N = ((decShapesHOL code).map sizeOfShapeHOL).sum := ⟨_, rfl⟩
  obtain ⟨nm, hnm⟩ : ∃ nm, nm = newMainNameHOL code := ⟨_, rfl⟩
  rw [← hNdef] at ht hdisj htopNot hbound hc
  rw [← hnm] at hc htable
  obtain ⟨T, hT⟩ : ∃ T : PanSemStateFiniteExact 64 F, T = { t with
    structs := []
    code := t.code.updateList (functionsHOL (compileTopExactHOL code start))
    eshapes := t.eshapes.updateList (exceptionsHOL (compileTopExactHOL code start)) } :=
    ⟨_, rfl⟩
  rw [← hT]
  have hTcode : T.code = (HolFiniteMapExact.empty.update
      (start, [], .seq (nestedSeqHOL inits) (.call none nm []), rshape)).updateList
      ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
        (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))) := by
    rw [hT]; simp only; rw [ht]; simp only; rw [htable, hcode]; rfl
  -- Initial-globals simulation of the declaration initialisers.
  have hcD : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 N } :
         PanGlobalsContextExact 64) (code.filter isDeclHOL) = (inits, [], [], ctx) := by
    have := compile_decs_FILTER_declsHOL _ _ _ _ _ _ hc
    rwa [filterDeclFperm, filterDeclResort] at this
  have hND : ((decShapesHOL (code.filter isDeclHOL)).map sizeOfShapeHOL).sum = N := by
    rw [(dec_shapes_FILTERHOL code).2.2.1]; exact hNdef.symm
  obtain ⟨t', hrun, hrel', hclk, hffi, hloc, -⟩ := PanGlobalsInitGlobalsAssembly.initGlobalsAll _ (code.filter isDeclHOL) _ sD
    inits [] [] ctx { T with locals := HolFiniteMapExact.empty } _
    ⟨hsD, fun d hd => (List.mem_filter.mp hd).2, hcD, by
      unfold panGlobalsStateRelHOLExact
      subst hT ht
      refine ⟨?_, fun h => absurd h (by decide), rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_,
        fun a h => Or.inl h, rfl, hmem, rfl, ?_, ?_, ?_, ?_, hgood⟩
      · change s.topAddr = s.topAddr + panBytesInWord 64 * BitVec.ofNat 64 N -
          panBytesInWord 64 * BitVec.ofNat 64 N
        rw [BitVec.add_sub_cancel]
      · rw [exceptionsFilterExn, exceptions_compile_topHOL code start _ hstartLookup]
      · intro name value h
        rw [hglobals] at h
        cases h
      · intro name shape address h
        cases h
      · intro f ps p rs h
        rw [hcode] at h
        cases h
      · intro _ _ _ _ _ _ _ h
        exact absurd (by rw [hglobals]; rfl) h
      · rintro (h | h)
        · exact htopNot h
        · exact topNotInAddresses hgood _ _ hbound h
      · exact alignedAdd hgood _ _ halign
          (PanGlobalsInitGlobalsAlignment.byteAlignedBytesInWordMulHOL _ hgood), rfl, by
      intro a h
      rw [hND]
      subst hT ht
      change ¬ Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord 64 * BitVec.ofNat 64 N -
          panBytesInWord 64 * BitVec.ofNat 64 N - 0) N a
      rw [globals_bvSubZero, BitVec.add_sub_cancel]
      exact hdisj a h, by
      intro a h
      rw [hND] at h
      subst hT ht
      change Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord 64 * BitVec.ofNat 64 N -
          panBytesInWord 64 * BitVec.ofNat 64 N - 0) N a at h
      rw [globals_bvSubZero, BitVec.add_sub_cancel] at h
      exact Or.inr h,
      alignedZero, hcode, by
      rintro v sh addr ⟨h1, -⟩
      change (s.globals.lookup v).isSome = true at h1
      rw [hglobals] at h1
      (cases h1), by rw [hND]; exact hbound⟩
  -- Function-table facts for the renamed and compiled code.
  have hnmFresh : nm ∉ (functionsHOL code).map Prod.fst := by
    rw [hnm]; exact new_main_name_correctHOL code
  have hstartMem : start ∈ (functionsHOL code).map Prod.fst :=
    List.mem_map.mpr ⟨_, lookupMem _ _ _ hstartLookup, rfl⟩
  have hnmStart : nm ≠ start := fun h => hnmFresh (h ▸ hstartMem)
  have hfpNodup := ALL_DISTINCT_fperm_decsHOL start nm code hdistinct
  have hLkeys : ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
      (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))).map Prod.fst =
      (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [List.map_map]; rfl
  have hLNodup := hLkeys ▸ hfpNodup
  have hTlookup : ∀ f entry, (f, entry) ∈ functionsHOL (fpermDecsHOL start nm code) →
      T.code.lookup f = some (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2) := by
    intro f entry hmem
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupReverseOfNodup _ _ hLNodup,
      lookupOfMemNodup _ f (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2)
        (List.mem_map.mpr ⟨(f, entry), hmem, rfl⟩) hLNodup]
  have hstartNotRenamed : start ∉ (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [functionsFpermDecsHOL, List.map_map]
    intro hmem
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
    simp only [Function.comp, fpermName] at heq
    by_cases h1 : start = entry.1
    · rw [if_pos h1] at heq; exact hnmStart heq
    · rw [if_neg h1] at heq
      by_cases h2 : nm = entry.1
      · exact hnmFresh (List.mem_map.mpr ⟨entry, hentry, h2.symm⟩)
      · rw [if_neg h2] at heq; exact h1 heq.symm
  -- Target: the initialiser call reduces to the renamed original entry.
  have hL1 : T.code.lookup start =
      some ([], .seq (nestedSeqHOL inits) (.call none nm []), rshape) := by
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupNoneOfNotMem _ _ (by
        rw [List.map_reverse, List.mem_reverse, hLkeys]; exact hstartNotRenamed)]
    simp [HolFiniteMapExact.update, FUPDATE]
  have hbodyMem : (nm, ([] : List (MlS × ShapeHOL)), fpermHOL start nm body, rshape) ∈
      functionsHOL (fpermDecsHOL start nm code) := by
    rw [functionsFpermDecsHOL]
    refine List.mem_map.mpr ⟨(start, [], body, rshape), lookupMem _ _ _ hstartLookup, ?_⟩
    simp [fpermName]
  have hL2 := hTlookup nm _ hbodyMem
  -- Source: rename the entry, empty the locals, and relate to the target.
  have hsDempty : sD.code = HolFiniteMapExact.empty := hsDcode.trans hcode
  have hupd : ∀ (m : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
      (l : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)),
      m.updateList l = m.updateListEq l := by
    intro m l
    apply HolFiniteMapExact.ext
    funext k
    simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_updateListEq]
    rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  have hC2 : fpermCodeHOL start nm s1.code =
      HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL start nm code)) := by
    rw [hs1form]
    simp only
    rw [hsDempty, functionsHOL_filter_isFunction, hupd, hupd,
      fpermCodeHOL_updateList_functions, fpermCodeHOL_empty]
  have hinv := Flapjack.evaluateInvariantsHOLFinite (nestedSeqHOL inits)
    (PanPropsEvalStateFiniteExact.ofPanSemFinite { T with locals := HolFiniteMapExact.empty })
    none (PanPropsEvalStateFiniteExact.ofPanSemFinite t') (by
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, hrun])
  have htcode : t'.code = T.code := hinv.2.2.2.2.2.2.1
  have hrelT : panGlobalsStateRelHOLExact true ctx
      (emptyLocalsHOLFinite { s1 with code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))) }) t' := by
    subst hs1form
    obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18,
      h19⟩ := hrel'
    refine ⟨h1, fun _ => ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_, h16,
      h17, h18, h19⟩
    · rw [hloc]; rfl
    · intro f ps p rs hlk
      change (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))).lookup f = _ at hlk
      rw [emptyUpdateListLookup _ _ hfpNodup] at hlk
      rw [htcode]
      exact hTlookup f (ps, p, rs) (lookupMem _ _ _ hlk)

  -- Source: rename the entry and empty the caller locals; events unchanged.
  have frun := fperm_run start nm run ok (fpermCodeHOL start nm s1.code) rfl
  have hcall : fpermHOL start nm (.call none start [] : ProgHOL 64) = .call none nm [] := by
    rw [fperm_call]; simp [simpMapInfo, fpermName]
  rw [hcall, hC2] at frun
  obtain ⟨post2, erun⟩ := entry_empty_locals frun
  -- The renamed, compiled code satisfies the pan_globals certificate.
  obtain ⟨C2, hC2def⟩ : ∃ C2 : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL),
      C2 = HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL start nm code)) := ⟨_, rfl⟩
  rw [← hC2def] at erun hrelT
  have codeReady : GlobalsCodeReady (emptyLocalsHOLFinite { s1 with code := C2 }).code := by
    intro f ps p rs hlk
    change C2.lookup f = _ at hlk
    rw [hC2def, emptyUpdateListLookup _ _ hfpNodup] at hlk
    have hmem := lookupMem _ _ _ hlk
    rw [functionsFpermDecsHOL] at hmem
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.1 hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨-, rfl, rfl, -⟩ := heq
    have := ready entry hentry
    rw [globals_ready_fperm]
    exact this
  have cov : GlobalsCovered ctx (emptyLocalsHOLFinite { s1 with code := C2 }) := by
    intro name entry found
    have hcov := globals_decls_cover (code.filter isDeclHOL)
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 N } : PanGlobalsContextExact 64)
      _ sD hsD (by intro n e f; cases f) name entry (by rw [hcD]; exact found)
    unfold GlobalsPresent at hcov ⊢
    rw [hs1form]
    exact hcov
  -- Target inner call: the pan_globals statement transfer.
  obtain ⟨ev2, inner⟩ := source_evaluation_cost_trace t' (.call none nm [] : ProgHOL 64)
  have inner' := inner
  rw [← globals_compile_call_entry ctx nm] at inner'
  have le2 := globals_run_le B erun ctx t' hrelT ok
    (by simp [globalsReadyProg, globalsReadyExps]) codeReady (by rfl) cov _ _ _ inner'
  obtain ⟨hr2, -⟩ := globals_sub_match erun ok hrelT inner'
  -- Initialiser run: constant stores.
  obtain ⟨ev1, initTrace⟩ := source_evaluation_cost_trace
    { T with locals := HolFiniteMapExact.empty } (nestedSeqHOL inits)
  rw [hrun] at initTrace
  have stores : ConstStores inits := by
    have h := globals_constStores (code.filter isDeclHOL)
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 N } : PanGlobalsContextExact 64) constGlobals
    rw [hcD] at h; exact h
  have initLe := globals_inits_score B inits stores initTrace (by simp)
  have initLen : inits.length = (code.filter isDeclHOL).length := by
    have h := globals_inits_length (code.filter isDeclHOL)
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 N } : PanGlobalsContextExact 64)
    rw [hcD] at h
    rw [h, List.filter_filter]
    simp
  -- Outer call of the generated entry.
  have hlkExact : lookupCodeHOLExact T.code.lookup start [] =
      some (.seq (nestedSeqHOL inits) (.call none nm []), fun _ => none, rshape) := by
    unfold lookupCodeHOLExact; rw [hL1]; simp
  obtain ⟨callee, hlk, hcallee⟩ : ∃ callee,
      PanSemStateFiniteExact.lookupCodeHOLFinite T.code.lookup start [] =
      some (.seq (nestedSeqHOL inits) (.call none nm []), callee, rshape) ∧
      callee = HolFiniteMapExact.empty := by
    rcases hc : PanSemStateFiniteExact.lookupCodeHOLFinite T.code.lookup start [] with _ | ⟨b, c, rs⟩
    · unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hc
      split at hc
      · rename_i h; rw [hlkExact] at h; cases h
      · cases hc
    · have e := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hc
      rw [hlkExact] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, hl, rfl⟩ := e
      exact ⟨c, rfl, holFiniteMapExact_eq_of_lookup_eq (by rw [← hl]; rfl)⟩
  subst hcallee
  have entryState : callEntryStateHOLFinite { T with clock := T.clock + 1 } HolFiniteMapExact.empty =
      { T with locals := HolFiniteMapExact.empty } := by
    simp [callEntryStateHOLFinite]
  have bodyRun := StatementRun.seqNext initTrace inner
  rw [← entryState] at bodyRun
  have args0 : evalListHOLFinite { T with clock := T.clock + 1 }
      (h := fun a => Classical.propDecidable (({ T with clock := T.clock + 1 } :
        PanSemStateFiniteExact 64 F).memaddrs a)) [] = some [] := by
    simp [evalListHOLFinite, evalListHOLExact]
  rcases hplan : callCostPlan { T with clock := T.clock + 1 } none rshape
      (evaluateHOLFiniteState t' (.call none nm [])).1 (evaluateHOLFiniteState t' (.call none nm [])).2
    with ⟨res, pst⟩ | ⟨e, p⟩
  · have outer := StatementRun.callDone (s := { T with clock := T.clock + 1 }) args0 hlk
      (by simp) bodyRun hplan
    have srcLk : C2.lookup nm = some ([], fpermHOL start nm body, rshape) := by
      rw [hC2def, emptyUpdateListLookup _ _ hfpNodup]
      exact lookupOfMemNodup _ _ _ hbodyMem hfpNodup
    have resOk : res = r := by
      have hplan' := hplan
      rw [globals_compile_call_entry] at hr2
      rw [hr2] at hplan'
      exact entry_plan_same erun ok (entry_lookup_noargs srcLk) _ _ hplan'
    refine ⟨res, pst, _, outer, resOk, ?_⟩
    have structsT : T.structs = [] := by rw [hT]
    rw [globals_compile_call_entry] at hr2
    rw [hr2] at outer ⊢
    simp only [expressionListEvents, List.flatMap_nil, List.length_nil, callGlobalEvents,
      List.nil_append, List.append_nil, structsT, sharp_size_nil, globalsTopInit] at outer ⊢
    gsimp
    have := callExitOverhead_le r
    omega
  · obtain ⟨_, _, _, hinfo⟩ := globals_plan_handler_info hplan
    cases hinfo

#print axioms globals_top_entry
end InitECandidate.Runtime.FineCost
