import InitECandidate.Runtime.SourceCostGlobalsTop
import InitECandidate.Runtime.SourceCostSimpTop
import InitECandidate.Runtime.SourceCostPanStructsId
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Whole-program preprocessing transfer: the original entry run from the
post-declaration state, through `pan_simp` (installed code), `pan_structs`
(the identity on struct-free programs) and `pan_globals` (generated entry), to
the run of the generated entry of the program `pan_to_crep` receives. -/

theorem source_top_entry {F : Type} (decls : List (DeclHOL 64)) (start : MlS)
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
    {s1 : PanSemStateFiniteExact 64 F}
    (hs1 : @evaluateDeclsHOLFinite 64 F _ { s0 with structs := [] }
      (fun a => Classical.propDecidable (s0.memaddrs a)) decls = some s1)
    {r : Option (PanSemResultExact 64)} {post : PanSemStateFiniteExact 64 F} {ev : List WorkEvent}
    (run : StatementRun { s1 with clock := clock } (.call none start []) r post ev)
    (ok : r ≠ some .error) :
    ∃ T, @evaluateDeclsHOLFinite 64 F _ { t with structs := [] }
        (fun a => Classical.propDecidable (t.memaddrs a))
        (compileTopExactHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL decls))
          start) = some T ∧
      ∃ r' post' ev', StatementRun { T with clock := T.clock + 1 } (.call none start []) r' post' ev' ∧
        r' ≠ some .error ∧ sharpScore ev' ≤ sharpScore ev +
          globalsTopInit rshape ((panSimpDeclsHOL decls).filter isDeclHOL).length (callPayloadWords r) := by
  obtain ⟨s1', hs1', post', ev1, run1, le1⟩ :=
    simp_top_entry decls s0 h.2.2.1 hs1 start clock run ok
  have hs1k : @evaluateDeclsHOLFinite 64 F _
      { ({ s0 with clock := clock } : PanSemStateFiniteExact 64 F) with structs := [] }
      (fun a => Classical.propDecidable (s0.memaddrs a)) (panSimpDeclsHOL decls) =
        some { s1' with clock := clock } := by
    have := decls_clock clock (panSimpDeclsHOL decls) { s0 with structs := [] }
    rw [hs1'] at this
    exact this
  obtain ⟨T, hT, r', post'', ev', run', ok', le'⟩ := globals_top_entry sharpReplayBound
    { s0 with clock := clock } t (panSimpDeclsHOL decls) start mgs freeAddrs tmem tlocals h body
    rshape hstartLookup ready constGlobals hs1k run1 ok
  rw [structFree]
  exact ⟨T, hT, r', post'', ev', run', ok', by
    have : sharpScore ev' ≤ sharpScore ev1 +
        globalsTopInit rshape ((panSimpDeclsHOL decls).filter isDeclHOL).length (callPayloadWords r) := le'
    omega⟩

#print axioms source_top_entry
end InitECandidate.Runtime.FineCost
