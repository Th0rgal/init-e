import InitECandidate.Runtime.PanCrepClock
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemantics
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

noncomputable def panCrepEntryContext {width : Nat} [NeZero width] (code : List (DeclHOL width)) :
    PanToCrepContextExact width :=
  mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL code)) 0 (getEidsFromDeclsHOL code)

/-- Original entry-call simulation with no clock inflation and all static
compiler relations derived from the declaration table. -/
theorem pan_crep_entry_return_same_clock {width : Nat} [NeZero width] {F : Type}
    (s : PanSemStateFiniteExact width F) (t : CrepSemHOLState width F)
    (code : List (DeclHOL width)) (start : MlS)
    (state : panToCrepStateRelFiniteExact s t)
    (distinct : ((functionsHOL code).map Prod.fst).Nodup)
    (sourceCode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL code).reverse)
    (targetCode : t.code = HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW code).reverse)
    (locals : s.locals = HolFiniteMapExact.empty)
    (localised : ∀ entry ∈ functionsHOL code, localisedProgHOL entry.2.2.1 = true)
    (size : sizeOfEidsHOL code < 2 ^ width)
    (exceptions : ∀ key, (s.eshapes.lookup key).isSome = ((getEidsFromDeclsHOL code).lookup key).isSome)
    (post : PanSemStateFiniteExact width F) (value : ValueHOL width)
    (run : s.evaluateHOLFiniteState (.call none start []) = (some (.returned value),post)) :
    ∃ final : CrepSemHOLState width F,
      evalCrepSemHOLProgExact t (.call none start []) = (some (.return (flattenHOL value)),final) ∧
      panToCrepStateRelFiniteExact post final ∧
      codeRelExactHOLW (panCrepEntryContext code) post.code final.code ∧
      panToCrepExcpRelFiniteExact (panCrepEntryContext code).eids post.eshapes ∧
      t.clock = s.clock ∧ final.clock = post.clock ∧ final.ffi = post.ffi := by
  have codeRel : codeRelExactHOLW (panCrepEntryContext code) s.code t.code := by
    rw [sourceCode,targetCode]
    exact mkCtxtCodeImpCodeRelExactHOLW code distinct localised
  have excRel : panToCrepExcpRelFiniteExact (panCrepEntryContext code).eids s.eshapes :=
    getEidsImpExcpRelExact s.eshapes code ⟨size,exceptions⟩
  have localRel : panToCrepLocalsRelFiniteExact (panCrepEntryContext code) s.locals t.locals := by
    rw [locals]
    exact mkCtxtImpLocalsRelExact _ _ _
  obtain ⟨result,final,initialClock,finalClock,evaluated,postState,postCode,postExc,outcome⟩ :=
    pan_crep_same_clock (.call none start []) s (some (.returned value)) post t (panCrepEntryContext code)
      ⟨run,by simp,state,codeRel,excRel,localRel,by simp [localisedProgHOL,everyExpListHOL]⟩
  change result = some (.return (flattenHOL value)) at outcome
  subst result
  have compiled : compileProgExactHOLW (panCrepEntryContext code) (.call none start [] : ProgHOL width) =
      (.call none start [] : CrepProgHOL width) := by
    simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList]
  rw [compiled] at evaluated
  exact ⟨final,evaluated,postState,postCode,postExc,initialClock,finalClock,postState.2.2.2.2.2.2.2.1.symm⟩

#print axioms pan_crep_entry_return_same_clock
/-- Original entry-call simulation with no clock inflation and all static
compiler relations derived from the declaration table. -/
theorem pan_crep_entry_ffi_same_clock {width : Nat} [NeZero width] {F : Type}
    (s : PanSemStateFiniteExact width F) (t : CrepSemHOLState width F)
    (code : List (DeclHOL width)) (start : MlS)
    (state : panToCrepStateRelFiniteExact s t)
    (distinct : ((functionsHOL code).map Prod.fst).Nodup)
    (sourceCode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL code).reverse)
    (targetCode : t.code = HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW code).reverse)
    (locals : s.locals = HolFiniteMapExact.empty)
    (localised : ∀ entry ∈ functionsHOL code, localisedProgHOL entry.2.2.1 = true)
    (size : sizeOfEidsHOL code < 2 ^ width)
    (exceptions : ∀ key, (s.eshapes.lookup key).isSome = ((getEidsFromDeclsHOL code).lookup key).isSome)
    (post : PanSemStateFiniteExact width F) (event : HolFinalEvent)
    (run : s.evaluateHOLFiniteState (.call none start []) = (some (.finalFfi event),post)) :
    ∃ final : CrepSemHOLState width F,
      evalCrepSemHOLProgExact t (.call none start []) = (some (.finalFfi event),final) ∧
      panToCrepStateRelFiniteExact post final ∧
      codeRelExactHOLW (panCrepEntryContext code) post.code final.code ∧
      panToCrepExcpRelFiniteExact (panCrepEntryContext code).eids post.eshapes ∧
      t.clock = s.clock ∧ final.clock = post.clock ∧ final.ffi = post.ffi := by
  have codeRel : codeRelExactHOLW (panCrepEntryContext code) s.code t.code := by
    rw [sourceCode,targetCode]
    exact mkCtxtCodeImpCodeRelExactHOLW code distinct localised
  have excRel : panToCrepExcpRelFiniteExact (panCrepEntryContext code).eids s.eshapes :=
    getEidsImpExcpRelExact s.eshapes code ⟨size,exceptions⟩
  have localRel : panToCrepLocalsRelFiniteExact (panCrepEntryContext code) s.locals t.locals := by
    rw [locals]
    exact mkCtxtImpLocalsRelExact _ _ _
  obtain ⟨result,final,initialClock,finalClock,evaluated,postState,postCode,postExc,outcome⟩ :=
    pan_crep_same_clock (.call none start []) s (some (.finalFfi event)) post t (panCrepEntryContext code)
      ⟨run,by simp,state,codeRel,excRel,localRel,by simp [localisedProgHOL,everyExpListHOL]⟩
  change result = some (.finalFfi event) at outcome
  subst result
  have compiled : compileProgExactHOLW (panCrepEntryContext code) (.call none start [] : ProgHOL width) =
      (.call none start [] : CrepProgHOL width) := by
    simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList]
  rw [compiled] at evaluated
  exact ⟨final,evaluated,postState,postCode,postExc,initialClock,finalClock,postState.2.2.2.2.2.2.2.1.symm⟩

#print axioms pan_crep_entry_ffi_same_clock
end InitECandidate.Runtime
