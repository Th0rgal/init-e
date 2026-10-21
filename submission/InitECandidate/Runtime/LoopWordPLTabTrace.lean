import InitECandidate.Runtime.LoopSiteAll
import InitECandidate.Runtime.LoopWordPLRelabel
import InitECandidate.Runtime.SourceCostLoopWorkWs
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-! The WordSimp surcharge trace of an optimised Loop run, bounded by the same
run's trace under the certified caller+callee table: each returning call pays
`24 * callTab (caller, static target)` instead of its own site entry. -/

/-- The table trace price: the WordSimp surcharges with every returning-call
site charge raised to its caller+callee table entry. -/
noncomputable def tabTrace (c : Compiler.Encoders.Asm.AsmConfigExact 64) : LoopPriceL :=
  { surOnly (wsLoopPrice c wsT1 wsT2) with site := siteB }

theorem surOnly_ws_dom (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ p w, (surOnly (wsLoopPrice c wsT1 wsT2)).base.leaf p = some w → (loopWorkLeafCost p).isSome = true := by
  intro p w h
  simp only [surOnly, wsLoopPrice, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, -⟩ := h
  exact (wsLeaf c wsT1 wsT2).dom p v hv

/-- From an optimised Loop run at the WordSimp-source base prices, in a state
whose code table holds only pinned Loop outputs, at a label where the program
passes the site walk: the labelled run costs at most its base work plus a
table trace `S`. -/
theorem ws_trace_tab {F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) {s : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {output} {w : Nat}
    (work : LoopWorkP (wsLoopPrice c wsT1 wsT2).base s p output w) (l : Nat × Nat)
    (site : SiteLe siteA siteB l p)
    (hcode : ∀ n ps prog, sptLookup n s.code = some (ps, prog) → (n, ps, prog) ∈
      InitECandidate.Proofs.FrontendStages.Loop.outputs) :
    ∃ S w', LoopWorkPL (tabTrace c) l s p output S ∧ LoopWorkPL (wsLoopPrice c wsT1 wsT2) l s p output w' ∧
      w' ≤ w + S := by
  obtain ⟨S, w', tr, lab, h⟩ := LoopWorkP.relabel work l
  have hs : (surOnly (wsLoopPrice c wsT1 wsT2)).site = siteA := rfl
  obtain ⟨S', tr', hS⟩ := LoopWorkPL.site_mono siteB (surOnly_ws_dom c) tr (by rw [hs]; exact site)
    (by rw [hs]; exact codeSiteLe_of_outputs s hcode)
  exact ⟨S', w', tr', lab, by omega⟩

#print axioms ws_trace_tab
end InitECandidate.Runtime.FineCost
