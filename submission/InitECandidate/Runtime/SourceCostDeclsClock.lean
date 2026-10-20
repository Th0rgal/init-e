import InitECandidate.Runtime.SourceCostEntryLocals
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Declaration evaluation never reads the clock. -/

theorem decls_clock {F : Type} (clock : Nat) :
    ∀ (decls : List (DeclHOL 64)) (s : PanSemStateFiniteExact 64 F),
      @evaluateDeclsHOLFinite 64 F _ { s with clock := clock }
          (fun a => Classical.propDecidable (s.memaddrs a)) decls =
        (@evaluateDeclsHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) decls).map
          (fun s' => { s' with clock := clock })
  | [], s => rfl
  | .name _ _ :: rest, s => by
    simp only [evaluateDeclsHOLFinite]; exact decls_clock clock rest s
  | .decl shape name expression :: rest, s => by
    simp only [evaluateDeclsHOLFinite]
    have he : @evalHOLFinite 64 F _ (emptyLocalsHOLFinite { s with clock := clock })
        (fun a => Classical.propDecidable (s.memaddrs a)) expression =
        @evalHOLFinite 64 F _ (emptyLocalsHOLFinite s)
        (fun a => Classical.propDecidable (s.memaddrs a)) expression :=
      @evalHOLFinite_upd_clock_eq 64 F _ (emptyLocalsHOLFinite s)
        (fun a => Classical.propDecidable (s.memaddrs a)) clock expression
    rw [he]
    split
    · split
      · exact decls_clock clock rest (setGlobalHOLFinite name _ s)
      · rfl
    · rfl
  | .function declaration :: rest, s => by
    simp only [evaluateDeclsHOLFinite]
    split
    · exact decls_clock clock rest { s with code := s.code.update (declaration.name, _) }
    · rfl
  | .exnDecl exceptionName shape :: rest, s => by
    simp only [evaluateDeclsHOLFinite]
    split
    · exact decls_clock clock rest { s with eshapes := s.eshapes.update (exceptionName, shape) }
    · rfl

#print axioms decls_clock
end InitECandidate.Runtime.FineCost
