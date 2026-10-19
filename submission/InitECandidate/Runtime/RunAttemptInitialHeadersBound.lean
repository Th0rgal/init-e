import InitECandidate.Runtime.RunAttemptInitialReach
import InitECandidate.Runtime.RunAttemptHeadersDeclarationReach
/-!
The actual `run_attempt` source body reaches the real header-validation call
site and then its real continuation `runAttemptAt 3` within the proved callee
budget.

The entry bridge (`RunAttemptInitialReach`) turns the original prefix
`pl = load(si + 0); skip` into the exact intermediate state
`setVarHOLFinite "pl" payload s` at zero cost, and the checked declaration
reach then runs the original `validate_headers` callee from that state, so the
whole composition inherits the same caller geometry and the same callee budget
without any new header bound.  The retained body run keeps the evidence for
stronger post-call contracts (see `RunAttemptHeadersDeclarationContract`).
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual `run_attempt` prefix reaches the header-call site as the exact
`pl`-extended state, keeping memory, globals, domain, clock and code. -/
theorem run_attempt_initial_state_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si payload : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload) :
    Reaches s (runAttemptAt 0)
      (fun ready => ready = setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
      0 (runAttemptAt 2) := by
  obtain ⟨bodyShape,skipShape⟩ := source_run_attempt_prefix
  rw [bodyShape]
  refine reaches_trans s (.dec (ofString "pl") .one
      (.load .one (.op .add [.var .local (ofString "si"),.const 0])) (runAttemptAt 1))
    (runAttemptAt 1) (runAttemptAt 2)
    (fun E => E = setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
    (fun E => E = setVarHOLFinite (ofString "pl") (.val (.word payload)) s) 0 0 ?_ ?_
  · apply reaches_dec
    intro v loaded
    have domainSi : s.memaddrs si := by simpa using siDomain
    have cellSi : s.memory si = .word payload := by simpa using siCell
    have valueEq : v = .val (.word payload) := by
      simp [evalHOLExact,evalListHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
        memLoadHOLExact,List.map_cons,List.map_nil,domainSi,cellSi] at loaded
      simpa using loaded.symm
    subst valueEq
    exact ⟨payload,rfl,rfl⟩
  · intro next nextEq
    subst nextEq
    rw [skipShape]
    apply reaches_seq
    refine Or.inl ⟨setVarHOLFinite (ofString "pl") (.val (.word payload)) s,rfl,?_,le_refl _,?_⟩
    · simp
    exact evaluateHOLFiniteState_skip _

/-- Evidence retained by the composed actual body run: the caller locals keep
the real `pl` payload and receive some `vh` value from the actual call, while
the caller memory domain and code are untouched.  The real body run itself is
available by composing with `run_attempt_headers_declaration_reaches`
(`RunAttemptHeadersDeclarationContract` refines it further). -/
def RunAttemptHeadersComposed {F : Type} (s : PanSemStateFiniteExact 64 F) (payload : BitVec 64) :
    PanSemStateFiniteExact 64 F → Prop :=
  fun ready => ∃ value : ValueHOL 64,
    ready.locals = (s.locals.update (ofString "pl",.val (.word payload))).update (ofString "vh",value) ∧
    ready.memaddrs = s.memaddrs ∧ ready.code = s.code

/-- The actual `run_attempt` source body reaches `runAttemptAt 3` through the
real header-validation call, within the proved callee budget, keeping the real
caller locals, domain and code. -/
theorem run_attempt_initial_headers_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si payload array count input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling inputLimit : Nat)
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload)
    (inputBound : inputLength.toNat ≤ inputLimit) (inputCap : inputLimit ≤ 134217712)
    (inputAfter : ceiling ≤ input.toNat) (tableAbove : ceiling ≤ array.toNat)
    (inputBefore : input.toNat + inputLength.toNat ≤ heap.toNat)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (ceilingAligned : ceiling % 8 = 0) (stateBelow : keccakState.toNat + 200 ≤ ceiling)
    (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 72 80 array count input inputLength heap)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (stateGlobal : s.globals.lookup (ofString "keccak_st") = some (.val (.word keccakState)))
    (padGlobal : s.globals.lookup (ofString "keccak_pad") = some (.val (.word keccakPad)))
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, heap.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (heapGlobal : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : s.code = originalRuntimeCode)
    (budget : validateHeadersBodyCost inputLimit + 1 ≤ s.clock) :
    Reaches s (runAttemptAt 0) (RunAttemptHeadersComposed s payload)
      (validateHeadersBodyCost inputLimit + 1) (runAttemptAt 3) := by
  rcases run_attempt_initial_state_reaches s si payload atSi siDomain siCell with
    ⟨E, pE, c1, c2, sc⟩ | ab
  · subst pE
    have atSiNext : (setVarHOLFinite (ofString "pl") (.val (.word payload)) s).locals.lookup
        (ofString "si") = some (.val (.word si)) := by
      rw [setVarHOLFinite]
      simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,atSi]
    have linkedNext : WitnessArrayLinked (setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
        si 72 80 array count input inputLength heap :=
      WitnessArrayLinked.after_frame s (setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
        si 72 80 array count input inputLength heap linked rfl rfl
    have base := run_attempt_headers_declaration_reaches
      (setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
      si array count input inputLength scratch frame heap keccakState keccakPad ceiling inputLimit
      inputBound inputCap inputAfter tableAbove inputBefore orderedFrame framePositive scratchBelow
      ceilingAligned stateBelow padBelow atSiNext linkedNext scratchGlobal frameGlobal stateGlobal padGlobal
      arena heapArena heapGlobal heapBound code budget
    rcases base with ⟨F', qF, d1, d2, sc2⟩ | ab2
    · refine Or.inl ⟨F', ?_, by omega, by omega, scoped_trans sc sc2⟩
      obtain ⟨value,bodyPost,run,pin,mem,glob,dom,codeK⟩ := qF
      exact ⟨value,pin,dom,codeK⟩
    · exact Or.inr (stAbort_scoped s _ _ (validateHeadersBodyCost inputLimit + 1) sc ab2)
  · exact Or.inr (stAbort_mono s _ 0 _ (by omega) ab)

#print axioms run_attempt_initial_state_reaches
#print axioms run_attempt_initial_headers_reaches
end InitECandidate.Runtime
