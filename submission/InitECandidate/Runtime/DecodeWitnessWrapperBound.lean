import InitECandidate.Runtime.DecodeWitnessMptWrapperBound
import InitECandidate.Runtime.ScratchMarkDeclarationExact
import InitECandidate.Runtime.PanFourWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 def decodeWitnessMptCallee (db pointer length mark : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (decodeWitnessBodyCallee db pointer length).update (ofString "mark",.val (.word mark))
 theorem decode_witness_rlp_handler_bounded : ProgBounded decodeWitnessRlpHandler 1 := by
  rw [source_decode_witness_rlp_handler]
  exact ProgBounded.seq (ProgBounded.call scratch_release_fun_bounded none [.var .local (ofString "mark")])
    (ProgBounded.straight _ rfl)
 theorem decode_witness_cleanup_bounded : ProgBounded decodeWitnessCleanup 1 := by
  rw [source_decode_witness_cleanup]
  exact ProgBounded.seq (ProgBounded.call scratch_release_fun_bounded none [.var .local (ofString "mark")])
    (ProgBounded.straight _ rfl)
/-- Both actual exception wrappers and all scratch cleanup paths are bounded
from the exact original body-entry state after three real call-entry ticks.
The body may return, reject, raise or fail; no successful-room premise. -/
theorem runBounded_decode_witness_wrapper {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db pointer length mark : BitVec 64) (bodyCost : Nat)
    (atDb : s.locals.lookup (ofString "db")=some (.val (.word db)))
    (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
    (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word mark)))
    (code : s.code=originalRuntimeCode) (budget : bodyCost+6≤s.clock)
    (bodyBound : RunBounded {callEntryStateHOLFinite s (decodeWitnessBodyCallee db pointer length) with clock:=s.clock-3}
      (sourceFunctionBody Guest.guestFn__decode_witness_node_body) bodyCost) :
    RunBounded s (sourceFunctionBody Guest.guestFn__decode_witness_node) (bodyCost+6) := by
  let marked := setVarHOLFinite (ofString "mark") (.val (.word mark)) {s with clock:=s.clock-1}
  have suffixBound : RunBounded marked decodeWitnessAfterMark (bodyCost+5) := by
    rw [source_decode_witness_after_mark]
    apply RunBounded.decConst marked (ofString "e") (0#64)
    let first := setVarHOLFinite (ofString "e") (.val (.word (0#64))) marked
    apply RunBounded.decConst first (ofString "nd") (0#64)
    let entered := setVarHOLFinite (ofString "nd") (.val (.word (0#64))) first
    have other (name : MlS) (notNd : name≠ofString "nd") (notE : name≠ofString "e") (notMark : name≠ofString "mark") :
        entered.locals.lookup name=s.locals.lookup name := by
      simp [entered,first,marked,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notNd,Ne.symm notE,Ne.symm notMark]
    have enteredDb := (other _ (by decide) (by decide) (by decide)).trans atDb
    have enteredP := (other _ (by decide) (by decide) (by decide)).trans atPointer
    have enteredN := (other _ (by decide) (by decide) (by decide)).trans atLength
    have enteredMark : entered.locals.lookup (ofString "mark")=some (.val (.word mark)) := by
      simp (config := {decide := true}) [entered,first,marked,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have args : evalListHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
        [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n"),.var .local (ofString "mark")]=
        some [.val (.word db),.val (.word pointer),.val (.word length),.val (.word mark)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,enteredDb,enteredP,enteredN,enteredMark]
    have lookup := pan_four_word_shape_lookup entered.code.lookup (ofString "_decode_witness_node_mpt")
      (ofString "db") (ofString "p") (ofString "n") (ofString "mark") (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt)
      .one db pointer length mark (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by change s.code.lookup _ = _; rw [code];exact originalRuntimeCode_decodeWitnessMpt_lookup)
    let entry := callEntryStateHOLFinite entered (decodeWitnessMptCallee db pointer length mark)
    have pDb : entry.locals.lookup (ofString "db")=some (.val (.word db)) := by
      simp (config := {decide := true}) [entry,decodeWitnessMptCallee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have pP : entry.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
      simp (config := {decide := true}) [entry,decodeWitnessMptCallee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have pN : entry.locals.lookup (ofString "n")=some (.val (.word length)) := by
      simp (config := {decide := true}) [entry,decodeWitnessMptCallee,decodeWitnessBodyCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have bodyEntryEq : callEntryStateHOLFinite entry (decodeWitnessBodyCallee db pointer length)=
        {callEntryStateHOLFinite s (decodeWitnessBodyCallee db pointer length) with clock:=s.clock-3} := by
      simp only [entry,entered,first,marked,callEntryStateHOLFinite,setVarHOLFinite,Nat.sub_sub]
    have mptBound := runBounded_decode_witness_mpt_wrapper entry db pointer length bodyCost pDb pP pN code
      (by change bodyCost+2≤s.clock-1-1;omega) (by rw [bodyEntryEq];exact bodyBound)
    have called := RunBounded.handledCall entered (ofString "_decode_witness_node_mpt") (ofString "RlpErr") (ofString "e")
      (some (.local,ofString "nd")) _ _ (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt) decodeWitnessRlpHandler
      (decodeWitnessMptCallee db pointer length mark) .one (bodyCost+2) 1 args lookup code
      (by change bodyCost+2+1+1≤s.clock-1;omega) mptBound decode_witness_rlp_handler_bounded
    have calledCost : RunBounded entered (.call (some (some (.local,ofString "nd"),some (ofString "RlpErr",ofString "e",decodeWitnessRlpHandler))) (ofString "_decode_witness_node_mpt") [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n"),.var .local (ofString "mark")]) (bodyCost+4) := by simpa only [Nat.add_assoc] using called
    rw [source_decode_witness_after_locals]
    have whole := RunBounded.seq (tail := decodeWitnessCleanup) (b := 1) calledCost
      (by change bodyCost+4+1≤s.clock-1;omega) (by
        intro next normal nextCode ticks
        exact RunBounded.ofProg (state := next) decode_witness_cleanup_bounded (nextCode.trans code) ticks)
    simpa only [Nat.add_assoc,entered] using whole
  have marker := evaluate_scratch_mark_declaration_exact s mark code atScratch (by omega) decodeWitnessAfterMark
  unfold RunBounded at suffixBound ⊢
  rw [source_decode_witness_body,marker]
  dsimp only
  change s.clock≤(evaluateHOLFiniteState marked decodeWitnessAfterMark).2.clock+(bodyCost+6) ∧
    (evaluateHOLFiniteState marked decodeWitnessAfterMark).2.clock≤s.clock ∧
    (evaluateHOLFiniteState marked decodeWitnessAfterMark).1≠some .timeOut
  have spent:=suffixBound.1
  have remaining:=suffixBound.2.1
  change s.clock-1≤_ at spent
  change _≤s.clock-1 at remaining
  exact ⟨by omega,by omega,suffixBound.2.2⟩
#print axioms decode_witness_rlp_handler_bounded
#print axioms decode_witness_cleanup_bounded
#print axioms runBounded_decode_witness_wrapper
end InitECandidate.Runtime
