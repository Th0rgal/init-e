import InitECandidate.Runtime.DecodeWitnessWrapperSource
import InitECandidate.Runtime.OriginalDecodeWitnessWrapperCode
import InitECandidate.Runtime.WitnessScratchPrimitiveBounds
import InitECandidate.Runtime.RunBoundedHandledCall
import InitECandidate.Runtime.PanThreeWordShapeLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 def decodeWitnessBodyCallee (db pointer length : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((HolFiniteMapExact.empty.update (ofString "db",.val (.word db))).update
    (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))
 theorem decode_witness_mpt_handler_bounded : ProgBounded decodeWitnessMptHandler 1 := by
  rw [source_decode_witness_mpt_handler]
  exact ProgBounded.seq (ProgBounded.call scratch_release_fun_bounded none [.var .local (ofString "mark")])
    (ProgBounded.straight _ rfl)
/-- Actual MptErr wrapper from the bound on its exact original body-call entry.
The handler's release and rethrow are included on every exception outcome. -/
theorem runBounded_decode_witness_mpt_wrapper {F : Type} (s : PanSemStateFiniteExact 64 F)
    (db pointer length : BitVec 64) (bodyCost : Nat)
    (atDb : s.locals.lookup (ofString "db")=some (.val (.word db)))
    (atPointer : s.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
    (code : s.code=originalRuntimeCode) (budget : bodyCost+2≤s.clock)
    (bodyBound : RunBounded (callEntryStateHOLFinite s (decodeWitnessBodyCallee db pointer length))
      (sourceFunctionBody Guest.guestFn__decode_witness_node_body) bodyCost) :
    RunBounded s (sourceFunctionBody Guest.guestFn__decode_witness_node_mpt) (bodyCost+2) := by
  rw [source_decode_witness_mpt_body]
  apply RunBounded.decConst s (ofString "e") (0#64)
  let first := setVarHOLFinite (ofString "e") (.val (.word (0#64))) s
  apply RunBounded.decConst first (ofString "nd") (0#64)
  let entered := setVarHOLFinite (ofString "nd") (.val (.word (0#64))) first
  have other (name : MlS) (notNd : name≠ofString "nd") (notE : name≠ofString "e") : entered.locals.lookup name=s.locals.lookup name := by
    simp [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notNd,Ne.symm notE]
  have args : evalListHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
      [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n")]=
      some [.val (.word db),.val (.word pointer),.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,other (ofString "db") (by decide) (by decide),other (ofString "p") (by decide) (by decide),other (ofString "n") (by decide) (by decide),atDb,atPointer,atLength]
  have lookup := pan_three_word_shape_lookup entered.code.lookup (ofString "_decode_witness_node_body")
    (ofString "db") (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn__decode_witness_node_body)
    .one db pointer length (by decide) (by decide) (by decide) (by change s.code.lookup _ = _; rw [code];exact originalRuntimeCode_decodeWitnessBody_lookup)
  have enteredBody : RunBounded (callEntryStateHOLFinite entered (decodeWitnessBodyCallee db pointer length))
      (sourceFunctionBody Guest.guestFn__decode_witness_node_body) bodyCost := by
    simpa only [entered,first,callEntryStateHOLFinite,setVarHOLFinite] using bodyBound
  have called := RunBounded.handledCall entered (ofString "_decode_witness_node_body") (ofString "MptErr") (ofString "e")
    (some (.local,ofString "nd")) _ _ (sourceFunctionBody Guest.guestFn__decode_witness_node_body) decodeWitnessMptHandler
    (decodeWitnessBodyCallee db pointer length) .one bodyCost 1 args lookup code (by change bodyCost+1+1≤s.clock;omega)
    enteredBody decode_witness_mpt_handler_bounded
  rw [source_decode_witness_mpt_after_locals]
  have calledCost : RunBounded entered (.call (some (some (.local,ofString "nd"),some (ofString "MptErr",ofString "e",decodeWitnessMptHandler))) (ofString "_decode_witness_node_body") [.var .local (ofString "db"),.var .local (ofString "p"),.var .local (ofString "n")]) (bodyCost+2) := by simpa only [Nat.add_assoc] using called
  have whole := RunBounded.seq (tail := .return (.var .local (ofString "nd"))) (b := 0) calledCost
    (by change bodyCost+2+0≤s.clock;omega) (by
      intro next normal nextCode ticks
      exact RunBounded.ofProg (state := next) (ProgBounded.straight _ rfl) (nextCode.trans code) (Nat.zero_le _))
  simpa only [Nat.add_zero,entered] using whole
#print axioms decode_witness_mpt_handler_bounded
#print axioms runBounded_decode_witness_mpt_wrapper
end InitECandidate.Runtime
