import InitECandidate.Runtime.ComputeJumpdestsSource
import InitECandidate.Runtime.WordStoreMemoryFrame
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.PayloadOffsetReadWords
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
private theorem declaration_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64) (watched : BitVec 64)
 (frame : ∀value,(evaluateHOLFiniteState (setVarHOLFinite name value s) body).2.memory watched=s.memory watched) :
 (evaluateHOLFiniteState s (.dec name shape initializer body)).2.memory watched=s.memory watched := by
 rw [evaluateHOLFiniteState_dec_total]
 dsimp only
 split
 · rfl
 · split
   · exact frame _
   · rfl
private theorem seq_readonly_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (first tail : ProgHOL 64) (watched : BitVec 64) (readOnly : readOnlyMemory tail=true)
 (frame : (evaluateHOLFiniteState s first).2.memory watched=s.memory watched) :
 (evaluateHOLFiniteState s (.seq first tail)).2.memory watched=s.memory watched := by
 rw [evaluateHOLFiniteState_seq_line780]
 cases run : evaluateHOLFiniteState s first with
 | mk result post=>
  rw [run] at frame
  cases result with
  | none=>exact (congrFun (evaluate_readOnly_memory tail readOnly post) watched).trans frame
  | some result=>exact frame
private theorem conditional_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (yes no : ProgHOL 64) (watched : BitVec 64)
 (yesFrame : (evaluateHOLFiniteState s yes).2.memory watched=s.memory watched)
 (noFrame : (evaluateHOLFiniteState s no).2.memory watched=s.memory watched) :
 (evaluateHOLFiniteState s (.ite condition yes no)).2.memory watched=s.memory watched := by
 rw [evaluateHOLFiniteState_ite]
 split
 · split
   · exact noFrame
   · exact yesFrame
 · rfl

theorem eval_compute_jumpdests_store_address {F : Type} (s : PanSemStateFiniteExact 64 F)
 (bitmap pc : BitVec 64)
 (atBitmap : s.locals.lookup (ofString "bm")=some (.val (.word bitmap)))
 (atPc : s.locals.lookup (ofString "pc")=some (.val (.word pc))) :
 @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) computeJumpdestsStoreAddress=
 some (.val (.word (bitmap+(pc>>> (6 : Nat))*8))) := by
 simp [computeJumpdestsStoreAddress,evalHOLExact,evalListHOLExact,atBitmap,atPc,
  wordOpHOL,wordOp,valueIsWord,valueWord,panOpHOL,wordShiftHOL]

/-- Every outcome of the original jump-destination loop body frames all
words other than its one actual bitmap cell. This includes failed reads,
failed writes and malformed opcode-dependent branches, at every fuel. -/
theorem compute_jumpdests_body_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (bitmap pc watched : BitVec 64)
 (atBitmap : s.locals.lookup (ofString "bm")=some (.val (.word bitmap)))
 (atPc : s.locals.lookup (ofString "pc")=some (.val (.word pc)))
 (separate : watched≠bitmap+(pc>>> (6 : Nat))*8) :
 (evaluateHOLFiniteState s computeJumpdestsLoopBody).2.memory watched=s.memory watched := by
 rw [source_compute_jumpdests_body]
 apply declaration_word_frame
 intro opcode
 let opState:=setVarHOLFinite (ofString "op") opcode s
 apply declaration_word_frame
 intro advance
 let inner:=setVarHOLFinite (ofString "adv") advance opState
 have bm : inner.locals.lookup (ofString "bm")=some (.val (.word bitmap)) := by
  simpa (config:={decide:=true}) [inner,opState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atBitmap
 have counter : inner.locals.lookup (ofString "pc")=some (.val (.word pc)) := by
  simpa (config:={decide:=true}) [inner,opState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPc
 apply seq_readonly_word_frame (s:=inner) _ _ watched (by decide_cbv)
 apply conditional_word_frame
 · apply evaluate_wordStore_memory_frame inner _ _ _ watched
    (eval_compute_jumpdests_store_address inner bitmap pc bm counter)
   · intro parsed evaluated
     exact evaluated_binop_word inner .or _ parsed evaluated
   · exact separate
 · exact congrFun (evaluate_readOnly_memory computeJumpdestsOpcodeRest (by decide_cbv) inner) watched
#print axioms eval_compute_jumpdests_store_address
#print axioms compute_jumpdests_body_word_frame
end InitECandidate.Runtime
