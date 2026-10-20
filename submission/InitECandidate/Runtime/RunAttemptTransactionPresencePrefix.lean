import InitECandidate.Runtime.RunAttemptTransactionPresenceReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem source_run_attempt_tx_array : runAttemptAt 13=
 .dec (ofString "txs") .one (.load .one (.op .add [.var .local (ofString "pl"),.const 32])) (runAttemptAt 14) := by rfl
theorem source_run_attempt_tx_count : runAttemptAt 14=
 .dec (ofString "ntx") .one (.load .one (.op .add [.var .local (ofString "pl"),.const 40])) (runAttemptAt 15) := by rfl

/-- An actual one-word record load either aborts or declares the real memory word. -/
theorem run_attempt_payload_word_declaration {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (payload offset : BitVec 64) (tail : ProgHOL 64)
 (atPayload : s.locals.lookup (ofString "pl")=some (.val (.word payload))) :
 Reaches s (.dec name .one (.load .one (.op .add [.var .local (ofString "pl"),.const offset])) tail)
  (fun ready => ∃word : BitVec 64,ready=setVarHOLFinite name (.val (.word word)) s) 0 tail := by
 classical
 apply reaches_dec
 intro value evaluated
 cases cell : s.memory (payload+offset) with
 | word word =>
  have loaded : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
   (.load .one (.op .add [.var .local (ofString "pl"),.const offset])) =
   if s.memaddrs (payload+offset) then some (.val (.word word)) else none := by
   simp [evalHOLExact,evalListHOLExact,atPayload,wordOpHOL,wordOp,valueWord,valueIsWord,isWfShapeExactHOL,memLoadHOLExact,cell]
  rw [loaded] at evaluated
  split at evaluated
  · have same := Option.some.inj evaluated
    subst value
    exact ⟨word,rfl,word,rfl⟩
  · cases evaluated

/-- The real payload-array/count loads and presence loop reach header construction
or terminate within a finite uniform bound, with no readability assumption. -/
theorem run_attempt_tx_presence_prefix {F : Type} (s : PanSemStateFiniteExact 64 F)
 (payload : BitVec 64) (code : s.code=originalRuntimeCode)
 (atPayload : s.locals.lookup (ofString "pl")=some (.val (.word payload)))
 (budget : 2^64-1≤s.clock) :
 Reaches s (runAttemptAt 13)
  (fun post => post.memory=s.memory ∧ post.memaddrs=s.memaddrs ∧ post.code=s.code ∧ post.be=s.be ∧
   (∀key,post.globals.lookup key=s.globals.lookup key) ∧
   (∀key,key≠ofString "i"→key≠ofString "txs"→key≠ofString "ntx"→post.locals.lookup key=s.locals.lookup key))
  (2^64-1) (runAttemptAt 17) := by
 let resultFacts := fun post : PanSemStateFiniteExact 64 F =>
  post.memory=s.memory ∧ post.memaddrs=s.memaddrs ∧ post.code=s.code ∧ post.be=s.be ∧
   (∀key,post.globals.lookup key=s.globals.lookup key) ∧
   (∀key,key≠ofString "i"→key≠ofString "txs"→key≠ofString "ntx"→post.locals.lookup key=s.locals.lookup key)
 change Reaches s (runAttemptAt 13) resultFacts (2^64-1) (runAttemptAt 17)
 have first : Reaches s (runAttemptAt 13)
  (fun ready => ∃array : BitVec 64,ready=setVarHOLFinite (ofString "txs") (.val (.word array)) s) 0 (runAttemptAt 14) := by
  rw [source_run_attempt_tx_array]
  exact run_attempt_payload_word_declaration s (ofString "txs") payload 32 _ atPayload
 have composed := reaches_trans s (runAttemptAt 13) (runAttemptAt 14) (runAttemptAt 17) _ resultFacts 0 (2^64-1)
  first (by
   intro ready facts
   obtain ⟨array,rfl⟩ := facts
   let arrayState := setVarHOLFinite (ofString "txs") (.val (.word array)) s
   have arrayPayload : arrayState.locals.lookup (ofString "pl")=some (.val (.word payload)) := by
    simpa (config:={decide:=true}) [arrayState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atPayload
   have second : Reaches arrayState (runAttemptAt 14)
    (fun next => ∃count : BitVec 64,next=setVarHOLFinite (ofString "ntx") (.val (.word count)) arrayState) 0 (runAttemptAt 15) := by
    rw [source_run_attempt_tx_count]
    exact run_attempt_payload_word_declaration arrayState (ofString "ntx") payload 40 _ arrayPayload
   have tail := reaches_trans arrayState (runAttemptAt 14) (runAttemptAt 15) (runAttemptAt 17) _ resultFacts 0 (2^64-1)
    second (by
     intro next facts
     obtain ⟨count,rfl⟩ := facts
     let countState := setVarHOLFinite (ofString "ntx") (.val (.word count)) arrayState
     have countLocal : countState.locals.lookup (ofString "ntx")=some (.val (.word count)) := by
      simp [countState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
     have checked := run_attempt_tx_presence_reaches countState count code countLocal budget
     apply reaches_mono countState (runAttemptAt 15) (runAttemptAt 17) _ resultFacts _ _ (Nat.le_refl _) _ checked
     intro post retained
     obtain ⟨memory,domain,installed,endian,globals,locals⟩ := retained
     refine ⟨memory,domain,installed,endian,globals,?_⟩
     intro key notIndex notArray notCount
     simpa [countState,arrayState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      Ne.symm notArray,Ne.symm notCount] using locals key notIndex)
   simpa only [Nat.zero_add] using tail)
 simpa only [Nat.zero_add] using composed
#print axioms source_run_attempt_tx_array
#print axioms source_run_attempt_tx_count
#print axioms run_attempt_payload_word_declaration
#print axioms run_attempt_tx_presence_prefix
end InitECandidate.Runtime
