import InitECandidate.Runtime.RunAttemptTransactionPresenceBound
import InitECandidate.Runtime.RunBoundedSeqReach
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanWhileNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem source_run_attempt_tx_presence_index : runAttemptAt 15=
 .dec (ofString "i") .one (.const 0) (runAttemptAt 16) := by rfl

/-- The actual presence check reaches header construction or terminates; it
keeps memory, globals, domain/code and every caller local except its loop index. -/
theorem run_attempt_tx_presence_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (count : BitVec 64) (code : s.code=originalRuntimeCode)
 (atCount : s.locals.lookup (ofString "ntx")=some (.val (.word count)))
 (budget : 2^64-1≤s.clock) :
 Reaches s (runAttemptAt 15)
  (fun post => post.memory=s.memory ∧ post.memaddrs=s.memaddrs ∧ post.code=s.code ∧ post.be=s.be ∧
   (∀key,post.globals.lookup key=s.globals.lookup key) ∧
   (∀key,key≠ofString "i"→post.locals.lookup key=s.locals.lookup key))
  (2^64-1) (runAttemptAt 17) := by
 let resultFacts := fun post : PanSemStateFiniteExact 64 F =>
  post.memory=s.memory ∧ post.memaddrs=s.memaddrs ∧ post.code=s.code ∧ post.be=s.be ∧
   (∀key,post.globals.lookup key=s.globals.lookup key) ∧
   (∀key,key≠ofString "i"→post.locals.lookup key=s.locals.lookup key)
 change Reaches s (runAttemptAt 15) resultFacts (2^64-1) (runAttemptAt 17)
 have initial : Reaches s (runAttemptAt 15)
  (fun ready => ready=setVarHOLFinite (ofString "i") (.val (.word (0#64))) s) 0 (runAttemptAt 16) := by
  rw [source_run_attempt_tx_presence_index]
  apply reaches_dec
  intro value evaluated
  have same : (.val (.word (0#64)) : ValueHOL 64)=value := Option.some.inj evaluated
  subst value
  exact ⟨0,rfl,rfl⟩
 have composed := reaches_trans s (runAttemptAt 15) (runAttemptAt 16) (runAttemptAt 17) _ resultFacts 0 (2^64-1)
  initial (by
   intro ready same
   subst ready
   let entered := setVarHOLFinite (ofString "i") (.val (.word (0#64))) s
   have index : entered.locals.lookup (ofString "i")=some (.val (.word (0#64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   have limit : entered.locals.lookup (ofString "ntx")=some (.val (.word count)) := by
    simpa (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCount
   have bounded := runBounded_run_attempt_tx_presence entered count code index limit budget
   rw [source_run_attempt_tx_presence_loop]
   apply runBounded_seq_reaches entered runAttemptTxPresenceLoop (runAttemptAt 17) _ _ bounded
   · intro value
     exact evaluate_while_no_return _ _ (fun state value => evaluate_noDirectReturn _ rfl state value) entered value
   · intro post run
     have memory := evaluate_readOnly_memory runAttemptTxPresenceLoop rfl entered
     have metadata := evaluateHOLFiniteState_metadata entered runAttemptTxPresenceLoop
     rw [run] at memory metadata
     refine ⟨memory,metadata.2.1,metadata.1,metadata.2.2.1,?_,?_⟩
     · intro key
       have global := evaluate_avoidsGlobalAssignment key runAttemptTxPresenceLoop rfl entered
       rw [run] at global
       exact global
     · intro key different
       have avoidsIndex : avoidsLocal key runAttemptTxPresenceLoop=true := by
        change (!(ofString "i"==key))=true
        simp [Ne.symm different]
       have localFrame := evaluate_avoidsLocal_flowing key runAttemptTxPresenceLoop avoidsIndex entered
        (by rw [run];exact Or.inl rfl)
       rw [run] at localFrame
       simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different] using localFrame)
 simpa only [Nat.zero_add] using composed
#print axioms source_run_attempt_tx_presence_index
#print axioms run_attempt_tx_presence_reaches
end InitECandidate.Runtime
