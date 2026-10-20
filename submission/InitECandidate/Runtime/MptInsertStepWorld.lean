import InitECandidate.Runtime.MptInsertSelectedFinishWorld
import InitECandidate.Runtime.PanZeroDecNormalScope
import InitECandidate.Runtime.LocalAssignNormalValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A continuing whole original insertion iteration preserves its concrete
traversal world and strictly advances the indexed-key level. This includes
all four zero declarations, the actual go reset and their lexical restoration. -/
theorem mpt_insert_step_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level length slot root : BitVec 64)
 (nodeValid : node=0 ∨node∈live) (rootValid : root=0 ∨root∈live)
 (capacity : node∈live →32≤size node)
 (nibbles : TrieNibbleRange s key length)
 (keyAligned : key.toNat%8=0) (recordBefore : node∈live →node.toNat+32≤key.toNat)
 (keyExtent : key.toNat+length.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atSlot : s.locals.lookup (ofString "slot")=some (.val (.word slot)))
 (atRoot : s.locals.lookup (ofString "result")=some (.val (.word root)))
 (typedSlot : slot≠0 →TrieChildSlot s extensions branches slot)
 (oldBacklink : slot≠0 →s.memory slot=.word node)
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 21≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertLoopStep=(none,post)) :
 ∃child nextSlot nextLevel nextRoot : BitVec 64, AllocatedTrieWorld post live extensions branches size frontier ∧
 TrieNibbleRange post key length ∧
 post.locals.lookup (ofString "node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "slot")=some (.val (.word nextSlot)) ∧
 post.memory nextSlot=.word child ∧TrieChildSlot post extensions branches nextSlot ∧
 post.locals.lookup (ofString "level")=some (.val (.word nextLevel)) ∧
 level.toNat<nextLevel.toNat ∧nextLevel.toNat≤length.toNat ∧
 post.locals.lookup (ofString "result")=some (.val (.word nextRoot)) ∧(nextRoot=0 ∨nextRoot∈live) ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.globals=s.globals ∧
 (∀name∈([ofString "key",ofString "klen",ofString "vptr",ofString "vlen"] : List MlS),
  post.locals.lookup name=s.locals.lookup name) ∧
 (∀watched : BitVec 64,watched≠node+8→watched≠node+16→watched≠node+24→post.memory watched=s.memory watched) := by
 rw [source_mptInsert_step] at run
 obtain ⟨outR,runR,scopeR⟩:=evaluate_zero_dec_normal_scope s post (ofString "r") _ run
 let first:=setVarHOLFinite (ofString "r") (.val (.word (0#64))) s
 change evaluateHOLFiniteState first _=(none,outR) at runR
 obtain ⟨outN,runN,scopeN⟩:=evaluate_zero_dec_normal_scope first outR (ofString "next_node") _ runR
 let second:=setVarHOLFinite (ofString "next_node") (.val (.word (0#64))) first
 change evaluateHOLFiniteState second _=(none,outN) at runN
 obtain ⟨outS,runS,scopeS⟩:=evaluate_zero_dec_normal_scope second outN (ofString "next_slot") _ runN
 let third:=setVarHOLFinite (ofString "next_slot") (.val (.word (0#64))) second
 change evaluateHOLFiniteState third _=(none,outS) at runS
 obtain ⟨output,runL,scopeL⟩:=evaluate_zero_dec_normal_scope third outS (ofString "next_level") _ runS
 let fourth:=setVarHOLFinite (ofString "next_level") (.val (.word (0#64))) third
 change evaluateHOLFiniteState fourth (.seq (.assign .local (ofString "go") (.const (0#64))) mptInsertSelectedFinish)=(none,output) at runL
 obtain ⟨reset,resetRun,coreRun⟩:=seq_normal_parts runL
 obtain ⟨resetValue,resetEval,resetEq⟩:=evaluate_local_assign_normal_value fourth reset (ofString "go") (.const (0#64)) resetRun
 have resetZero : resetValue=.val (.word (0#64)):=Option.some.inj resetEval.symm
 subst resetValue
 subst reset
 let entered:=setVarHOLFinite (ofString "go") (.val (.word (0#64))) fourth
 change evaluateHOLFiniteState entered mptInsertSelectedFinish=(none,output) at coreRun
 have kept (name : MlS) (a : name≠ofString "r") (b : name≠ofString "next_node")
  (c : name≠ofString "next_slot") (d : name≠ofString "next_level") (e : name≠ofString "go") :
  entered.locals.lookup name=s.locals.lookup name := by
  simp [entered,fourth,third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,a,b,c,d,e,
   Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d,Ne.symm e]
 have restored (name : MlS) (a : name≠ofString "r") (b : name≠ofString "next_node")
  (c : name≠ofString "next_slot") (d : name≠ofString "next_level") :
  post.locals.lookup name=output.locals.lookup name := by
  rw [scopeR,saved_local_lookup_other outR.locals (ofString "r") name _ a]
  rw [scopeN,saved_local_lookup_other outN.locals (ofString "next_node") name _ b]
  rw [scopeS,saved_local_lookup_other outS.locals (ofString "next_slot") name _ c]
  rw [scopeL,saved_local_lookup_other output.locals (ofString "next_level") name _ d]
 have outputRunning : output.locals.lookup (ofString "go")≠some (.val (.word (0#64))) := by
  intro stopped;apply running;rw [restored _ (by decide) (by decide) (by decide) (by decide)];exact stopped
 have zeroLocal (name : MlS) (member : name∈([ofString "r",ofString "next_node",ofString "next_slot",ofString "next_level",ofString "go"] : List MlS)) :
  entered.locals.lookup name=some (.val (.word (0#64))) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;>
   simp (config:={decide:=true}) [entered,fourth,third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨child,nextSlot,nextLevel,nextRoot,worldOut,nibblesOut,nodeAt,valid,slotAt,backlink,typed,levelAt,advanced,fits,rootAt,validRoot,go,globals,localFrame,memoryFrame⟩:=
  mpt_insert_selected_finish_world entered output live extensions branches size frontier (world.after_memory_globals rfl rfl)
   node key level length slot root 0 0 0 0 nodeValid rootValid capacity (nibbles.after_frame rfl rfl rfl)
   keyAligned recordBefore keyExtent fullDomain
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atNode)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atKey)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atLevel)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atLength)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atSlot)
   ((kept _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans atRoot)
   (by intro notZero;exact (typedSlot notZero).after_length_frame (by intro node registered;rfl)) oldBacklink
   (zeroLocal _ (by simp)) (zeroLocal _ (by simp)) (zeroLocal _ (by simp)) (zeroLocal _ (by simp))
   (zeroLocal _ (by simp)) inside short code budget outputRunning coreRun
 have memoryScope : post.memory=output.memory:=by rw [scopeR,scopeN,scopeS,scopeL]
 have globalsScope : post.globals=output.globals:=by rw [scopeR,scopeN,scopeS,scopeL]
 have domainScope : post.memaddrs=output.memaddrs:=by rw [scopeR,scopeN,scopeS,scopeL]
 have endianScope : post.be=output.be:=by rw [scopeR,scopeN,scopeS,scopeL]
 refine ⟨child,nextSlot,nextLevel,nextRoot,worldOut.after_memory_globals memoryScope globalsScope,
  nibblesOut.after_frame memoryScope domainScope endianScope,
  (restored _ (by decide) (by decide) (by decide) (by decide)).trans nodeAt,valid,
  (restored _ (by decide) (by decide) (by decide) (by decide)).trans slotAt,?_,?_,
  (restored _ (by decide) (by decide) (by decide) (by decide)).trans levelAt,advanced,fits,
  (restored _ (by decide) (by decide) (by decide) (by decide)).trans rootAt,validRoot,
  (restored _ (by decide) (by decide) (by decide) (by decide)).trans go,globalsScope.trans globals,?_,?_⟩
 · rw [memoryScope];exact backlink
 · exact typed.after_length_frame (by intro node registered;rw [memoryScope])
 · intro name member
   have different : name≠ofString "r" ∧name≠ofString "next_node" ∧name≠ofString "next_slot" ∧name≠ofString "next_level" ∧name≠ofString "go" := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> decide
   exact (restored name different.1 different.2.1 different.2.2.1 different.2.2.2.1).trans
    ((localFrame name member).trans (kept name different.1 different.2.1 different.2.2.1 different.2.2.2.1 different.2.2.2.2))

 · intro watched n8 n16 n24
   rw [memoryScope]
   exact memoryFrame watched n8 n16 n24

#print axioms mpt_insert_step_world
end InitECandidate.Runtime
