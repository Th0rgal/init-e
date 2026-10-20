import InitECandidate.Runtime.MptInsertKindDispatchWorld
import InitECandidate.Runtime.MptInsertNodeLoad
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A continuing non-null insertion path loads its real kind and restores the
lexical kind local around the complete checked dispatch. -/
theorem mpt_insert_nonnull_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level length oldResult oldNode oldSlot oldLevel : BitVec 64)
 (member : node∈live) (capacity : 32≤size node)
 (nibbles : TrieNibbleRange s key length)
 (keyAligned : key.toNat%8=0) (recordBefore : node.toNat+32≤key.toNat)
 (keyExtent : key.toNat+length.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 21≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertNonNullStep=(none,post)) :
 ∃child slot nextLevel : BitVec 64, AllocatedTrieWorld post live extensions branches size frontier ∧
 TrieNibbleRange post key length ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word slot)) ∧
 post.memory slot=.word child ∧TrieChildSlot post extensions branches slot ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word nextLevel)) ∧
 level.toNat<nextLevel.toNat ∧nextLevel.toNat≤length.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.globals=s.globals ∧
 (∀watched : BitVec 64,watched≠node+8 →watched≠node+16 →watched≠node+24 →post.memory watched=s.memory watched) := by
 have sourceForm : mptInsertNonNullStep=
  .dec (ofString "k") .one (.load .one (mptInsertNodeAddress 0)) mptInsertKindDispatch := by
  simp only [mptInsertNonNullStep,mptInsertKindDispatch,mptInsertLoopStep,sourceFunctionBody,
   Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl
 rw [sourceForm] at run
 obtain ⟨kindValue,output,evaluated,dispatchRun,scope⟩:=evaluate_dec_normal_scope s post (ofString "k") .one _ _ run
 obtain ⟨kind,kindEq,kindField,_⟩:=mpt_insert_node_load_word s node 0 kindValue atNode evaluated
 subst kindValue
 have realKind : s.memory node=.word kind:=by simpa using kindField
 let entered:=setVarHOLFinite (ofString "k") (.val (.word kind)) s
 change evaluateHOLFiniteState entered mptInsertKindDispatch=(none,output) at dispatchRun
 have kept (name : MlS) (different : name≠ofString "k") : entered.locals.lookup name=s.locals.lookup name := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
 have restored (name : MlS) (different : name≠ofString "k") : post.locals.lookup name=output.locals.lookup name := by
  rw [scope]
  exact saved_local_lookup_other output.locals (ofString "k") name _ different
 have outputRunning : output.locals.lookup (ofString "go")≠some (.val (.word (0#64))) := by
  intro stopped;apply running;rw [restored _ (by decide)];exact stopped
 have enteredKind : entered.locals.lookup (ofString "k")=some (.val (.word kind)) := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨child,slot,nextLevel,worldOut,nibblesOut,result,nextNode,valid,nextSlot,backlink,typed,nextLevelAt,advanced,fits,go,globals,frame⟩:=
  mpt_insert_kind_dispatch_world entered output live extensions branches size frontier (world.after_memory_globals rfl rfl)
   node key level length kind oldResult oldNode oldSlot oldLevel member capacity enteredKind realKind
   (nibbles.after_frame rfl rfl rfl) keyAligned recordBefore keyExtent fullDomain
   ((kept _ (by decide)).trans atNode) ((kept _ (by decide)).trans atKey)
   ((kept _ (by decide)).trans atLevel) ((kept _ (by decide)).trans atLength)
   ((kept _ (by decide)).trans atResult) ((kept _ (by decide)).trans atNextNode)
   ((kept _ (by decide)).trans atNextSlot) ((kept _ (by decide)).trans atNextLevel)
   ((kept _ (by decide)).trans zero) inside short code budget outputRunning dispatchRun
 have memoryScope : post.memory=output.memory:=by rw [scope]
 have globalsScope : post.globals=output.globals:=by rw [scope]
 have domainScope : post.memaddrs=output.memaddrs:=by rw [scope]
 have endianScope : post.be=output.be:=by rw [scope]
 refine ⟨child,slot,nextLevel,worldOut.after_memory_globals memoryScope globalsScope,
  nibblesOut.after_frame memoryScope domainScope endianScope,
  (restored _ (by decide)).trans result,(restored _ (by decide)).trans nextNode,valid,
  (restored _ (by decide)).trans nextSlot,?_,?_,(restored _ (by decide)).trans nextLevelAt,advanced,fits,
  (restored _ (by decide)).trans go,globalsScope.trans globals,?_⟩
 · rw [memoryScope];exact backlink
 · exact typed.after_length_frame (by intro node registered;rw [memoryScope])
 · intro watched n8 n16 n24
   rw [memoryScope]
   exact frame watched n8 n16 n24

#print axioms mpt_insert_nonnull_world
end InitECandidate.Runtime
