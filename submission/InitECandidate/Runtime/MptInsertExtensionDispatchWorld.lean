import InitECandidate.Runtime.MptInsertExtensionComparisonWorld
import InitECandidate.Runtime.MptInsertExtensionDispatchBound
import InitECandidate.Runtime.MptInsertNodeLoad
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Continuing execution of the real extension dispatch earns the two field
initializers, restores both lexical scopes, and advances through a live backlink. -/
theorem mpt_insert_extension_dispatch_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level length oldResult oldNode oldSlot oldLevel : BitVec 64)
 (registered : node∈extensions)
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
 (code : s.code=originalRuntimeCode) (budget : 20≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertExtensionDispatch=(none,post)) :
 ∃segment child : BitVec 64, AllocatedTrieWorld post live extensions branches size frontier ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word (node+BitVec.ofNat 64 48))) ∧
 post.memory (node+BitVec.ofNat 64 48)=.word child ∧
 TrieChildSlot post extensions branches (node+BitVec.ofNat 64 48) ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word (level+segment))) ∧
 level.toNat<(level+segment).toNat ∧(level+segment).toNat≤length.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.memory=s.memory ∧post.globals=s.globals := by
 rw [source_mptInsert_extension_dispatch] at run
 obtain ⟨segValue,firstOutput,segEval,firstRun,firstScope⟩:=evaluate_dec_normal_scope s post (ofString "seg") .one _ _ run
 obtain ⟨segmentPointer,segEq,_,_⟩:=mpt_insert_node_load_word s node 32 segValue atNode segEval
 subst segValue
 let first:=setVarHOLFinite (ofString "seg") (.val (.word segmentPointer)) s
 change evaluateHOLFiniteState first _=(none,firstOutput) at firstRun
 have firstNode : first.locals.lookup (ofString "node")=some (.val (.word node)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atNode
 obtain ⟨slValue,output,slEval,comparisonRun,secondScope⟩:=evaluate_dec_normal_scope first firstOutput (ofString "sl") .one _ _ firstRun
 obtain ⟨segment,slEq,lengthField,_⟩:=mpt_insert_node_load_word first node 40 slValue firstNode slEval
 subst slValue
 let entered:=setVarHOLFinite (ofString "sl") (.val (.word segment)) first
 change evaluateHOLFiniteState entered mptInsertExtensionComparison=(none,output) at comparisonRun
 have kept (name : MlS) (notSegment : name≠ofString "seg") (notLength : name≠ofString "sl") :
  entered.locals.lookup name=s.locals.lookup name := by
  simp [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,notSegment,notLength,Ne.symm notSegment,Ne.symm notLength]
 have restored (name : MlS) (notSegment : name≠ofString "seg") (notLength : name≠ofString "sl") :
  post.locals.lookup name=output.locals.lookup name := by
  rw [firstScope]
  rw [saved_local_lookup_other firstOutput.locals (ofString "seg") name _ notSegment]
  rw [secondScope]
  exact saved_local_lookup_other output.locals (ofString "sl") name _ notLength
 have outputRunning : output.locals.lookup (ofString "go")≠some (.val (.word (0#64))) := by
  intro stopped;apply running;rw [restored _ (by decide) (by decide)];exact stopped
 have enteredWorld : AllocatedTrieWorld entered live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have atSegmentPointer : entered.locals.lookup (ofString "seg")=some (.val (.word segmentPointer)) := by
  simp (config:={decide:=true}) [entered,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atSegment : entered.locals.lookup (ofString "sl")=some (.val (.word segment)) := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 cases childField : s.memory (node+BitVec.ofNat 64 48) with
 | word child=>
  obtain ⟨outputWorld,result,nextNode,valid,nextSlot,backlink,nextLevel,advanced,bounded,go,memory,globals⟩:=
   mpt_insert_extension_comparison_world entered output live extensions branches size frontier enteredWorld
    node segmentPointer segment key level length child oldResult oldNode oldSlot oldLevel registered
    ((kept _ (by decide) (by decide)).trans atNode) atSegmentPointer atSegment
    ((kept _ (by decide) (by decide)).trans atKey) ((kept _ (by decide) (by decide)).trans atLevel)
    ((kept _ (by decide) (by decide)).trans atLength) ((kept _ (by decide) (by decide)).trans atResult)
    ((kept _ (by decide) (by decide)).trans atNextNode) ((kept _ (by decide) (by decide)).trans atNextSlot)
    ((kept _ (by decide) (by decide)).trans atNextLevel) ((kept _ (by decide) (by decide)).trans zero)
    lengthField childField inside short code budget outputRunning comparisonRun
  have fullMemory : post.memory=s.memory := by rw [firstScope,secondScope];exact memory
  have fullGlobals : post.globals=s.globals := by rw [firstScope,secondScope];exact globals
  have typed : TrieChildSlot post extensions branches (node+BitVec.ofNat 64 48) := by
   obtain ⟨actualLength,loaded,positive⟩:=world.positive node registered
   exact Or.inr ⟨node,registered,actualLength,rfl,(by rw [fullMemory];exact loaded),positive⟩
  exact ⟨segment,child,world.after_memory_globals fullMemory fullGlobals,
   (restored _ (by decide) (by decide)).trans result,(restored _ (by decide) (by decide)).trans nextNode,valid,
   (restored _ (by decide) (by decide)).trans nextSlot,(by rw [fullMemory];exact childField),typed,
   (restored _ (by decide) (by decide)).trans nextLevel,advanced,bounded,
   (restored _ (by decide) (by decide)).trans go,fullMemory,fullGlobals⟩

#print axioms mpt_insert_extension_dispatch_world
end InitECandidate.Runtime
