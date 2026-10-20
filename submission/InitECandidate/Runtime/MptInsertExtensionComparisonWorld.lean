import InitECandidate.Runtime.MptInsertExtensionAdvanceNormal
import InitECandidate.Runtime.MptInsertTerminalGo
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A continuing normal original prefix comparison must match the entire
positive extension. Its actual readonly call and actual advance preserve the
allocated trie world and prepare a live child with its real backlink. -/
theorem mpt_insert_extension_comparison_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node segmentPointer segment key level length child oldResult oldNode oldSlot oldLevel : BitVec 64)
 (registered : node∈extensions)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atSegmentPointer : s.locals.lookup (ofString "seg")=some (.val (.word segmentPointer)))
 (atSegment : s.locals.lookup (ofString "sl")=some (.val (.word segment)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (lengthField : s.memory (node+BitVec.ofNat 64 40)=.word segment)
 (childField : s.memory (node+BitVec.ofNat 64 48)=.word child)
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 20≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertExtensionComparison=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word (node+BitVec.ofNat 64 48))) ∧
 post.memory (node+BitVec.ofNat 64 48)=.word child ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word (level+segment))) ∧
 level.toNat<(level+segment).toNat ∧(level+segment).toNat≤length.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.memory=s.memory ∧post.globals=s.globals := by
 have remaining : (length-level).toNat≤18 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)];omega
 have minimum := BitVec.le_def.mp (wordMin_le_right segment (length-level))
 obtain ⟨found,ready,output,leftBound,fits,locals,memory,globals,tail,matchedAdvance,postEq⟩:=
  evaluate_mptInsert_extension_comparison s post segmentPointer segment key level length atSegmentPointer atSegment
   atKey atLevel atLength inside code (by omega) run
 let entered:=setVarHOLFinite (ofString "pl") (.val (.word found)) ready
 have kept (name : MlS) (different : name≠ofString "pl") : entered.locals.lookup name=s.locals.lookup name := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different,locals]
 have restored (name : MlS) (different : name≠ofString "pl") : post.locals.lookup name=output.locals.lookup name := by
  rw [postEq]
  exact saved_local_lookup_other output.locals (ofString "pl") name _ different
 have outputRunning : output.locals.lookup (ofString "go")≠some (.val (.word (0#64))) := by
  intro stopped
  apply running
  rw [restored _ (by decide)]
  exact stopped
 have atPrefix : entered.locals.lookup (ofString "pl")=some (.val (.word found)) := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨same,advanceRun⟩:=mpt_insert_extension_continuation_running entered output found segment atPrefix
  ((kept _ (by decide)).trans atSegment) ((kept _ (by decide)).trans zero) outputRunning tail
 subst found
 have enteredWorld : AllocatedTrieWorld entered live extensions branches size frontier:=
  (world.after_memory_globals memory globals).after_memory_globals rfl rfl
 have enteredLength : entered.memory (node+BitVec.ofNat 64 40)=.word segment := by
  change ready.memory _=_;rw [memory];exact lengthField
 have enteredChild : entered.memory (node+BitVec.ofNat 64 48)=.word child := by
  change ready.memory _=_;rw [memory];exact childField
 obtain ⟨outputWorld,result,nextNode,valid,nextSlot,nextLevel,advanced,bounded,go,memoryOut,globalsOut⟩:=
  mpt_insert_extension_advance_normal_world entered output live extensions branches size frontier enteredWorld
   node level segment child length oldResult oldNode oldSlot oldLevel 0 registered
   ((kept _ (by decide)).trans atNode) ((kept _ (by decide)).trans atLevel) atPrefix enteredLength enteredChild fits
   ((kept _ (by decide)).trans atResult) ((kept _ (by decide)).trans atNextNode)
   ((kept _ (by decide)).trans atNextSlot) ((kept _ (by decide)).trans atNextLevel)
   ((kept _ (by decide)).trans zero) advanceRun
 have fullMemory : post.memory=s.memory := by rw [postEq];exact memoryOut.trans memory
 have fullGlobals : post.globals=s.globals := by rw [postEq];exact globalsOut.trans globals
 refine ⟨world.after_memory_globals fullMemory fullGlobals,
  (restored _ (by decide)).trans result,(restored _ (by decide)).trans nextNode,valid,
  (restored _ (by decide)).trans nextSlot,?_,(restored _ (by decide)).trans nextLevel,advanced,bounded,
  (restored _ (by decide)).trans go,fullMemory,fullGlobals⟩
 rw [fullMemory];exact childField

#print axioms mpt_insert_extension_comparison_world
end InitECandidate.Runtime
