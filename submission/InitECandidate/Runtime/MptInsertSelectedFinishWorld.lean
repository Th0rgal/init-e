import InitECandidate.Runtime.MptInsertNonNullLocalFrame
import InitECandidate.Runtime.TrieChildSlotCacheFrame
import InitECandidate.Runtime.MptInsertFinishWorld
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertSelectedFinish : ProgHOL 64 :=
 .seq (.ite (.cmp .equal (.var .local (ofString "node")) (.const (0#64)))
  mptInsertNewLeafCall mptInsertNonNullStep) mptInsertFinish

/-- Continuing normal execution of the actual node choice and finishing suffix
preserves the allocated trie and key, installs a typed live backlink, and
strictly advances the traversal level. -/
theorem mpt_insert_selected_finish_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node key level length slot root oldResult oldNode oldSlot oldLevel : BitVec 64)
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
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (zero : s.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (inside : level.toNat≤length.toNat) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 21≤s.clock)
 (running : post.locals.lookup (ofString "go")≠some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertSelectedFinish=(none,post)) :
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
  post.locals.lookup name=s.locals.lookup name) := by
 unfold mptInsertSelectedFinish at run
 obtain ⟨selected,selectedRun,finishRun⟩:=seq_normal_parts run
 have finishGo : post.locals.lookup (ofString "go")=selected.locals.lookup (ofString "go") := by
  have avoids : avoidsLocal (ofString "go") mptInsertFinish=true := by
   rw [source_mptInsert_finish,source_mptInsert_commit,source_mptInsert_advance];decide
  have kept:=evaluate_avoidsLocal_flowing (ofString "go") mptInsertFinish avoids selected
  rw [finishRun] at kept
  exact kept (Or.inl rfl)
 have selectedRunning : selected.locals.lookup (ofString "go")≠some (.val (.word (0#64))) := by
  intro stopped;apply running;rw [finishGo];exact stopped
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "node")) (.const (0#64)))=
  some (.val (.word (if node=0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact,atNode,Compiler.Encoders.Asm.wordCmpHOL]
 rw [evaluateHOLFiniteState_ite,cmp] at selectedRun
 have nonzero : node≠0#64 := by
  intro null
  have actual:=selectedRun
  simp only [if_pos null,show (1#64)≠0 from by decide,if_false] at actual
  exact selectedRunning (mpt_insert_new_leaf_normal_stopped s selected zero actual)
 simp only [if_neg nonzero] at selectedRun
 change evaluateHOLFiniteState s mptInsertNonNullStep=(none,selected) at selectedRun
 have member : node∈live:=nodeValid.resolve_left nonzero
 obtain ⟨child,nextSlot,nextLevel,selectedWorld,selectedNibbles,result,nextNode,valid,nextSlotAt,nextBacklink,prepared,nextLevelAt,advanced,fits,go,globals,frame⟩:=
  mpt_insert_nonnull_world s selected live extensions branches size frontier world node key level length oldResult oldNode oldSlot oldLevel
   member (capacity member) nibbles keyAligned (recordBefore member) keyExtent fullDomain atNode atKey atLevel atLength
   atResult atNextNode atNextSlot atNextLevel zero inside short code budget selectedRunning selectedRun
 have locals:=mpt_insert_nonnull_local_frame s selected selectedRun
 have kept (name : MlS) (member : name∈mptInsertStableNames) : selected.locals.lookup name=s.locals.lookup name:=locals name member
 have metadata:=evaluateHOLFiniteState_metadata s mptInsertNonNullStep
 rw [selectedRun] at metadata
 have oldTyped (notZero : slot≠0) : TrieChildSlot selected extensions branches slot :=
  (typedSlot notZero).after_cache_frame s selected live extensions branches size world.layout slot node member (capacity member) frame
 have backlink (notZero : slot≠0) : selected.memory slot=.word node := by
  have separate (offset : Nat) (small : offset<32) : slot≠node+BitVec.ofNat 64 offset :=
   (typedSlot notZero).metadata_separate s live extensions branches size world.layout slot node member (capacity member) offset small
  rw [frame slot (separate 8 (by decide)) (separate 16 (by decide)) (separate 24 (by decide))]
  exact oldBacklink notZero
 obtain ⟨output,nextRoot,actualFinish,outputWorld,outputNibbles,rootAt,validRoot,nodeAt,slotAt,typed,backlinkOut,levelAt,goOut,memory,globalsOut,_,frameOut⟩:=
  evaluate_mptInsert_finish_world selected live extensions branches size frontier selectedWorld node slot level root child nextSlot nextLevel key length
   ((kept _ (by simp [mptInsertStableNames])).trans atNode) ((kept _ (by simp [mptInsertStableNames])).trans atSlot)
   ((kept _ (by simp [mptInsertStableNames])).trans atLevel) result ((kept _ (by simp [mptInsertStableNames])).trans atRoot)
   nextNode nextSlotAt nextLevelAt go member rootValid valid nextBacklink prepared oldTyped backlink selectedNibbles
   (by intro address small;rw [metadata.2.1];exact fullDomain address small) (metadata.1.trans code)
 have same : output=post:=(Prod.mk.inj (actualFinish.symm.trans finishRun)).2
 subst output
 refine ⟨child,nextSlot,nextLevel,nextRoot,outputWorld,outputNibbles,nodeAt,valid,slotAt,backlinkOut,typed,levelAt,
  advanced,fits,rootAt,validRoot,goOut,globalsOut.trans globals,?_⟩
 intro name member
 have different : name≠ofString "result" ∧name≠ofString "node" ∧name≠ofString "slot" ∧name≠ofString "level" := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> decide
 have stable : name∈mptInsertStableNames := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> simp [mptInsertStableNames]
 exact (frameOut name different.1 different.2.1 different.2.2.1 different.2.2.2).trans (kept name stable)

#print axioms mpt_insert_selected_finish_world
end InitECandidate.Runtime
