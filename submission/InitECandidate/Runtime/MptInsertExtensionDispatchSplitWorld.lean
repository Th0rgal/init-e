import InitECandidate.Runtime.MptInsertExtensionComparisonSplitWorld
import InitECandidate.Runtime.MptInsertExtensionLoadScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original extension dispatch includes both initial loads,
prefix comparison and constructors. A full match exposes the actual advance;
a mismatch produces a live root with the enlarged world and stored paths. -/
theorem mpt_insert_extension_dispatch_split_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (extension : node∈extensions)
 (levelBound : level.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 71≤s.clock)
 (run : evaluateHOLFiniteState s mptInsertExtensionDispatch=(none,post)) :
 (∃found : BitVec 64,∃ready output : PanSemStateFiniteExact 64 F,
  found.toNat≤(length-level).toNat ∧ready.memory=s.memory ∧ready.globals=s.globals ∧
  evaluateHOLFiniteState ready mptInsertExtensionAdvance=(none,output) ∧
  post.memory=output.memory ∧post.globals=output.globals) ∨
 ( ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧
 TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠ofString "r"→ other≠ofString "br"→post.locals.lookup other=s.locals.lookup other)) := by
 obtain ⟨segment,segmentLength,output,memoryKey,memoryLength,_,_,comparisonRun,scope⟩:=
  mpt_insert_extension_loads_normal_scope s post node atNode run
 let entered:=mptInsertExtensionLoadedState s segment segmentLength
 have kept (name : MlS) (notSegment : name≠ofString "seg") (notLength : name≠ofString "sl") :
  entered.locals.lookup name=s.locals.lookup name :=
  mpt_insert_extension_loaded_local s segment segmentLength name notSegment notLength
 have enteredWorld : AllocatedTrieWorld entered live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have enteredKinds : TrieNodeKinds entered live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;rfl)
 have atSegment : entered.locals.lookup (ofString "seg")=some (.val (.word segment)) := by
  simp (config:={decide:=true}) [entered,mptInsertExtensionLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atSize : entered.locals.lookup (ofString "sl")=some (.val (.word segmentLength)) := by
  simp [entered,mptInsertExtensionLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have casesWorld:=mpt_insert_extension_comparison_split_world entered output live extensions branches size frontier
  node segment segmentLength key length level value valueLength oldResult
  enteredWorld enteredKinds (paths.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl)
  short extension memoryKey memoryLength levelBound
  ((kept _ (by decide) (by decide)).trans atNode) atSegment atSize
  ((kept _ (by decide) (by decide)).trans atKey) ((kept _ (by decide) (by decide)).trans atLength)
  ((kept _ (by decide) (by decide)).trans atLevel) ((kept _ (by decide) (by decide)).trans atValue)
  ((kept _ (by decide) (by decide)).trans atValueLength) ((kept _ (by decide) (by decide)).trans atResult)
  fullDomain code budget comparisonRun
 rcases casesWorld with matched | splitWorld
 · obtain ⟨found,ready,final,_,bound,memory,globals,advance,innerScope⟩:=matched
   exact Or.inl ⟨found,ready,final,bound,memory,globals,advance,by rw [scope,innerScope],by rw [scope,innerScope]⟩
 · apply Or.inr
   obtain ⟨root,larger,newExtensions,newSize,finish,assigned,rootLive,sub,extSub,
    worldOut,kindsOut,pathsOut,transport,locals⟩:=splitWorld
   have memory : post.memory=output.memory:=by rw [scope]
   have globals : post.globals=output.globals:=by rw [scope]
   have domains : post.memaddrs=output.memaddrs:=by rw [scope]
   have endian : post.be=output.be:=by rw [scope]
   have restored (name : MlS) (notSegment : name≠ofString "seg") (notLength : name≠ofString "sl") :
    post.locals.lookup name=output.locals.lookup name := by
    rw [scope,saved_local_lookup_other _ (ofString "seg") name _ notSegment]
    exact saved_local_lookup_other output.locals (ofString "sl") name _ notLength
   refine ⟨root,larger,newExtensions,newSize,finish,(restored _ (by decide) (by decide)).trans assigned,
    rootLive,sub,extSub,worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domains endian,?_,?_⟩
   · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
      (by intro current member;rw [memory])
   · intro nib len path
     exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domains endian
   · intro other notR notBr
     by_cases isSegment : other=ofString "seg"
     · subst other
       rw [scope]
       cases old : s.locals.lookup (ofString "seg") <;> simp [old,FDOMSUB_HOL,FUPDATE_HOL]
     · by_cases isLength : other=ofString "sl"
       · subst other
         rw [scope,saved_local_lookup_other _ (ofString "seg") (ofString "sl") _ (by decide)]
         have oldLength : (setVarHOLFinite (ofString "seg") (.val (.word segment)) s).locals.lookup (ofString "sl")=
          s.locals.lookup (ofString "sl") := by
          simp (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
         rw [oldLength]
         cases old : s.locals.lookup (ofString "sl") <;> simp [old,FDOMSUB_HOL,FUPDATE_HOL]
       · exact (restored other isSegment isLength).trans ((locals other notR notBr).trans (kept other isSegment isLength))

#print axioms mpt_insert_extension_dispatch_split_world
end InitECandidate.Runtime
