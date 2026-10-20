import InitECandidate.Runtime.MptInsertExtensionComparisonNormalFrame
import InitECandidate.Runtime.MptInsertExtensionSplitWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original prefix comparison either selects its real matched advance,
or constructs a split world. The splitter budget is earned by the actual
read-only comparison; no future callee fact is assumed. -/
theorem mpt_insert_extension_comparison_split_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node segment segmentLength key length level value valueLength oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (extension : node∈extensions)
 (memoryKey : s.memory (node+32#64)=.word segment)
 (memoryLength : s.memory (node+40#64)=.word segmentLength)
 (levelBound : level.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atSegment : s.locals.lookup (ofString "seg")=some (.val (.word segment)))
 (atSize : s.locals.lookup (ofString "sl")=some (.val (.word segmentLength)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 71≤s.clock)
 (run : evaluateHOLFiniteState s mptInsertExtensionComparison=(none,post)) :
 (∃found : BitVec 64,∃ready output : PanSemStateFiniteExact 64 F,
  found=segmentLength ∧found.toNat≤(length-level).toNat ∧
  ready.memory=s.memory ∧ready.globals=s.globals ∧
  evaluateHOLFiniteState ready mptInsertExtensionAdvance=(none,output) ∧
  post={output with locals:=HolFiniteMapExact.resVarEq output.locals (ofString "pl",s.locals.lookup (ofString "pl"))}) ∨
 ( ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧
 TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠ofString "r"→ other≠ofString "br"→post.locals.lookup other=s.locals.lookup other)) := by
 have remainder : (length-level).toNat≤18 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr levelBound)];omega
 have minimum := BitVec.le_def.mp (wordMin_le_right segmentLength (length-level))
 obtain ⟨found,bodyPost,output,leftBound,rightBound,spent,remaining,memory,globals,domains,endian,installed,selected,scope⟩:=
  mpt_insert_extension_comparison_normal_frame s post segment segmentLength key level length
   atSegment atSize atKey atLevel atLength code (by omega) run
 let ready:=setVarHOLFinite (ofString "pl") (.val (.word found)) {bodyPost with locals:=s.locals}
 have kept (name : MlS) (different : name≠ofString "pl") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
 change evaluateHOLFiniteState ready (if found=segmentLength then _ else _)=(none,output) at selected
 by_cases matched : found=segmentLength
 · exact Or.inl ⟨found,ready,output,matched,rightBound,memory,globals,by simpa only [if_pos matched] using selected,scope⟩
 · apply Or.inr
   have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals memory globals
   have readyKinds : TrieNodeKinds ready live extensions branches:=
    kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current member;exact congrFun memory current)
   have readyPaths : TrieNodePaths ready live extensions branches size frontier:=paths.after_context memory domains endian
   have readyKey : TriePathBuffer ready live size key length frontier:=keyPath.after_context memory domains endian
   have atFound : ready.locals.lookup (ofString "pl")=some (.val (.word found)) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   have strict : found.toNat<segmentLength.toNat := by
    have different : found.toNat≠segmentLength.toNat:=fun h=>matched (BitVec.eq_of_toNat_eq h)
    omega
   obtain ⟨root,larger,newExtensions,newSize,finish,assigned,rootLive,sub,extSub,
    worldOut,kindsOut,pathsOut,transport,locals⟩:=
    mpt_insert_extension_split_normal_world ready output live extensions branches size frontier
     node segment segmentLength key length level found value valueLength oldResult
     readyWorld readyKinds readyPaths readyKey short extension
     (by change bodyPost.memory _=_;rw [memory];exact memoryKey)
     (by change bodyPost.memory _=_;rw [memory];exact memoryLength)
     strict rightBound levelBound
     ((kept _ (by decide)).trans atNode) ((kept _ (by decide)).trans atSegment)
     ((kept _ (by decide)).trans atKey) ((kept _ (by decide)).trans atLength)
     ((kept _ (by decide)).trans atLevel) atFound
     ((kept _ (by decide)).trans atValue) ((kept _ (by decide)).trans atValueLength)
     ((kept _ (by decide)).trans atResult)
     (by intro address bound;change bodyPost.memaddrs address;rw [domains];exact fullDomain address bound)
     (installed.trans code) (by change 51≤bodyPost.clock;omega)
     (by simpa only [if_neg matched] using selected)
   have postMemory : post.memory=output.memory:=by rw [scope]
   have postGlobals : post.globals=output.globals:=by rw [scope]
   have postDomains : post.memaddrs=output.memaddrs:=by rw [scope]
   have postEndian : post.be=output.be:=by rw [scope]
   refine ⟨root,larger,newExtensions,newSize,finish,?_,rootLive,sub,extSub,
    worldOut.after_memory_globals postMemory postGlobals,?_,pathsOut.after_context postMemory postDomains postEndian,?_,?_⟩
   · rw [scope,saved_local_lookup_other output.locals (ofString "pl") (ofString "r") _ (by decide)]
     exact assigned
   · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive
      (by intro current member;rw [postMemory])
   · intro nib len path
     exact (transport nib len (path.after_context memory domains endian)).after_context postMemory postDomains postEndian
   · intro other notR notBr
     by_cases isPl : other=ofString "pl"
     · subst other
       rw [scope]
       cases old : s.locals.lookup (ofString "pl") <;> simp [old,FDOMSUB_HOL,FUPDATE_HOL]
     · rw [scope,saved_local_lookup_other output.locals (ofString "pl") other _ isPl]
       exact (locals other notR notBr).trans (kept other isPl)

#print axioms mpt_insert_extension_comparison_split_world
end InitECandidate.Runtime
