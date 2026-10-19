import InitECandidate.Runtime.StatelessWitnessListInputFrame
import InitECandidate.Runtime.StatelessWitnessPairStores
import InitECandidate.Runtime.HtabInsertRawFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- The last original witness decoder, its two header stores and return link
the decoded header slices to the returned stateless-input record. -/
theorem stateless_last_witness_decoded {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (P L S H : BitVec 64) (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word S)))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) statelessLastWitnessArguments =
      some [.val (.word P),.val (.word L),.val (.word (256#64)),.val (.word (1024#64))])
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H)))
    (capped : H.toNat ≤ 33806089496) (aligned : H.toNat % 8 = 0)
    (recordBefore : S.toNat + 88 ≤ H.toNat) (inputFits : P.toNat + L.toNat < 2^64)
    (run : evaluateHOLFiniteState s (statelessAt 45) = (some (.returned v),post)) :
    ∃ array count nextHeap : BitVec 64,
      v = .val (.word S) ∧ post.memaddrs (S + (72#64)) ∧ post.memaddrs (S + (80#64)) ∧
      post.memory (S + (72#64)) = .word array ∧ post.memory (S + (80#64)) = .word count ∧
      RlpSliceInputPrefix post array P L count.toNat ∧ count.toNat ≤ L.toNat / 4 ∧ (count = 0 ∨ array = H) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧ H.toNat ≤ nextHeap.toNat ∧
      array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧
      (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → S.toNat + 88 ≤ w.toNat → post.memory w = s.memory w) ∧
      (∀ w : BitVec 64, w.toNat < H.toNat → w ≠ S + (72#64) → w ≠ S + (80#64) →
        post.memory w = s.memory w) := by
  have metadata := evaluateHOLFiniteState_metadata s (statelessAt 45)
  rw [run] at metadata
  have postDomain : post.memaddrs = s.memaddrs := metadata.2.1
  rw [source_stateless_last_witness] at run
  obtain ⟨ready,output,array,count,locals,atPair,installed,domain,decoded,countLe,origin,
    ⟨decodedHeap,decodedBinding,extent⟩,frame,⟨nextHeap,nextBinding,growth,cap,al,other⟩,tail,postGlobals,postMemory⟩ :=
    ret_bytesListDecl_input_frame s post (ofString "hd") statelessLastWitnessArguments (statelessAt 46)
      P L 256 1024 H v code args heap capped aligned inputFits run
  have sameHeap : decodedHeap = nextHeap := by simpa using decodedBinding.symm.trans nextBinding
  rw [sameHeap] at extent
  have readySi := (locals _ (by decide)).trans atSi
  have stores : evaluateHOLFiniteState ready (witnessPairStores (ofString "hd") 72 80 (statelessAt 48)) =
      (some (.returned v),output) := by rw [← source_witness_pair_stores.2.2]; exact tail
  obtain ⟨returned,finalRun,returnedLocals,returnedGlobals,returnedDomain,returnedCode,dom72,dom80,cell72,cell80,kept⟩ :=
    witness_pair_stores_returned ready output (ofString "hd") 72 80 S array count (statelessAt 48) v readySi atPair (by decide) stores
  have atSi' : returned.locals.lookup (ofString "si") = some (.val (.word S)) := by rw [returnedLocals]; exact readySi
  have decoded' : RlpSliceInputPrefix returned array P L count.toNat := by
    apply decoded.after_pair_stores ready returned array count P L (S + (72#64)) (S + (80#64))
      (by have := extent; omega) returnedDomain ?_ kept
    rcases origin with empty | same
    · exact Or.inl empty
    · right
      rw [same,word_add_toNat S 72 (by omega),word_add_toNat S 80 (by omega)]
      omega
  rw [source_stateless_witness_return,evaluateHOLFiniteState_return] at finalRun
  simp only [evalHOLExact,lookupKvarHOLExact,atSi'] at finalRun
  simp [shapeOfHOLExact] at finalRun
  obtain ⟨rfl,rfl⟩ := finalRun
  have memory : post.memory = returned.memory := postMemory
  have domains : post.memaddrs = returned.memaddrs := postDomain.trans (returnedDomain.trans domain).symm
  refine ⟨array,count,nextHeap,rfl,?_,?_,?_,?_,?_,countLe,origin,?_,cap,al,growth,extent,?_,?_,?_⟩
  · rw [domains]; exact dom72
  · rw [domains]; exact dom80
  · rw [memory]; exact cell72
  · rw [memory]; exact cell80
  · intro j inside
    obtain ⟨src,len,entry⟩ := decoded' j inside
    exact ⟨src,len,entry.after_frame returned post array j src len P L domains (congrFun memory _) (congrFun memory _)⟩
  · rw [postGlobals]
    change returned.globals.lookup _ = _
    rw [returnedGlobals]; exact nextBinding

  · intro name different
    rw [postGlobals]
    change returned.globals.lookup _ = _
    rw [returnedGlobals]; exact other name different
  · intro w below above
    rw [memory]
    apply (kept w ?_ ?_).trans (frame w below)
    · intro e
      rw [e] at above
      change S.toNat + 88 ≤ (S + (72#64)).toNat at above
      rw [word_add_toNat S 72 (by omega)] at above
      omega
    · intro e
      rw [e] at above
      change S.toNat + 88 ≤ (S + (80#64)).toNat at above
      rw [word_add_toNat S 80 (by omega)] at above
      omega

  · intro w below h72 h80
    rw [memory]
    exact (kept w h72 h80).trans (frame w below)

#print axioms stateless_last_witness_decoded
end InitECandidate.Runtime
