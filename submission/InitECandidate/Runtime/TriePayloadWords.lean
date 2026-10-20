import InitECandidate.Runtime.TrieNodePaths
import InitECandidate.Runtime.HashWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Word-valued payload cells, an automatic property of the exact source
memory type. Physical read domains and actual payload values are separate facts. -/
structure TriePayloadWords {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) : Prop where
 leaf : ∀node∈live,node∉extensions→node∉branches→
  (∃value : BitVec 64,s.memory (node+48)=.word value) ∧
  (∃length : BitVec 64,s.memory (node+56)=.word length)
 branch : ∀node∈branches,
  (∃value : BitVec 64,s.memory (node+160)=.word value) ∧
  (∃length : BitVec 64,s.memory (node+168)=.word length)

/-- Source memory cells are words by their datatype, independent of allocation. -/
theorem source_memory_word {F : Type} (s : PanSemStateFiniteExact 64 F) (address : BitVec 64) :
 ∃value : BitVec 64,s.memory address=.word value := by
 cases cell : s.memory address with
 | word value=>exact ⟨value,rfl⟩

/-- No initial payload-typing hypothesis is needed for the source model. -/
theorem TriePayloadWords.of_state {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) : TriePayloadWords s live extensions branches := by
 constructor
 · intro node member nonExt nonBranch
   exact ⟨source_memory_word s (node+48),source_memory_word s (node+56)⟩
 · intro node member
   exact ⟨source_memory_word s (node+160),source_memory_word s (node+168)⟩

theorem TriePayloadWords.empty {F : Type} (s : PanSemStateFiniteExact 64 F) :
 TriePayloadWords s ∅ ∅ ∅ := by
 constructor <;>intro node member <;>exact False.elim member

theorem TriePayloadWords.after_memory {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} (valid : TriePayloadWords s live extensions branches)
 (memory : post.memory=s.memory) : TriePayloadWords post live extensions branches := by
 constructor
 · intro node member nonExt nonBranch
   simpa only [memory] using valid.leaf node member nonExt nonBranch
 · intro node member
   simpa only [memory] using valid.branch node member

/-- A real word store preserves word-valued payloads even if it targets a
payload cell itself; this fact needs no non-aliasing assumption. -/
theorem TriePayloadWords.write_word {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} (valid : TriePayloadWords s live extensions branches)
 (address value : BitVec 64) : TriePayloadWords (sourceWriteWord s address value) live extensions branches := by
 have keep (watched : BitVec 64) (word : ∃old : BitVec 64,s.memory watched=.word old) :
  ∃next : BitVec 64,(sourceWriteWord s address value).memory watched=.word next := by
  by_cases same : watched=address
  · exact ⟨value,by simp [sourceWriteWord,same]⟩
  · obtain ⟨old,atOld⟩:=word
    exact ⟨old,by simpa [sourceWriteWord,same] using atOld⟩
 constructor
 · intro node member nonExt nonBranch
   have old:=valid.leaf node member nonExt nonBranch
   exact ⟨keep _ old.1,keep _ old.2⟩
 · intro node member
   have old:=valid.branch node member
   exact ⟨keep _ old.1,keep _ old.2⟩

#print axioms TriePayloadWords.of_state
#print axioms TriePayloadWords.write_word
#print axioms TriePayloadWords.after_memory
end InitECandidate.Runtime
