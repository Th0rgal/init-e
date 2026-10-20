import InitECandidate.Runtime.TriePathBuffer
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual new-leaf declaration preserves any older path, and earns its
separation from the new record using the checked allocator result. -/
theorem NodeNewLeafDeclarationReady.path_buffer {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length valuePointer valueLength key keyLength : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (path : TriePathBuffer s live size key keyLength pointer) :
 TriePathBuffer post (insert pointer live) (Function.update size pointer 64) key keyLength (allocationEnd pointer 64) :=
 path.after_new_record world 64 (by have:=ready.extent;omega) ready.memory ready.domain ready.endian

/-- The actual new-branch declaration retains old path bytes and separates
their containing cells from its freshly initialized 176-byte record. -/
theorem NodeNewBranchDeclarationReady.path_buffer {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer key keyLength : BitVec 64} {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (path : TriePathBuffer s live size key keyLength pointer) :
 TriePathBuffer post (insert pointer live) (Function.update size pointer 176) key keyLength (allocationEnd pointer 176) :=
 path.after_new_record world 176 (by have:=ready.extent;omega) ready.memory ready.domain ready.endian

/-- The actual new-extension declaration also preserves path slices; no
alignment premise on the slice pointer or callee-frame callback is needed. -/
theorem NodeNewExtDeclarationReady.path_buffer {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child key keyLength : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (path : TriePathBuffer s live size key keyLength pointer) :
 TriePathBuffer post (insert pointer live) (Function.update size pointer 56) key keyLength (allocationEnd pointer 56) :=
 path.after_new_record world 56 (by have:=ready.extent;omega) ready.memory ready.domain ready.endian

#print axioms NodeNewLeafDeclarationReady.path_buffer
#print axioms NodeNewBranchDeclarationReady.path_buffer
#print axioms NodeNewExtDeclarationReady.path_buffer
end InitECandidate.Runtime
