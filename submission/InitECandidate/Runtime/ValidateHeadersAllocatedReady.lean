import InitECandidate.Runtime.ValidateHeadersFirstIndexReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 300000

/-- The actual pair of allocator outcomes establishes all dynamic first-loop
premises. Original input/workspace placement remains explicit at function entry. -/
theorem validate_headers_allocated_ready {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s first post : PanSemStateFiniteExact 64 F)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word e.array)))
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word e.count)))
    (table : RlpSliceInputPrefix s e.array e.input e.inputLength e.count.toNat)
    (inputBefore : e.input.toNat + e.inputLength.toNat ≤ e.hs.toNat)
    (scratch : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word e.scratch)))
    (frame : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word e.frame)))
    (state : s.globals.lookup (ofString "keccak_st") = some (.val (.word e.keccakState)))
    (pad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word e.keccakPad)))
    (arena : ∀ address : BitVec 64, e.frame.toNat ≤ address.toNat → address.toNat < e.ceiling → s.memaddrs address)
    (heapArena : ∀ address : BitVec 64, e.hs.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (hashPointer : e.hashes = allocationEnd e.hs (validateHeadersHsSize e.count))
    (hsAllocation : AllocationDeclarationReady s (ofString "hs") e.hs (validateHeadersHsSize e.count) first)
    (hashAllocation : AllocationDeclarationReady first (ofString "hashes") (allocationEnd e.hs (validateHeadersHsSize e.count))
      (validateHeadersHashesSize e.count) post) :
    ValidateHeadersFirstReady e post ∧ post.code = s.code := by
  obtain ⟨hs,nHash,n,heapGlobal,memory,domain,installed,hsExtent,hashExtent,hashAligned,heapAligned,heapBound,globals⟩ :=
    validate_headers_buffers s first post e.count e.hs e.cap atCount hsAllocation hashAllocation
  have heapMono : e.hs.toNat ≤ (allocationEnd (allocationEnd e.hs (validateHeadersHsSize e.count)) (validateHeadersHashesSize e.count)).toNat := by omega
  have arrayPost : post.locals.lookup (ofString "arr") = some (.val (.word e.array)) := by
    rw [hashAllocation.1,hsAllocation.1]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atArray
  have tablePost : RlpSliceInputPrefix post e.array e.input e.inputLength e.count.toNat := by
    intro slot inside
    obtain ⟨pointer,length,entry⟩ := table slot inside
    exact ⟨pointer,length,entry.after_frame s post e.array slot pointer length e.input e.inputLength domain
      (congrFun memory _) (congrFun memory _)⟩
  refine ⟨⟨allocationEnd (allocationEnd e.hs (validateHeadersHsSize e.count)) (validateHeadersHashesSize e.count),
    arrayPost,n,hs,?_,tablePost,by omega,by have := e.tableBeforeHs; omega,?_,?_,heapGlobal,?_,?_,heapBound,?_,?_⟩,installed⟩
  · rw [hashPointer]; exact nHash
  · rw [globals _ (by decide)]; exact scratch
  · rw [globals _ (by decide)]; exact frame
  · rw [globals _ (by decide)]; exact state
  · rw [globals _ (by decide)]; exact pad
  · intro address lo hi
    rw [domain]
    exact arena address lo hi
  · intro address lo hi
    rw [domain]
    exact heapArena address (by omega) hi

#print axioms validate_headers_allocated_ready
end InitECandidate.Runtime
