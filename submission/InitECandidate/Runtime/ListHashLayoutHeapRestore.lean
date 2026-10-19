import InitECandidate.Runtime.ListHashMemoryLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Restore the saved heap frontier in a hash memory layout after a real
release, while retaining the unchanged helper workspaces. -/
theorem ListHashMemoryLayout.after_heap_restore {F G : Type}
    {state : PanSemStateFiniteExact 64 F} {post : PanSemStateFiniteExact 64 G}
    {sha accelerator zeroHashes chunk heap restored out watched : BitVec 64}
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (globals : post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word restored)) state).globals)
    (code : post.code = state.code)
    (aligned : restored.toNat % 8 = 0) (bounded : restored.toNat ≤ 33806089496)
    (before : watched.toNat < restored.toNat) :
    ListHashMemoryLayout post sha accelerator zeroHashes chunk restored out watched := by
  have keep (key : MlS) (different : key ≠ ofString "heap_ptr") : post.globals.lookup key = state.globals.lookup key := by
    rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  exact {
    atSha := (keep _ (by decide)).trans layout.atSha
    atAccel := (keep _ (by decide)).trans layout.atAccel
    atZero := (keep _ (by decide)).trans layout.atZero
    atChunk := (keep _ (by decide)).trans layout.atChunk
    atHeap := by rw [globals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    outAligned := layout.outAligned
    outFits := layout.outFits
    outOutside := layout.outOutside
    heapAligned := aligned
    heapFits := bounded
    heapBefore := before
    accelAligned := layout.accelAligned
    accelFits := layout.accelFits
    shaFits := layout.shaFits
    accelOutside := layout.accelOutside
    shaOutside := layout.shaOutside
    code := code.trans layout.code
    chunkAligned := layout.chunkAligned
    chunkFits := layout.chunkFits
    chunkOutside := layout.chunkOutside }

#print axioms ListHashMemoryLayout.after_heap_restore
end InitECandidate.Runtime
