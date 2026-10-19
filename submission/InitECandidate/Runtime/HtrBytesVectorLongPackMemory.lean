import InitECandidate.Runtime.HtrBytesVectorLongTailMemory
import InitECandidate.Runtime.PackBytesDeclarationReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrBytesVectorLong_pack_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p n heap out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (atLength : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : htrBytesVectorLongPackCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrBytesVectorLongAt 1) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "p"),.var .local (ofString "n")] = some [.val (.word p),.val (.word n)] := by
    simp [evalListHOLExact,evalHOLExact,atInput,atLength]
  rw [source_htrBytesVectorLong_pack] at run
  obtain ⟨ready,output,tail,scope,packed,locals,heapWord,heapCap,relation,installed,memory,remaining⟩ :=
    packBytes_declaration_returned_frame state post (ofString "pk") _ (htrBytesVectorLongAt 2)
      p n heap value htrBytesVectorLongTailCost args hh small heapFits heapAligned code budget run
  obtain ⟨frontier,atFrontier,monotone,aligned,fits⟩ := relation.2 heap hh heapAligned heapFits
  have frontierEq : frontier = allocationEnd heap (packBytesCount n * (32#64)) := by
    rw [heapWord] at atFrontier
    simpa using atFrontier.symm
  subst frontierEq
  have suffix := htrBytesVectorLong_tail_returned_memory ready output pointer accelerator zeroHashes heap (packBytesCount n)
    (allocationEnd heap (packBytesCount n * (32#64))) out mark watched value
    ((relation.1 _ (by decide)).trans atPointer) ((relation.1 _ (by decide)).trans atAccel)
    ((locals _ (by decide)).trans atMark)
    ((relation.1 _ (by decide)).trans atZero) packed heapWord ((locals _ (by decide)).trans atOut)
    outAligned outFits outOutside ((packBytes_lengths n small).2.1.trans (by decide))
    aligned fits (Nat.lt_of_lt_of_le heapBefore monotone) accelAligned accelFits pointerFits
    accelOutside pointerOutside (installed.trans code) remaining tail
  rw [scope]
  exact suffix.trans (memory watched heapBefore)

#print axioms htrBytesVectorLong_pack_returned_memory
end InitECandidate.Runtime
