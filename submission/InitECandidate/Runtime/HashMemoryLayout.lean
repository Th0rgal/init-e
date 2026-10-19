import InitECandidate.Runtime.RecordHashBodyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure HashMemoryLayout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap out watched : BitVec 64) : Prop where
  atSha : state.globals.lookup (ofString "sha_st") = some (.val (.word sha))
  atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator))
  atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes))
  atHeap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap))
  outAligned : out.toNat % 8 = 0
  outFits : out.toNat + 32 ≤ 33806089496
  outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat
  heapAligned : heap.toNat % 8 = 0
  heapFits : heap.toNat ≤ 33806089496
  heapBefore : watched.toNat < heap.toNat
  accelAligned : accelerator.toNat % 8 = 0
  accelFits : accelerator.toNat + 96 ≤ 33806089496
  shaFits : sha.toNat + 64 ≤ 33806089496
  accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat
  shaOutside : watched.toNat < sha.toNat ∨ sha.toNat + 64 ≤ watched.toNat
  code : state.code = originalRuntimeCode

theorem HashMemoryLayout.transfer {F G : Type} {state : PanSemStateFiniteExact 64 F} {post : PanSemStateFiniteExact 64 G}
    {sha accelerator zeroHashes heap out watched : BitVec 64}
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (globals : post.globals = state.globals) (code : post.code = state.code) :
    HashMemoryLayout post sha accelerator zeroHashes heap out watched :=
  ⟨(by rw [globals]; exact layout.atSha),(by rw [globals]; exact layout.atAccel),
    (by rw [globals]; exact layout.atZero),(by rw [globals]; exact layout.atHeap),
    layout.outAligned,layout.outFits,layout.outOutside,layout.heapAligned,layout.heapFits,layout.heapBefore,
    layout.accelAligned,layout.accelFits,layout.shaFits,layout.accelOutside,layout.shaOutside,code.trans layout.code⟩

theorem HashMemoryLayout.recordEntry {F : Type} {state : PanSemStateFiniteExact 64 F}
    {sha accelerator zeroHashes input heap out watched : BitVec 64}
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atInput : state.locals.lookup (ofString "e") = some (.val (.word input)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out))) :
    RecordHashEntryContext state sha accelerator zeroHashes input heap out watched :=
  ⟨atInput,atOut,layout.atSha,layout.atAccel,layout.atZero,layout.atHeap,
    layout.outAligned,layout.outFits,layout.outOutside,layout.heapAligned,layout.heapFits,layout.heapBefore,
    layout.accelAligned,layout.accelFits,layout.shaFits,layout.accelOutside,layout.shaOutside,layout.code⟩

#print axioms HashMemoryLayout.transfer
#print axioms HashMemoryLayout.recordEntry
end InitECandidate.Runtime
