import InitECandidate.Runtime.HashMemoryLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure ListHashMemoryLayout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk heap out watched : BitVec 64) : Prop
    extends HashMemoryLayout state sha accelerator zeroHashes heap out watched where
  atChunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunk))
  chunkAligned : chunk.toNat % 8 = 0
  chunkFits : chunk.toNat + 32 ≤ 33806089496
  chunkOutside : watched.toNat < chunk.toNat ∨ chunk.toNat + 32 ≤ watched.toNat

theorem ListHashMemoryLayout.transfer {F G : Type} {state : PanSemStateFiniteExact 64 F} {post : PanSemStateFiniteExact 64 G}
    {sha accelerator zeroHashes chunk heap out watched : BitVec 64}
    (layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched)
    (globals : post.globals = state.globals) (code : post.code = state.code) :
    ListHashMemoryLayout post sha accelerator zeroHashes chunk heap out watched :=
  ⟨layout.toHashMemoryLayout.transfer globals code,(by rw [globals]; exact layout.atChunk),
    layout.chunkAligned,layout.chunkFits,layout.chunkOutside⟩

#print axioms ListHashMemoryLayout.transfer
end InitECandidate.Runtime
