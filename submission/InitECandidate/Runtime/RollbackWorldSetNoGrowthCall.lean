import InitECandidate.Runtime.HashTableSetCallNoGrowthPhysicalFrameSupported
import InitECandidate.Runtime.RollbackWorldPhysicalUpdate
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Nongrowing set retains the complete separated world without a safe plan. -/
theorem RollbackWorld.set_call_no_growth_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : (widths table) = 20 ∨ (widths table) = 32 ∨ (widths table) = 52)
    (ready : HashTableReady (widths table) table keys stride capacity used values order orderPos count bits pointer state)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + (widths table).toNat + 6 ≤ state.clock)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (journal snapshot countWorld : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot countWorld state)
    (registered : table ∈ tables) (separated : RollbackPhysicalSeparated widths tables state)
    (strideBound : stride.toNat ≤ 56) (large : 1 < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      RollbackWorld widths tables journal snapshot countWorld post ∧ RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + (widths table).toNat + 6 ∧ post.clock ≤ state.clock := by
  obtain ⟨nextCount,post,_,run,updated,frame,cost,remaining,locals,globals,code,domain,endian⟩ :=
    ready.set_call_no_growth_with_physical_frame state (widths table) table pointer keys stride capacity used values order orderPos count key value bits supported
      keyAligned sourceWordDomain sourceByteDomain loadFactor budget tableArgument keyArgument valueArgument arguments
  have retained := world.after_physical_update separated table pointer keys stride capacity used values order orderPos count nextCount bits
    registered ready updated strideBound large frame locals globals code domain endian
  exact ⟨post,run,retained.1,retained.2,cost,remaining⟩

#print axioms RollbackWorld.set_call_no_growth_preserves
end InitECandidate.Runtime
