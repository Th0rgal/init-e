import InitECandidate.Runtime.HashTableSetCallNoGrowthOrder32
import InitECandidate.Runtime.HashTableHeapFrontier32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_call_no_growth_frontier {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + 38 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state)
    (pointer : BitVec 64) (frontier : HashTableHeapFrontier32 orderPos capacity pointer state) :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_set")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos nextCount bits post ∧
      HashOrderEntriesBound order capacity nextCount post ∧
      HashTableHeapFrontier32 orderPos capacity pointer post ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + 38 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨nextCount,post,counts,run,valid,orderValid,cost,remaining,locals,globals,code,addresses,endian⟩ :=
    invariant.set_call_no_growth_order state table keys stride capacity used values order orderPos count key value bits
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain loadFactor budget entries
  exact ⟨nextCount,post,counts,run,valid,orderValid,frontier.after_globals state post orderPos capacity pointer globals,
    cost,remaining,locals,globals,code,addresses,endian⟩

#print axioms HashTableArraysInvariant32.set_call_no_growth_frontier
end InitECandidate.Runtime
