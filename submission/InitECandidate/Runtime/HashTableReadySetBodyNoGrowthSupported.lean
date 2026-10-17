import InitECandidate.Runtime.HashTableSetNoGrowthSupported
import InitECandidate.Runtime.HashTableReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_body_no_growth_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (initial : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : 3 * capacity.toNat + keyLength.toNat + 5 ≤ state.clock)
    :
    ∃ nextCount : BitVec 64, ∃ post, (nextCount = count ∨ nextCount = count + 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits pointer post ∧
      state.clock ≤ post.clock + 3 * capacity.toNat + keyLength.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨nextCount,post,counts,run,arrays,words,reverse,entries,linked,cost,remaining,globals,code,domain,endian⟩ :=
    initial.live.arrays.set_no_growth_supported state keyLength table keys stride capacity used values order orderPos count key value bits supported
      tableLocal keyLocal valueLocal keyAligned sourceWordDomain sourceByteDomain loadFactor budget
      initial.valuesWord initial.reverse initial.live.entries initial.linked initial.ordering
  exact ⟨nextCount,post,counts,run,⟨⟨arrays,entries,initial.live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    words,reverse,linked,initial.ordering⟩,cost,remaining,globals,code,domain,endian⟩

#print axioms HashTableReady.set_body_no_growth_supported
end InitECandidate.Runtime
