import InitECandidate.Runtime.DecodeHeaderFlagWhole
/-!
The legacy (twenty-one field) header from the first field parser.

With `is_current = 0` the zero test at `decodeHeaderAt 56` takes the legacy branch, so the
legacy suffix runs and the fields up to `extra_data` are decoded without the current
fields.  This is the legacy half of the returned-header contract: the returned value is
the record pointer and the generated state root word is readable at `pointer + 32`.

`decode_header_returned_root_from_zero` derives `is_current = 0` from the actual count
guard (`count = 21`), so the entry-level contract does not need this corollary; it exists
for callers that already know they are looking at a legacy header.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Legacy header: `is_current = 0` at the first field parser means the legacy suffix
runs and the returned record carries the generated state root at `pointer + 32`. -/
theorem decode_header_legacy_returned_root {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record : BitVec 64) (ceiling inputLimit : Nat)
    (env : HeaderCarryEnv s array count input inputLength scratch frame record ceiling inputLimit)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : s.locals.lookup (ofString "h") = some (.val (.word record)))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (legacy : s.locals.lookup (ofString "is_current") = some (.val (.word 0#64)))
    (budget : headerWholeBodyCost inputLimit ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeHeaderAt 11) = (some (.returned value),post)) :
    value = .val (.word record) ∧
      (∃ rooted : BitVec 64, post.memory (record + 32#64) = .word rooted) ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (∀ global : MlS, post.globals.lookup global = s.globals.lookup global) ∧
      array.toNat + count.toNat * 16 ≤ record.toNat ∧ record.toNat + 248 < 2^64 := by
  exact decode_header_whole_returned_root_flag s post array count input inputLength scratch frame record 0#64
    ceiling inputLimit env atArray atRecord table legacy (fun nonzero => absurd rfl nonzero) budget value run

#print axioms decode_header_legacy_returned_root
end InitECandidate.Runtime
