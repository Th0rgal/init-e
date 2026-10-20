import InitECandidate.Runtime.EncodeHeaderSource
import InitECandidate.Runtime.RlpEncodeBytesFixedCallBound
import InitECandidate.Runtime.RlpPutU256RuntimeBound
import InitECandidate.Runtime.RlpLengthRuntimeBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def firstOf : ProgHOL 64 → ProgHOL 64
 | .seq first _ => first
 | other => other
private def argsOf : ProgHOL 64 → List (ExpHOL 64)
 | .seq (.call _ _ args) _ | .decCall _ _ _ args _ => args
 | _ => []
private def bytesRight (program : ProgHOL 64) : ExpHOL 64 := (argsOf program)[1]?.getD (.const 0)
private def forkCondition : ExpHOL 64 := match firstOf (encodeHeaderAt 44) with
 | .ite condition _ _ => condition
 | _ => .const 0
private def forkYes : ProgHOL 64 := match firstOf (encodeHeaderAt 44) with
 | .ite _ yes _ => yes
 | _ => .skip
private def forkNo : ProgHOL 64 := match firstOf (encodeHeaderAt 44) with
 | .ite _ _ no => no
 | _ => .skip
private def forkAt (i : Nat) := (statelessNext^[i]) forkYes
private def writeDestination : Option (VarKind×MlS) := some (.local,ofString "w")
private def cursor : ExpHOL 64 := .var .local (ofString "p")
private def bytesCost (n : Nat) := rlpEncodeBytesSourceCost n+1
private def wordCost := rlpWriterSourceCost+1
private def forkCost := bytesCost 32+wordCost
private def finalCost := ((2^64-1)+3)+(rlpWriterSourceCost+2)
def encodeHeaderFixedTailCost : Nat := (bytesCost 32)+((bytesCost 8)+((rlpPutU256SourceCost+1)+((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))))))))
private theorem fork_bounded : ProgBounded forkYes forkCost := by
 have last : ProgBounded (forkAt 3) 0 := ProgBounded.straight _ (by decide_cbv)
 have s2 : forkAt 2=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_word") (argsOf (forkAt 2))) (forkAt 3) := rfl
 have b2 : ProgBounded (forkAt 2) wordCost := by
  rw [s2]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.call rlp_encode_word_fun_bounded _ _) last state code (by simpa [wordCost] using budget)
 have s1 : forkAt 1=.seq (firstOf (forkAt 1)) (forkAt 2) := rfl
 have b1 : ProgBounded (forkAt 1) wordCost := by
  rw [s1]
  have first : ProgBounded (firstOf (forkAt 1)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b2 state code (by simpa only [Nat.zero_add] using budget)
 have s0 : forkYes=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_bytes") [cursor,bytesRight (forkAt 0),.const 32]) (forkAt 1) := rfl
 rw [s0]
 intro F state code budget
 exact ProgBounded.seq (ProgBounded.rlpEncodeBytesFixedCall _ _ _ 32 (by decide)) b1 state code budget

/-- The actual header suffix after its variable-length field is uniformly
bounded, including failed reads, malformed arguments and allocation rejection. -/
theorem encode_header_fixed_tail_bounded : ProgBounded (encodeHeaderAt 27) encodeHeaderFixedTailCost := by
 have b49 : ProgBounded (encodeHeaderAt 49) 0 := ProgBounded.straight _ (by decide_cbv)
 have s48 : encodeHeaderAt 48=.seq (.call (some (none,none)) (ofString "rlp_encode_list_header") (argsOf (encodeHeaderAt 48))) (encodeHeaderAt 49) := rfl
 have b48 : ProgBounded (encodeHeaderAt 48) (rlpWriterSourceCost+2) := by
  rw [s48]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.call rlp_encode_list_header_fun_bounded _ _) b49 state code (by simpa only [Nat.add_zero] using budget)
 have s47 : encodeHeaderAt 47=.dec (ofString "start") .one (match encodeHeaderAt 47 with | .dec _ _ e _=>e | _=>.const 0) (encodeHeaderAt 48) := rfl
 have b47 : ProgBounded (encodeHeaderAt 47) (rlpWriterSourceCost+2) := by
  rw [s47];exact ProgBounded.dec _ _ _ b48
 have s46 : encodeHeaderAt 46=.decCall (ofString "hl") .one (ofString "rlp_list_header_len") (argsOf (encodeHeaderAt 46)) (encodeHeaderAt 47) := rfl
 have b46 : ProgBounded (encodeHeaderAt 46) finalCost := by
  rw [s46]
  intro F state code budget
  exact ProgBounded.decCall rlp_list_header_length_fun_bounded _ _ _ b47 state code budget
 have s45 : encodeHeaderAt 45=.dec (ofString "payload_len") .one (match encodeHeaderAt 45 with | .dec _ _ e _=>e | _=>.const 0) (encodeHeaderAt 46) := rfl
 have b45 : ProgBounded (encodeHeaderAt 45) finalCost := by
  rw [s45];exact ProgBounded.dec _ _ _ b46
 have s44 : encodeHeaderAt 44=.seq (.ite forkCondition forkYes forkNo) (encodeHeaderAt 45) := rfl
 have b44 : ProgBounded (encodeHeaderAt 44) (forkCost+finalCost) := by
  rw [s44]
  have noZero : ProgBounded forkNo 0 := ProgBounded.straight _ (by decide_cbv)
  have noBranch : ProgBounded forkNo forkCost := by
   intro F state code budget
   exact ProgBounded.weaken noZero (Nat.zero_le _) state code budget
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.ite _ fork_bounded noBranch) b45 state code budget
 have b43 : ProgBounded (encodeHeaderAt 43) (forkCost+finalCost) := by
  have stage : encodeHeaderAt 43=.seq (firstOf (encodeHeaderAt 43)) (encodeHeaderAt 44) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 43)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b44 state code (by simpa only [Nat.zero_add] using budget)
 have b42 : ProgBounded (encodeHeaderAt 42) ((bytesCost 32)+(forkCost+finalCost)) := by
  have stage : encodeHeaderAt 42=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_bytes") [cursor,bytesRight (encodeHeaderAt 42),.const 32]) (encodeHeaderAt 43) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.rlpEncodeBytesFixedCall _ _ _ 32 (by decide)) b43 state code budget
 have b41 : ProgBounded (encodeHeaderAt 41) ((bytesCost 32)+(forkCost+finalCost)) := by
  have stage : encodeHeaderAt 41=.seq (firstOf (encodeHeaderAt 41)) (encodeHeaderAt 42) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 41)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b42 state code (by simpa only [Nat.zero_add] using budget)
 have b40 : ProgBounded (encodeHeaderAt 40) ((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))) := by
  have stage : encodeHeaderAt 40=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_bytes") [cursor,bytesRight (encodeHeaderAt 40),.const 32]) (encodeHeaderAt 41) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.rlpEncodeBytesFixedCall _ _ _ 32 (by decide)) b41 state code budget
 have b39 : ProgBounded (encodeHeaderAt 39) ((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))) := by
  have stage : encodeHeaderAt 39=.seq (firstOf (encodeHeaderAt 39)) (encodeHeaderAt 40) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 39)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b40 state code (by simpa only [Nat.zero_add] using budget)
 have b38 : ProgBounded (encodeHeaderAt 38) ((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost)))) := by
  have stage : encodeHeaderAt 38=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_word") (argsOf (encodeHeaderAt 38))) (encodeHeaderAt 39) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.call rlp_encode_word_fun_bounded _ _) b39 state code budget
 have b37 : ProgBounded (encodeHeaderAt 37) ((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost)))) := by
  have stage : encodeHeaderAt 37=.seq (firstOf (encodeHeaderAt 37)) (encodeHeaderAt 38) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 37)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b38 state code (by simpa only [Nat.zero_add] using budget)
 have b36 : ProgBounded (encodeHeaderAt 36) ((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))))) := by
  have stage : encodeHeaderAt 36=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_word") (argsOf (encodeHeaderAt 36))) (encodeHeaderAt 37) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.call rlp_encode_word_fun_bounded _ _) b37 state code budget
 have b35 : ProgBounded (encodeHeaderAt 35) ((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))))) := by
  have stage : encodeHeaderAt 35=.seq (firstOf (encodeHeaderAt 35)) (encodeHeaderAt 36) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 35)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b36 state code (by simpa only [Nat.zero_add] using budget)
 have b34 : ProgBounded (encodeHeaderAt 34) ((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost)))))) := by
  have stage : encodeHeaderAt 34=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_bytes") [cursor,bytesRight (encodeHeaderAt 34),.const 32]) (encodeHeaderAt 35) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.rlpEncodeBytesFixedCall _ _ _ 32 (by decide)) b35 state code budget
 have b33 : ProgBounded (encodeHeaderAt 33) ((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost)))))) := by
  have stage : encodeHeaderAt 33=.seq (firstOf (encodeHeaderAt 33)) (encodeHeaderAt 34) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 33)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b34 state code (by simpa only [Nat.zero_add] using budget)
 have b32 : ProgBounded (encodeHeaderAt 32) ((rlpPutU256SourceCost+1)+((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))))))) := by
  have stage : encodeHeaderAt 32=.seq (.call (some (writeDestination,none)) (ofString "rlp_put_u256") (argsOf (encodeHeaderAt 32))) (encodeHeaderAt 33) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.call rlp_put_u256_fun_bounded _ _) b33 state code budget
 have b31 : ProgBounded (encodeHeaderAt 31) ((rlpPutU256SourceCost+1)+((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))))))) := by
  have stage : encodeHeaderAt 31=.seq (firstOf (encodeHeaderAt 31)) (encodeHeaderAt 32) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 31)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b32 state code (by simpa only [Nat.zero_add] using budget)
 have b30 : ProgBounded (encodeHeaderAt 30) ((bytesCost 8)+((rlpPutU256SourceCost+1)+((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost)))))))) := by
  have stage : encodeHeaderAt 30=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_bytes") [cursor,bytesRight (encodeHeaderAt 30),.const 8]) (encodeHeaderAt 31) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.rlpEncodeBytesFixedCall _ _ _ 8 (by decide)) b31 state code budget
 have b29 : ProgBounded (encodeHeaderAt 29) ((bytesCost 8)+((rlpPutU256SourceCost+1)+((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost)))))))) := by
  have stage : encodeHeaderAt 29=.seq (firstOf (encodeHeaderAt 29)) (encodeHeaderAt 30) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 29)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b30 state code (by simpa only [Nat.zero_add] using budget)
 have b28 : ProgBounded (encodeHeaderAt 28) ((bytesCost 32)+((bytesCost 8)+((rlpPutU256SourceCost+1)+((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))))))))) := by
  have stage : encodeHeaderAt 28=.seq (.call (some (writeDestination,none)) (ofString "rlp_encode_bytes") [cursor,bytesRight (encodeHeaderAt 28),.const 32]) (encodeHeaderAt 29) := rfl
  rw [stage]
  intro F state code budget
  exact ProgBounded.seq (ProgBounded.rlpEncodeBytesFixedCall _ _ _ 32 (by decide)) b29 state code budget
 have b27 : ProgBounded (encodeHeaderAt 27) ((bytesCost 32)+((bytesCost 8)+((rlpPutU256SourceCost+1)+((bytesCost 32)+((wordCost)+((wordCost)+((bytesCost 32)+((bytesCost 32)+(forkCost+finalCost))))))))) := by
  have stage : encodeHeaderAt 27=.seq (firstOf (encodeHeaderAt 27)) (encodeHeaderAt 28) := rfl
  rw [stage]
  have first : ProgBounded (firstOf (encodeHeaderAt 27)) 0 := ProgBounded.straight _ (by decide_cbv)
  intro F state code budget
  exact ProgBounded.seq first b28 state code (by simpa only [Nat.zero_add] using budget)
 intro F state code budget
 exact b27 state code budget
#print axioms encode_header_fixed_tail_bounded
end InitECandidate.Runtime
