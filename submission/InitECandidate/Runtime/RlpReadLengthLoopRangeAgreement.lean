import InitECandidate.Runtime.RlpReadLengthNormalTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normally completed original reader loops compute the same accumulator
from equal input registers and byte reads, independently of clocks/globals. -/
theorem rlpReadLength_loop_range_agreement {F : Type}
    (first second firstPost secondPost : PanSemStateFiniteExact 64 F)
    (pointer index value length : BitVec 64)
    (firstPointer : first.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (firstIndex : first.locals.lookup (ofString "i") = some (.val (.word index)))
    (firstValue : first.locals.lookup (ofString "v") = some (.val (.word value)))
    (firstLength : first.locals.lookup (ofString "n") = some (.val (.word length)))
    (secondPointer : second.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (secondIndex : second.locals.lookup (ofString "i") = some (.val (.word index)))
    (secondValue : second.locals.lookup (ofString "v") = some (.val (.word value)))
    (secondLength : second.locals.lookup (ofString "n") = some (.val (.word length)))
    (reads : ∀ offset : BitVec 64, offset.toNat < length.toNat → @panMemLoadByteHOL 64 _ first.memory first.memaddrs
        (fun address => Classical.propDecidable (first.memaddrs address)) first.be (pointer + offset) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs
        (fun address => Classical.propDecidable (second.memaddrs address)) second.be (pointer + offset))
    (firstRun : evaluateHOLFiniteState first rlpReadLengthLoop = (none,firstPost))
    (secondRun : evaluateHOLFiniteState second rlpReadLengthLoop = (none,secondPost)) :
    firstPost.locals.lookup (ofString "v") = secondPost.locals.lookup (ofString "v") := by
  have visit : ∀ remaining : Nat, ∀ (first second firstPost secondPost : PanSemStateFiniteExact 64 F)
      (pointer index value length : BitVec 64), length.toNat - index.toNat = remaining →
      first.locals.lookup (ofString "p") = some (.val (.word pointer)) →
      first.locals.lookup (ofString "i") = some (.val (.word index)) →
      first.locals.lookup (ofString "v") = some (.val (.word value)) →
      first.locals.lookup (ofString "n") = some (.val (.word length)) →
      second.locals.lookup (ofString "p") = some (.val (.word pointer)) →
      second.locals.lookup (ofString "i") = some (.val (.word index)) →
      second.locals.lookup (ofString "v") = some (.val (.word value)) →
      second.locals.lookup (ofString "n") = some (.val (.word length)) →
      (∀ offset : BitVec 64, offset.toNat < length.toNat → @panMemLoadByteHOL 64 _ first.memory first.memaddrs
          (fun address => Classical.propDecidable (first.memaddrs address)) first.be (pointer + offset) =
        @panMemLoadByteHOL 64 _ second.memory second.memaddrs
          (fun address => Classical.propDecidable (second.memaddrs address)) second.be (pointer + offset)) →
      evaluateHOLFiniteState first rlpReadLengthLoop = (none,firstPost) →
      evaluateHOLFiniteState second rlpReadLengthLoop = (none,secondPost) →
      firstPost.locals.lookup (ofString "v") = secondPost.locals.lookup (ofString "v") := by
    intro remaining
    induction remaining using Nat.strongRecOn with
    | ind remaining ih =>
      intro first second firstPost secondPost pointer index value length distance p1 i1 v1 n1 p2 i2 v2 n2 reads run1 run2
      by_cases enabled : index.toNat < length.toNat
      · obtain ⟨byte1,loaded1,tail1⟩ := rlpReadLength_loop_normal_tail first firstPost pointer index value length p1 i1 v1 n1 enabled run1
        obtain ⟨byte2,loaded2,tail2⟩ := rlpReadLength_loop_normal_tail second secondPost pointer index value length p2 i2 v2 n2 enabled run2
        have equal : byte1 = byte2 := Option.some.inj (loaded1.symm.trans ((reads index enabled).trans loaded2))
        subst byte2
        let next1 := rlpReadLengthStepState (decClockHOLFinite first) index value byte1
        let next2 := rlpReadLengthStepState (decClockHOLFinite second) index value byte1
        let nextValue : BitVec 64 := (value <<< (8 : Nat)) ||| BitVec.ofNat 64 byte1.toNat
        have nextIndex : (index + 1).toNat = index.toNat + 1 := by
          rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2^64; have bound := length.isLt; omega)]
          rfl
        apply ih (length.toNat - (index + 1).toNat) (by omega) next1 next2 firstPost secondPost pointer (index + 1) nextValue length rfl
        · simpa [next1,rlpReadLengthStepState,decClockHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
            show ofString "i" ≠ ofString "p" by decide,show ofString "v" ≠ ofString "p" by decide] using p1
        · exact (rlpReadLengthStepState_registers _ index value byte1).1
        · exact (rlpReadLengthStepState_registers _ index value byte1).2
        · simpa [next1,rlpReadLengthStepState,decClockHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
            show ofString "i" ≠ ofString "n" by decide,show ofString "v" ≠ ofString "n" by decide] using n1
        · simpa [next2,rlpReadLengthStepState,decClockHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
            show ofString "i" ≠ ofString "p" by decide,show ofString "v" ≠ ofString "p" by decide] using p2
        · exact (rlpReadLengthStepState_registers _ index value byte1).1
        · exact (rlpReadLengthStepState_registers _ index value byte1).2
        · simpa [next2,rlpReadLengthStepState,decClockHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
            show ofString "i" ≠ ofString "n" by decide,show ofString "v" ≠ ofString "n" by decide] using n2
        · exact reads
        · exact tail1
        · exact tail2
      · have stopped1 : evaluateHOLFiniteState first rlpReadLengthLoop = (none,first) := by
          rw [source_rlpReadLength_loop,evaluateHOLFiniteState_while_total]
          simp [evalHOLFinite,evalHOLExact,i1,n1,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled]
        have stopped2 : evaluateHOLFiniteState second rlpReadLengthLoop = (none,second) := by
          rw [source_rlpReadLength_loop,evaluateHOLFiniteState_while_total]
          simp [evalHOLFinite,evalHOLExact,i2,n2,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled]
        have post1 := (Prod.mk.inj (run1.symm.trans stopped1)).2
        have post2 := (Prod.mk.inj (run2.symm.trans stopped2)).2
        rw [post1,post2,v1,v2]
  exact visit _ first second firstPost secondPost pointer index value length rfl firstPointer firstIndex firstValue firstLength
    secondPointer secondIndex secondValue secondLength reads firstRun secondRun

#print axioms rlpReadLength_loop_range_agreement
end InitECandidate.Runtime
