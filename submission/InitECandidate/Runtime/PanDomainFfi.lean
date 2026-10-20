import InitECandidate.Runtime.PanDomainAtoms
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem callFFIHOL_return_length {F : Type} (ffi next : HolFfiState F) (name : HolFfiName) (config bytes newBytes : List (BitVec 8))
    (run : callFFIHOL ffi name config bytes=.ret next newBytes) : newBytes.length=bytes.length := by
  unfold callFFIHOL at run
  split at run
  · cases run;rfl
  · split at run
    · split at run
      · cases run;assumption
      · cases run
    · cases run
 theorem evaluate_extCall_finite_record {F : Type} (s : PanSemStateFiniteExact 64 F) (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    evaluateHOLFiniteState s (.extCall function configuration configurationLength array arrayLength)=
    (match @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) configuration,
      @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) configurationLength,
      @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) array,
      @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arrayLength with
    | some (.val (.word address1)),some (.val (.word length1)),some (.val (.word address2)),some (.val (.word length2)) =>
      match readBytearrayWordHOL address1 length1.toNat (@panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be),
        readBytearrayWordHOL address2 length2.toNat (@panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be) with
      | some bytes1,some bytes2 =>
        match callFFIHOL s.ffi (.extCall function) bytes1 bytes2 with
        | .final event => (some (.finalFfi event),emptyLocalsHOLFinite s)
        | .ret nextFfi newBytes => (none,{s with memory:=@panWriteBytearrayWord8HOL 64 _ address2 newBytes s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be,ffi:=nextFfi})
      | _,_ => (some .error,s)
    | _,_,_,_ => (some .error,s)) := by
  have roundtrip (memory : BitVec 64→HolWordLab 64) (ffi : HolFfiState F)
      (proof : ({s.toExact with memory:=memory,ffi:=ffi} : PanSemStateExact 64 F).FiniteSupport) :
      ofExact {s.toExact with memory:=memory,ffi:=ffi} proof={s with memory:=memory,ffi:=ffi} := by
    cases s
    rfl
  rw [evaluateHOLFiniteState_extCall_source]
  simp only [roundtrip]
  cases old_address1 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) configuration with
  | none => rfl
  | some value => cases value with
    | rStruct fields => rfl
    | nStruct name fields => rfl
    | val payload => cases payload with
      | word address1 =>
        cases old_length1 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) configurationLength with
        | none => rfl
        | some value => cases value with
          | rStruct fields => rfl
          | nStruct name fields => rfl
          | val payload => cases payload with
            | word length1 =>
              cases old_address2 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) array with
              | none => rfl
              | some value => cases value with
                | rStruct fields => rfl
                | nStruct name fields => rfl
                | val payload => cases payload with
                  | word address2 =>
                    cases old_length2 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arrayLength with
                    | none => rfl
                    | some value => cases value with
                      | rStruct fields => rfl
                      | nStruct name fields => rfl
                      | val payload => cases payload with
                        | word length2 =>
                          cases read1 : readBytearrayWordHOL address1 length1.toNat (@panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be) with
                          | none => rfl
                          | some bytes1 =>
                            cases read2 : readBytearrayWordHOL address2 length2.toNat (@panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be) with
                            | none => rfl
                            | some bytes2 =>
                              cases callFFIHOL s.ffi (.extCall function) bytes1 bytes2 <;> rfl
 theorem panDomainMono_extCall {F : Type} (s : PanSemStateFiniteExact 64 F) (function : MlS) (configuration configurationLength array arrayLength : ExpHOL 64) :
    PanDomainMonoAt (.extCall function configuration configurationLength array arrayLength) s := by
  classical
  intro domain subset valid
  simp only [evaluate_extCall_finite_record] at valid ⊢
  cases old_address1 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) configuration with
  | none => simp only [old_address1] at valid;exact False.elim (valid rfl)
  | some value => cases value with
    | rStruct fields => simp only [old_address1] at valid;exact False.elim (valid rfl)
    | nStruct name fields => simp only [old_address1] at valid;exact False.elim (valid rfl)
    | val payload => cases payload with
      | word address1 =>
        have next_address1:=evalHOLFinite_memaddrs_mono s domain subset configuration (.val (.word address1)) old_address1
        simp only [old_address1] at valid ⊢
        simp only [next_address1]
        cases old_length1 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) configurationLength with
        | none => simp only [old_length1] at valid;exact False.elim (valid rfl)
        | some value => cases value with
          | rStruct fields => simp only [old_length1] at valid;exact False.elim (valid rfl)
          | nStruct name fields => simp only [old_length1] at valid;exact False.elim (valid rfl)
          | val payload => cases payload with
            | word length1 =>
              have next_length1:=evalHOLFinite_memaddrs_mono s domain subset configurationLength (.val (.word length1)) old_length1
              simp only [old_length1] at valid ⊢
              simp only [next_length1]
              cases old_address2 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) array with
              | none => simp only [old_address2] at valid;exact False.elim (valid rfl)
              | some value => cases value with
                | rStruct fields => simp only [old_address2] at valid;exact False.elim (valid rfl)
                | nStruct name fields => simp only [old_address2] at valid;exact False.elim (valid rfl)
                | val payload => cases payload with
                  | word address2 =>
                    have next_address2:=evalHOLFinite_memaddrs_mono s domain subset array (.val (.word address2)) old_address2
                    simp only [old_address2] at valid ⊢
                    simp only [next_address2]
                    cases old_length2 : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) arrayLength with
                    | none => simp only [old_length2] at valid;exact False.elim (valid rfl)
                    | some value => cases value with
                      | rStruct fields => simp only [old_length2] at valid;exact False.elim (valid rfl)
                      | nStruct name fields => simp only [old_length2] at valid;exact False.elim (valid rfl)
                      | val payload => cases payload with
                        | word length2 =>
                          have next_length2:=evalHOLFinite_memaddrs_mono s domain subset arrayLength (.val (.word length2)) old_length2
                          simp only [old_length2] at valid ⊢
                          simp only [next_length2]
                          let oldLoad := @panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be
                          let nextLoad := @panMemLoadByteWord8HOL 64 _ s.memory domain (fun a=>Classical.propDecidable (domain a)) s.be
                          have bytesPreserved : ∀ address byte,oldLoad address=some byte→nextLoad address=some byte := fun address byte read => panMemLoadByteWord8HOL_memaddrs_mono s.memory s.memaddrs domain s.be address byte subset read
                          cases read1 : readBytearrayWordHOL address1 length1.toNat oldLoad with
                          | none => dsimp only [oldLoad] at read1;simp only [read1] at valid;exact False.elim (valid rfl)
                          | some bytes1 =>
                            dsimp only [oldLoad] at read1
                            have read1Next:=readBytearrayWordHOL_mono oldLoad nextLoad bytesPreserved length1.toNat address1 bytes1 read1
                            dsimp only [nextLoad] at read1Next
                            try simp only [read1] at valid ⊢
                            try simp only [read1Next]
                            cases read2 : readBytearrayWordHOL address2 length2.toNat oldLoad with
                            | none => dsimp only [oldLoad] at read2;simp only [read2] at valid;exact False.elim (valid rfl)
                            | some bytes2 =>
                              dsimp only [oldLoad] at read2
                              have read2Next:=readBytearrayWordHOL_mono oldLoad nextLoad bytesPreserved length2.toNat address2 bytes2 read2
                              dsimp only [nextLoad] at read2Next
                              try simp only [read2] at valid ⊢
                              try simp only [read2Next]
                              cases ffiRun : callFFIHOL s.ffi (.extCall function) bytes1 bytes2 with
                              | final event => simp only [ffiRun,emptyLocalsHOLFinite]
                              | ret nextFfi newBytes =>
                                have length:=callFFIHOL_return_length s.ffi nextFfi (.extCall function) bytes1 bytes2 newBytes ffiRun
                                have readLength:=readBytearrayWordHOL_length address2 length2.toNat oldLoad bytes2 read2
                                have readNew : readBytearrayWordHOL address2 newBytes.length oldLoad=some bytes2 := by simpa only [length,readLength] using read2
                                have writeEq:=@panWriteBytearrayWord8HOL_memaddrs_mono 64 _ s.memory s.memaddrs domain (fun a=>Classical.propDecidable (s.memaddrs a)) (fun a=>Classical.propDecidable (domain a)) s.be subset newBytes address2 bytes2 readNew
                                simp only [ffiRun,←writeEq,ofExact,toExact]
#print axioms evaluate_extCall_finite_record
#print axioms callFFIHOL_return_length
#print axioms panDomainMono_extCall
end InitECandidate.Runtime
