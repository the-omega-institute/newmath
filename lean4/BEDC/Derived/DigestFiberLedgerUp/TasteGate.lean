import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DigestFiberLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DigestFiberLedgerUp : Type where
  | mk :
      (visible fiber gap refusal transport continuation provenance name : BHist) →
        DigestFiberLedgerUp
  deriving DecidableEq

def digestFiberLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: digestFiberLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: digestFiberLedgerEncodeBHist h

def digestFiberLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (digestFiberLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (digestFiberLedgerDecodeBHist tail)

private theorem digestFiberLedger_decode_encode_bhist :
    ∀ h : BHist, digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def digestFiberLedgerFields : DigestFiberLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DigestFiberLedgerUp.mk visible fiber gap refusal transport continuation provenance name =>
      [visible, fiber, gap, refusal, transport, continuation, provenance, name]

def digestFiberLedgerToEventFlow : DigestFiberLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DigestFiberLedgerUp.mk visible fiber gap refusal transport continuation provenance name =>
      [[BMark.b0],
        digestFiberLedgerEncodeBHist visible,
        [BMark.b1, BMark.b0],
        digestFiberLedgerEncodeBHist fiber,
        [BMark.b1, BMark.b1, BMark.b0],
        digestFiberLedgerEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestFiberLedgerEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestFiberLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestFiberLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        digestFiberLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        digestFiberLedgerEncodeBHist name]

def digestFiberLedgerFromEventFlow : EventFlow → Option DigestFiberLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | visible :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | fiber :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gap :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | refusal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (DigestFiberLedgerUp.mk
                                                                          (digestFiberLedgerDecodeBHist
                                                                            visible)
                                                                          (digestFiberLedgerDecodeBHist
                                                                            fiber)
                                                                          (digestFiberLedgerDecodeBHist
                                                                            gap)
                                                                          (digestFiberLedgerDecodeBHist
                                                                            refusal)
                                                                          (digestFiberLedgerDecodeBHist
                                                                            transport)
                                                                          (digestFiberLedgerDecodeBHist
                                                                            continuation)
                                                                          (digestFiberLedgerDecodeBHist
                                                                            provenance)
                                                                          (digestFiberLedgerDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem digestFiberLedger_round_trip :
    ∀ x : DigestFiberLedgerUp,
      digestFiberLedgerFromEventFlow (digestFiberLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk visible fiber gap refusal transport continuation provenance name =>
      change
        some
          (DigestFiberLedgerUp.mk
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist visible))
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist fiber))
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist gap))
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist refusal))
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist transport))
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist continuation))
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist provenance))
            (digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist name))) =
          some
            (DigestFiberLedgerUp.mk visible fiber gap refusal transport continuation provenance
              name)
      rw [digestFiberLedger_decode_encode_bhist visible,
        digestFiberLedger_decode_encode_bhist fiber,
        digestFiberLedger_decode_encode_bhist gap,
        digestFiberLedger_decode_encode_bhist refusal,
        digestFiberLedger_decode_encode_bhist transport,
        digestFiberLedger_decode_encode_bhist continuation,
        digestFiberLedger_decode_encode_bhist provenance,
        digestFiberLedger_decode_encode_bhist name]

private theorem digestFiberLedgerToEventFlow_injective {x y : DigestFiberLedgerUp} :
    digestFiberLedgerToEventFlow x = digestFiberLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      digestFiberLedgerFromEventFlow (digestFiberLedgerToEventFlow x) =
        digestFiberLedgerFromEventFlow (digestFiberLedgerToEventFlow y) :=
    congrArg digestFiberLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (digestFiberLedger_round_trip x).symm
      (Eq.trans hread (digestFiberLedger_round_trip y)))

private theorem DigestFiberLedgerTasteGate_field_faithful :
    ∀ x y : DigestFiberLedgerUp, digestFiberLedgerFields x = digestFiberLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk visible fiber gap refusal transport continuation provenance name =>
      cases y with
      | mk visible' fiber' gap' refusal' transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance digestFiberLedgerBHistCarrier : BHistCarrier DigestFiberLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := digestFiberLedgerToEventFlow
  fromEventFlow := digestFiberLedgerFromEventFlow

instance digestFiberLedgerChapterTasteGate : ChapterTasteGate DigestFiberLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change digestFiberLedgerFromEventFlow (digestFiberLedgerToEventFlow x) = some x
    exact digestFiberLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (digestFiberLedgerToEventFlow_injective heq)

instance digestFiberLedgerFieldFaithful : FieldFaithful DigestFiberLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := digestFiberLedgerFields
  field_faithful := DigestFiberLedgerTasteGate_field_faithful

def taste_gate : ChapterTasteGate DigestFiberLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  digestFiberLedgerChapterTasteGate

theorem DigestFiberLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, digestFiberLedgerDecodeBHist (digestFiberLedgerEncodeBHist h) = h) ∧
      (∀ x : DigestFiberLedgerUp,
        digestFiberLedgerFromEventFlow (digestFiberLedgerToEventFlow x) = some x) ∧
        (∀ x y : DigestFiberLedgerUp,
          digestFiberLedgerToEventFlow x = digestFiberLedgerToEventFlow y → x = y) ∧
          digestFiberLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact digestFiberLedger_decode_encode_bhist
  · constructor
    · exact digestFiberLedger_round_trip
    · constructor
      · intro x y heq
        exact digestFiberLedgerToEventFlow_injective heq
      · rfl

theorem DigestFiberLedgerNameCertObligations
    {visible fiber gap refusal transport continuation provenance name : BHist} :
    SemanticNameCert
        (fun row : BHist =>
          hsame row visible ∨ hsame row fiber ∨ hsame row gap ∨ hsame row refusal ∨
            hsame row transport ∨ hsame row continuation ∨ hsame row provenance ∨
              hsame row name)
        (fun row : BHist =>
          hsame row visible ∨ hsame row fiber ∨ hsame row gap ∨ hsame row refusal ∨
            hsame row transport ∨ hsame row continuation ∨ hsame row provenance ∨
              hsame row name)
        (fun row : BHist =>
          hsame row visible ∨ hsame row fiber ∨ hsame row gap ∨ hsame row refusal ∨
            hsame row transport ∨ hsame row continuation ∨ hsame row provenance ∨
              hsame row name)
        hsame ∧
      digestFiberLedgerFields
          (DigestFiberLedgerUp.mk visible fiber gap refusal transport continuation provenance name) =
        [visible, fiber, gap, refusal, transport, continuation, provenance, name] := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  constructor
  · constructor
    · constructor
      · exact Exists.intro visible (Or.inl (hsame_refl visible))
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        cases source with
        | inl visibleSame =>
            exact Or.inl (hsame_trans (hsame_symm same) visibleSame)
        | inr rest =>
            cases rest with
            | inl fiberSame =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm same) fiberSame))
            | inr rest =>
                cases rest with
                | inl gapSame =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm same) gapSame)))
                | inr rest =>
                    cases rest with
                    | inl refusalSame =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm same) refusalSame))))
                    | inr rest =>
                        cases rest with
                        | inl transportSame =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm same) transportSame)))))
                        | inr rest =>
                            cases rest with
                            | inl continuationSame =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm same)
                                                continuationSame))))))
                            | inr rest =>
                                cases rest with
                                | inl provenanceSame =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm same)
                                                      provenanceSame)))))))
                                | inr nameSame =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (hsame_trans (hsame_symm same)
                                                      nameSame)))))))
    · intro _row source
      exact source
    · intro _row source
      exact source
  · rfl

end BEDC.Derived.DigestFiberLedgerUp
