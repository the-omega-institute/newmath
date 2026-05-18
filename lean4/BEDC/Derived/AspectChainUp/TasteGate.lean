import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AspectChainUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AspectChainUp : Type where
  | mk :
      (records inscription gap locality otherMinds transport routes provenance
        nameCert : BHist) →
      AspectChainUp
  deriving DecidableEq

def aspectChainEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: aspectChainEncodeBHist h
  | BHist.e1 h => BMark.b1 :: aspectChainEncodeBHist h

def aspectChainDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (aspectChainDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (aspectChainDecodeBHist tail)

private theorem aspectChainDecode_encode_bhist :
    ∀ h : BHist, aspectChainDecodeBHist (aspectChainEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def aspectChainToEventFlow : AspectChainUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
      nameCert =>
      [[BMark.b0],
        aspectChainEncodeBHist records,
        [BMark.b1, BMark.b0],
        aspectChainEncodeBHist inscription,
        [BMark.b1, BMark.b1, BMark.b0],
        aspectChainEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        aspectChainEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        aspectChainEncodeBHist otherMinds,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        aspectChainEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        aspectChainEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        aspectChainEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        aspectChainEncodeBHist nameCert]

def aspectChainFromEventFlow : EventFlow → Option AspectChainUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | records :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | inscription :: rest3 =>
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
                              | locality :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | otherMinds :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (AspectChainUp.mk
                                                                                  (aspectChainDecodeBHist
                                                                                    records)
                                                                                  (aspectChainDecodeBHist
                                                                                    inscription)
                                                                                  (aspectChainDecodeBHist
                                                                                    gap)
                                                                                  (aspectChainDecodeBHist
                                                                                    locality)
                                                                                  (aspectChainDecodeBHist
                                                                                    otherMinds)
                                                                                  (aspectChainDecodeBHist
                                                                                    transport)
                                                                                  (aspectChainDecodeBHist
                                                                                    routes)
                                                                                  (aspectChainDecodeBHist
                                                                                    provenance)
                                                                                  (aspectChainDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem aspectChain_round_trip :
    ∀ x : AspectChainUp, aspectChainFromEventFlow (aspectChainToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk records inscription gap locality otherMinds transport routes provenance nameCert =>
      change
        some
          (AspectChainUp.mk
            (aspectChainDecodeBHist (aspectChainEncodeBHist records))
            (aspectChainDecodeBHist (aspectChainEncodeBHist inscription))
            (aspectChainDecodeBHist (aspectChainEncodeBHist gap))
            (aspectChainDecodeBHist (aspectChainEncodeBHist locality))
            (aspectChainDecodeBHist (aspectChainEncodeBHist otherMinds))
            (aspectChainDecodeBHist (aspectChainEncodeBHist transport))
            (aspectChainDecodeBHist (aspectChainEncodeBHist routes))
            (aspectChainDecodeBHist (aspectChainEncodeBHist provenance))
            (aspectChainDecodeBHist (aspectChainEncodeBHist nameCert))) =
          some
            (AspectChainUp.mk records inscription gap locality otherMinds transport routes
              provenance nameCert)
      rw [aspectChainDecode_encode_bhist records,
        aspectChainDecode_encode_bhist inscription,
        aspectChainDecode_encode_bhist gap,
        aspectChainDecode_encode_bhist locality,
        aspectChainDecode_encode_bhist otherMinds,
        aspectChainDecode_encode_bhist transport,
        aspectChainDecode_encode_bhist routes,
        aspectChainDecode_encode_bhist provenance,
        aspectChainDecode_encode_bhist nameCert]

private theorem aspectChainToEventFlow_injective {x y : AspectChainUp} :
    aspectChainToEventFlow x = aspectChainToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      aspectChainFromEventFlow (aspectChainToEventFlow x) =
        aspectChainFromEventFlow (aspectChainToEventFlow y) :=
    congrArg aspectChainFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (aspectChain_round_trip x).symm
      (Eq.trans hread (aspectChain_round_trip y)))

instance aspectChainBHistCarrier : BHistCarrier AspectChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := aspectChainToEventFlow
  fromEventFlow := aspectChainFromEventFlow

instance aspectChainChapterTasteGate : ChapterTasteGate AspectChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change aspectChainFromEventFlow (aspectChainToEventFlow x) = some x
    exact aspectChain_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (aspectChainToEventFlow_injective heq)

instance aspectChainFieldFaithful : FieldFaithful AspectChainUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
        nameCert =>
        [records, inscription, gap, locality, otherMinds, transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y fieldsSame
    cases x with
    | mk records inscription gap locality otherMinds transport routes provenance nameCert =>
        cases y with
        | mk records' inscription' gap' locality' otherMinds' transport' routes' provenance'
            nameCert' =>
            simp only at fieldsSame
            injection fieldsSame with recordsSame tailSame
            injection tailSame with inscriptionSame tailSame
            injection tailSame with gapSame tailSame
            injection tailSame with localitySame tailSame
            injection tailSame with otherMindsSame tailSame
            injection tailSame with transportSame tailSame
            injection tailSame with routesSame tailSame
            injection tailSame with provenanceSame tailSame
            injection tailSame with nameCertSame _
            cases recordsSame
            cases inscriptionSame
            cases gapSame
            cases localitySame
            cases otherMindsSame
            cases transportSame
            cases routesSame
            cases provenanceSame
            cases nameCertSame
            rfl

def taste_gate : ChapterTasteGate AspectChainUp :=
  aspectChainChapterTasteGate

theorem AspectChainTasteGate_single_carrier_alignment :
    (∀ h : BHist, aspectChainDecodeBHist (aspectChainEncodeBHist h) = h) ∧
      (∀ x : AspectChainUp, aspectChainFromEventFlow (aspectChainToEventFlow x) = some x) ∧
        (∀ x y : AspectChainUp, aspectChainToEventFlow x = aspectChainToEventFlow y → x = y) ∧
          aspectChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact aspectChainDecode_encode_bhist
  · constructor
    · exact aspectChain_round_trip
    · constructor
      · intro x y heq
        exact aspectChainToEventFlow_injective heq
      · rfl

theorem AspectChainCarrier_non_collapse
    {records inscription gap locality otherMinds transport routes provenance nameCert records'
      inscription' gap' locality' otherMinds' transport' routes' provenance' nameCert' : BHist} :
    aspectChainToEventFlow
        (AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
          nameCert) =
      aspectChainToEventFlow
        (AspectChainUp.mk records' inscription' gap' locality' otherMinds' transport' routes'
          provenance' nameCert') →
      hsame records records' ∧ hsame inscription inscription' ∧ hsame gap gap' ∧
        hsame locality locality' ∧ hsame otherMinds otherMinds' ∧ hsame transport transport' ∧
          hsame routes routes' ∧ hsame provenance provenance' ∧ hsame nameCert nameCert' ∧
            aspectChainEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  intro encodedSame
  have packetSame :
      AspectChainUp.mk records inscription gap locality otherMinds transport routes provenance
          nameCert =
        AspectChainUp.mk records' inscription' gap' locality' otherMinds' transport' routes'
          provenance' nameCert' :=
    aspectChainToEventFlow_injective encodedSame
  cases packetSame
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.AspectChainUp
