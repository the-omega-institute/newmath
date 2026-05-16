import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalInductionStabilitySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalInductionStabilitySealUp : Type where
  | mk :
      (observation finiteFit continuation stability failure reuse transport provenance
        localName : BHist) →
      PhysicalInductionStabilitySealUp
  deriving DecidableEq

def physicalInductionStabilitySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalInductionStabilitySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalInductionStabilitySealEncodeBHist h

def physicalInductionStabilitySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalInductionStabilitySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalInductionStabilitySealDecodeBHist tail)

private theorem physicalInductionStabilitySealDecode_encode_bhist :
    ∀ h : BHist,
      physicalInductionStabilitySealDecodeBHist
        (physicalInductionStabilitySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def physicalInductionStabilitySealToEventFlow :
    PhysicalInductionStabilitySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalInductionStabilitySealUp.mk observation finiteFit continuation stability failure
      reuse transport provenance localName =>
      [[BMark.b0],
        physicalInductionStabilitySealEncodeBHist observation,
        [BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist finiteFit,
        [BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist stability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist reuse,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        physicalInductionStabilitySealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        physicalInductionStabilitySealEncodeBHist localName]

def physicalInductionStabilitySealFromEventFlow :
    EventFlow → Option PhysicalInductionStabilitySealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observation :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | finiteFit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | continuation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | stability :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | failure :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | reuse :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
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
                                                                      | localName :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (PhysicalInductionStabilitySealUp.mk
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    observation)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    finiteFit)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    continuation)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    stability)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    failure)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    reuse)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    transport)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    provenance)
                                                                                  (physicalInductionStabilitySealDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem physicalInductionStabilitySeal_round_trip :
    ∀ x : PhysicalInductionStabilitySealUp,
      physicalInductionStabilitySealFromEventFlow
        (physicalInductionStabilitySealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observation finiteFit continuation stability failure reuse transport provenance
      localName =>
      change
        some
          (PhysicalInductionStabilitySealUp.mk
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist observation))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist finiteFit))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist continuation))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist stability))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist failure))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist reuse))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist transport))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist provenance))
            (physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist localName))) =
          some
            (PhysicalInductionStabilitySealUp.mk observation finiteFit continuation
              stability failure reuse transport provenance localName)
      rw [physicalInductionStabilitySealDecode_encode_bhist observation,
        physicalInductionStabilitySealDecode_encode_bhist finiteFit,
        physicalInductionStabilitySealDecode_encode_bhist continuation,
        physicalInductionStabilitySealDecode_encode_bhist stability,
        physicalInductionStabilitySealDecode_encode_bhist failure,
        physicalInductionStabilitySealDecode_encode_bhist reuse,
        physicalInductionStabilitySealDecode_encode_bhist transport,
        physicalInductionStabilitySealDecode_encode_bhist provenance,
        physicalInductionStabilitySealDecode_encode_bhist localName]

private theorem physicalInductionStabilitySealToEventFlow_injective
    {x y : PhysicalInductionStabilitySealUp} :
    physicalInductionStabilitySealToEventFlow x =
        physicalInductionStabilitySealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalInductionStabilitySealFromEventFlow
          (physicalInductionStabilitySealToEventFlow x) =
        physicalInductionStabilitySealFromEventFlow
          (physicalInductionStabilitySealToEventFlow y) :=
    congrArg physicalInductionStabilitySealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalInductionStabilitySeal_round_trip x).symm
      (Eq.trans hread (physicalInductionStabilitySeal_round_trip y)))

def physicalInductionStabilitySealFields :
    PhysicalInductionStabilitySealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalInductionStabilitySealUp.mk observation finiteFit continuation stability failure
      reuse transport provenance localName =>
      [observation, finiteFit, continuation, stability, failure, reuse, transport,
        provenance, localName]

private theorem physicalInductionStabilitySeal_field_faithful :
    ∀ x y : PhysicalInductionStabilitySealUp,
      physicalInductionStabilitySealFields x = physicalInductionStabilitySealFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk observation finiteFit continuation stability failure reuse transport provenance
      localName =>
      cases y with
      | mk observation' finiteFit' continuation' stability' failure' reuse' transport'
          provenance' localName' =>
          cases hfields
          rfl

instance physicalInductionStabilitySealBHistCarrier :
    BHistCarrier PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalInductionStabilitySealToEventFlow
  fromEventFlow := physicalInductionStabilitySealFromEventFlow

instance physicalInductionStabilitySealChapterTasteGate :
    ChapterTasteGate PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      physicalInductionStabilitySealFromEventFlow
        (physicalInductionStabilitySealToEventFlow x) = some x
    exact physicalInductionStabilitySeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalInductionStabilitySealToEventFlow_injective heq)

instance physicalInductionStabilitySealFieldFaithful :
    FieldFaithful PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalInductionStabilitySealFields
  field_faithful := physicalInductionStabilitySeal_field_faithful

instance physicalInductionStabilitySealNontrivial :
    Nontrivial PhysicalInductionStabilitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalInductionStabilitySealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhysicalInductionStabilitySealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalInductionStabilitySealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalInductionStabilitySealChapterTasteGate

theorem PhysicalInductionStabilitySealTasteGate_single_carrier_alignment :
    ChapterTasteGate PhysicalInductionStabilitySealUp ∧
      Nonempty (Nontrivial PhysicalInductionStabilitySealUp) ∧
        Nonempty (FieldFaithful PhysicalInductionStabilitySealUp) ∧
          (∀ h : BHist,
            physicalInductionStabilitySealDecodeBHist
              (physicalInductionStabilitySealEncodeBHist h) = h) ∧
            physicalInductionStabilitySealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact physicalInductionStabilitySealChapterTasteGate
  · constructor
    · exact ⟨physicalInductionStabilitySealNontrivial⟩
    · constructor
      · exact ⟨physicalInductionStabilitySealFieldFaithful⟩
      · constructor
        · exact physicalInductionStabilitySealDecode_encode_bhist
        · rfl

end BEDC.Derived.PhysicalInductionStabilitySealUp
