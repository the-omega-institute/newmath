import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApophaticFixedPointFiberUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApophaticFixedPointFiberUp : Type where
  | mk
      (digestSocket supplySocket gapFiber farEndBoundary inscription transport
        continuation provenance nameCert : BHist) :
      ApophaticFixedPointFiberUp
  deriving DecidableEq

def apophaticFixedPointFiberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apophaticFixedPointFiberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apophaticFixedPointFiberEncodeBHist h

def apophaticFixedPointFiberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apophaticFixedPointFiberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apophaticFixedPointFiberDecodeBHist tail)

private theorem apophaticFixedPointFiberDecode_encode_bhist :
    ∀ h : BHist,
      apophaticFixedPointFiberDecodeBHist
        (apophaticFixedPointFiberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def apophaticFixedPointFiberToEventFlow :
    ApophaticFixedPointFiberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticFixedPointFiberUp.mk digestSocket supplySocket gapFiber farEndBoundary
      inscription transport continuation provenance nameCert =>
      [[BMark.b0],
        apophaticFixedPointFiberEncodeBHist digestSocket,
        [BMark.b1, BMark.b0],
        apophaticFixedPointFiberEncodeBHist supplySocket,
        [BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointFiberEncodeBHist gapFiber,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointFiberEncodeBHist farEndBoundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointFiberEncodeBHist inscription,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointFiberEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        apophaticFixedPointFiberEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        apophaticFixedPointFiberEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        apophaticFixedPointFiberEncodeBHist nameCert]

def apophaticFixedPointFiberFromEventFlow :
    EventFlow → Option ApophaticFixedPointFiberUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | digestSocket :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | supplySocket :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | gapFiber :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | farEndBoundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | inscription :: rest9 =>
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
                                                      | continuation :: rest13 =>
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
                                                                                (ApophaticFixedPointFiberUp.mk
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    digestSocket)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    supplySocket)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    gapFiber)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    farEndBoundary)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    inscription)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    transport)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    continuation)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    provenance)
                                                                                  (apophaticFixedPointFiberDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem apophaticFixedPointFiber_round_trip :
    ∀ x : ApophaticFixedPointFiberUp,
      apophaticFixedPointFiberFromEventFlow
        (apophaticFixedPointFiberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk digestSocket supplySocket gapFiber farEndBoundary inscription transport
      continuation provenance nameCert =>
      change
        some
          (ApophaticFixedPointFiberUp.mk
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist digestSocket))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist supplySocket))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist gapFiber))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist farEndBoundary))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist inscription))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist transport))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist continuation))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist provenance))
            (apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist nameCert))) =
          some
            (ApophaticFixedPointFiberUp.mk digestSocket supplySocket gapFiber
              farEndBoundary inscription transport continuation provenance nameCert)
      rw [apophaticFixedPointFiberDecode_encode_bhist digestSocket,
        apophaticFixedPointFiberDecode_encode_bhist supplySocket,
        apophaticFixedPointFiberDecode_encode_bhist gapFiber,
        apophaticFixedPointFiberDecode_encode_bhist farEndBoundary,
        apophaticFixedPointFiberDecode_encode_bhist inscription,
        apophaticFixedPointFiberDecode_encode_bhist transport,
        apophaticFixedPointFiberDecode_encode_bhist continuation,
        apophaticFixedPointFiberDecode_encode_bhist provenance,
        apophaticFixedPointFiberDecode_encode_bhist nameCert]

theorem apophaticFixedPointFiberToEventFlow_injective
    {x y : ApophaticFixedPointFiberUp} :
    apophaticFixedPointFiberToEventFlow x =
      apophaticFixedPointFiberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      apophaticFixedPointFiberFromEventFlow
          (apophaticFixedPointFiberToEventFlow x) =
        apophaticFixedPointFiberFromEventFlow
          (apophaticFixedPointFiberToEventFlow y) :=
    congrArg apophaticFixedPointFiberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apophaticFixedPointFiber_round_trip x).symm
      (Eq.trans hread (apophaticFixedPointFiber_round_trip y)))

def apophaticFixedPointFiberFields :
    ApophaticFixedPointFiberUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ApophaticFixedPointFiberUp.mk digestSocket supplySocket gapFiber farEndBoundary
      inscription transport continuation provenance nameCert =>
      [digestSocket, supplySocket, gapFiber, farEndBoundary, inscription, transport,
        continuation, provenance, nameCert]

private theorem apophaticFixedPointFiber_field_faithful :
    ∀ x y : ApophaticFixedPointFiberUp,
      apophaticFixedPointFiberFields x =
        apophaticFixedPointFiberFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk digestSocket₁ supplySocket₁ gapFiber₁ farEndBoundary₁ inscription₁
      transport₁ continuation₁ provenance₁ nameCert₁ =>
      cases y with
      | mk digestSocket₂ supplySocket₂ gapFiber₂ farEndBoundary₂ inscription₂
          transport₂ continuation₂ provenance₂ nameCert₂ =>
          cases h
          rfl

instance apophaticFixedPointFiberBHistCarrier :
    BHistCarrier ApophaticFixedPointFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := apophaticFixedPointFiberToEventFlow
  fromEventFlow := apophaticFixedPointFiberFromEventFlow

instance apophaticFixedPointFiberChapterTasteGate :
    ChapterTasteGate ApophaticFixedPointFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change apophaticFixedPointFiberFromEventFlow
      (apophaticFixedPointFiberToEventFlow x) = some x
    exact apophaticFixedPointFiber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apophaticFixedPointFiberToEventFlow_injective heq)

instance apophaticFixedPointFiberFieldFaithful :
    FieldFaithful ApophaticFixedPointFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := apophaticFixedPointFiberFields
  field_faithful := apophaticFixedPointFiber_field_faithful

instance apophaticFixedPointFiberNontrivial :
    Nontrivial ApophaticFixedPointFiberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ApophaticFixedPointFiberUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApophaticFixedPointFiberUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApophaticFixedPointFiberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  apophaticFixedPointFiberChapterTasteGate

theorem ApophaticFixedPointFiberTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ApophaticFixedPointFiberUp) ∧
      Nonempty (FieldFaithful ApophaticFixedPointFiberUp) ∧
        Nonempty (Nontrivial ApophaticFixedPointFiberUp) ∧
          (∀ h : BHist,
            apophaticFixedPointFiberDecodeBHist
              (apophaticFixedPointFiberEncodeBHist h) = h) ∧
            (∀ x : ApophaticFixedPointFiberUp,
              apophaticFixedPointFiberFromEventFlow
                (apophaticFixedPointFiberToEventFlow x) = some x) ∧
              (∀ x y : ApophaticFixedPointFiberUp,
                apophaticFixedPointFiberToEventFlow x =
                  apophaticFixedPointFiberToEventFlow y → x = y) ∧
                apophaticFixedPointFiberEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨apophaticFixedPointFiberChapterTasteGate⟩
  · constructor
    · exact ⟨apophaticFixedPointFiberFieldFaithful⟩
    · constructor
      · exact ⟨apophaticFixedPointFiberNontrivial⟩
      · constructor
        · exact apophaticFixedPointFiberDecode_encode_bhist
        · constructor
          · exact apophaticFixedPointFiber_round_trip
          · constructor
            · intro x y heq
              exact apophaticFixedPointFiberToEventFlow_injective heq
            · rfl

end BEDC.Derived.ApophaticFixedPointFiberUp
