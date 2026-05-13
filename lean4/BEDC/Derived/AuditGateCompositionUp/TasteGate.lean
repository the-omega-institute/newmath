import BEDC.FKernel.Hist
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditGateCompositionUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditGateCompositionUp : Type where
  | mk :
      (gateLeft gateRight boundaryLeft boundaryRight refusalLeft refusalRight composedTrace
        transport replay provenance name : BHist) →
      AuditGateCompositionUp

def auditGateCompositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditGateCompositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditGateCompositionEncodeBHist h

def auditGateCompositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditGateCompositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditGateCompositionDecodeBHist tail)

private theorem auditGateCompositionDecode_encode_bhist :
    ∀ h : BHist,
      auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditGateCompositionToEventFlow : AuditGateCompositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditGateCompositionUp.mk gateLeft gateRight boundaryLeft boundaryRight refusalLeft
      refusalRight composedTrace transport replay provenance name =>
      [[BMark.b0],
        auditGateCompositionEncodeBHist gateLeft,
        [BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist gateRight,
        [BMark.b1, BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist boundaryLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist boundaryRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist refusalLeft,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist refusalRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist composedTrace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditGateCompositionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditGateCompositionEncodeBHist name]

def auditGateCompositionFromEventFlow : EventFlow → Option AuditGateCompositionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | gateLeft :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | gateRight :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | boundaryLeft :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | boundaryRight :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusalLeft :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | refusalRight :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | composedTrace :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | replay ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | provenance ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] =>
                                                                                          none
                                                                                      | name ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (AuditGateCompositionUp.mk
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    gateLeft)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    gateRight)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    boundaryLeft)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    boundaryRight)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    refusalLeft)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    refusalRight)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    composedTrace)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    transport)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    replay)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    provenance)
                                                                                                  (auditGateCompositionDecodeBHist
                                                                                                    name))
                                                                                          | _ :: _ =>
                                                                                              none

private theorem auditGateComposition_round_trip :
    ∀ x : AuditGateCompositionUp,
      auditGateCompositionFromEventFlow (auditGateCompositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk gateLeft gateRight boundaryLeft boundaryRight refusalLeft refusalRight composedTrace
      transport replay provenance name =>
      change
        some
            (AuditGateCompositionUp.mk
              (auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist gateLeft))
              (auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist gateRight))
              (auditGateCompositionDecodeBHist
                (auditGateCompositionEncodeBHist boundaryLeft))
              (auditGateCompositionDecodeBHist
                (auditGateCompositionEncodeBHist boundaryRight))
              (auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist refusalLeft))
              (auditGateCompositionDecodeBHist
                (auditGateCompositionEncodeBHist refusalRight))
              (auditGateCompositionDecodeBHist
                (auditGateCompositionEncodeBHist composedTrace))
              (auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist transport))
              (auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist replay))
              (auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist provenance))
              (auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist name))) =
          some
            (AuditGateCompositionUp.mk gateLeft gateRight boundaryLeft boundaryRight
              refusalLeft refusalRight composedTrace transport replay provenance name)
      rw [auditGateCompositionDecode_encode_bhist gateLeft,
        auditGateCompositionDecode_encode_bhist gateRight,
        auditGateCompositionDecode_encode_bhist boundaryLeft,
        auditGateCompositionDecode_encode_bhist boundaryRight,
        auditGateCompositionDecode_encode_bhist refusalLeft,
        auditGateCompositionDecode_encode_bhist refusalRight,
        auditGateCompositionDecode_encode_bhist composedTrace,
        auditGateCompositionDecode_encode_bhist transport,
        auditGateCompositionDecode_encode_bhist replay,
        auditGateCompositionDecode_encode_bhist provenance,
        auditGateCompositionDecode_encode_bhist name]

private theorem auditGateCompositionToEventFlow_injective {x y : AuditGateCompositionUp} :
    auditGateCompositionToEventFlow x = auditGateCompositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditGateCompositionFromEventFlow (auditGateCompositionToEventFlow x) =
        auditGateCompositionFromEventFlow (auditGateCompositionToEventFlow y) :=
    congrArg auditGateCompositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditGateComposition_round_trip x).symm
      (Eq.trans hread (auditGateComposition_round_trip y)))

instance auditGateCompositionBHistCarrier : BHistCarrier AuditGateCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditGateCompositionToEventFlow
  fromEventFlow := auditGateCompositionFromEventFlow

instance auditGateCompositionChapterTasteGate : ChapterTasteGate AuditGateCompositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change auditGateCompositionFromEventFlow (auditGateCompositionToEventFlow x) = some x
    exact auditGateComposition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditGateCompositionToEventFlow_injective heq)

theorem AuditGateCompositionTasteGate_single_carrier_alignment :
    (∀ h : BHist, auditGateCompositionDecodeBHist (auditGateCompositionEncodeBHist h) = h) ∧
      (∀ x : AuditGateCompositionUp,
        auditGateCompositionFromEventFlow (auditGateCompositionToEventFlow x) = some x) ∧
        (∀ x y : AuditGateCompositionUp,
          auditGateCompositionToEventFlow x = auditGateCompositionToEventFlow y → x = y) ∧
          auditGateCompositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact auditGateCompositionDecode_encode_bhist h
  · constructor
    · intro x
      exact auditGateComposition_round_trip x
    · constructor
      · intro x y heq
        exact auditGateCompositionToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditGateCompositionUp
