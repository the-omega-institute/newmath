import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

/-!
# InscriptionPointUp TasteGate carrier.
-/

namespace BEDC.Derived.InscriptionPointUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Inscription point token with the ten BEDC rows visible to local consumers. -/
inductive InscriptionPointUp : Type where
  | mk :
      (history gap supply handoff event ledger transport route provenance localName : BHist) →
      InscriptionPointUp
  deriving DecidableEq

def inscriptionPointEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inscriptionPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inscriptionPointEncodeBHist h

def inscriptionPointDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inscriptionPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inscriptionPointDecodeBHist tail)

private theorem inscriptionPoint_decode_encode_bhist :
    ∀ h : BHist, inscriptionPointDecodeBHist (inscriptionPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def inscriptionPointToEventFlow : InscriptionPointUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InscriptionPointUp.mk history gap supply handoff event ledger transport route provenance
      localName =>
      [[BMark.b0],
        inscriptionPointEncodeBHist history,
        [BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist supply,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist event,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        inscriptionPointEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        inscriptionPointEncodeBHist localName]

def inscriptionPointFromEventFlow : EventFlow → Option InscriptionPointUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | history :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | gap :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | supply :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | handoff :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | event :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | ledger :: rest11 =>
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
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (InscriptionPointUp.mk
                                                                                          (inscriptionPointDecodeBHist
                                                                                            history)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            gap)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            supply)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            handoff)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            event)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            ledger)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            transport)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            route)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            provenance)
                                                                                          (inscriptionPointDecodeBHist
                                                                                            localName))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem inscriptionPoint_round_trip :
    ∀ x : InscriptionPointUp,
      inscriptionPointFromEventFlow (inscriptionPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history gap supply handoff event ledger transport route provenance localName =>
      change
        some
          (InscriptionPointUp.mk
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist history))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist gap))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist supply))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist handoff))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist event))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist ledger))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist transport))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist route))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist provenance))
            (inscriptionPointDecodeBHist (inscriptionPointEncodeBHist localName))) =
          some
            (InscriptionPointUp.mk history gap supply handoff event ledger transport route
              provenance localName)
      rw [inscriptionPoint_decode_encode_bhist history,
        inscriptionPoint_decode_encode_bhist gap,
        inscriptionPoint_decode_encode_bhist supply,
        inscriptionPoint_decode_encode_bhist handoff,
        inscriptionPoint_decode_encode_bhist event,
        inscriptionPoint_decode_encode_bhist ledger,
        inscriptionPoint_decode_encode_bhist transport,
        inscriptionPoint_decode_encode_bhist route,
        inscriptionPoint_decode_encode_bhist provenance,
        inscriptionPoint_decode_encode_bhist localName]

private theorem inscriptionPointToEventFlow_injective {x y : InscriptionPointUp} :
    inscriptionPointToEventFlow x = inscriptionPointToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      inscriptionPointFromEventFlow (inscriptionPointToEventFlow x) =
        inscriptionPointFromEventFlow (inscriptionPointToEventFlow y) :=
    congrArg inscriptionPointFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (inscriptionPoint_round_trip x).symm
      (Eq.trans hread (inscriptionPoint_round_trip y))
  cases hsome
  rfl

instance inscriptionPointBHistCarrier : BHistCarrier InscriptionPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inscriptionPointToEventFlow
  fromEventFlow := inscriptionPointFromEventFlow

instance inscriptionPointChapterTasteGate : ChapterTasteGate InscriptionPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change inscriptionPointFromEventFlow (inscriptionPointToEventFlow x) = some x
    exact inscriptionPoint_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (inscriptionPointToEventFlow_injective heq)

theorem InscriptionPointTasteGate_single_carrier_alignment :
    (∀ h : BHist, inscriptionPointDecodeBHist (inscriptionPointEncodeBHist h) = h) ∧
      (∀ x : InscriptionPointUp,
        inscriptionPointFromEventFlow (inscriptionPointToEventFlow x) = some x) ∧
      (∀ x y : InscriptionPointUp,
        inscriptionPointToEventFlow x = inscriptionPointToEventFlow y → x = y) ∧
      inscriptionPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inscriptionPoint_decode_encode_bhist
  · constructor
    · exact inscriptionPoint_round_trip
    · constructor
      · intro x y sameFlow
        exact inscriptionPointToEventFlow_injective sameFlow
      · rfl

end BEDC.Derived.InscriptionPointUp
