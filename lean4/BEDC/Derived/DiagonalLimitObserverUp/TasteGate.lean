import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalLimitObserverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalLimitObserverUp : Type where
  | mk :
      (diagonal window readback tolerance sealRow realSeal transport route provenance
        name : BHist) →
      DiagonalLimitObserverUp
  deriving DecidableEq

def diagonalLimitObserverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalLimitObserverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalLimitObserverEncodeBHist h

def diagonalLimitObserverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalLimitObserverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalLimitObserverDecodeBHist tail)

private theorem diagonalLimitObserver_decode_encode_bhist :
    ∀ h : BHist,
      diagonalLimitObserverDecodeBHist
        (diagonalLimitObserverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def diagonalLimitObserverToEventFlow :
    DiagonalLimitObserverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalLimitObserverUp.mk diagonal window readback tolerance sealRow realSeal transport route
      provenance name =>
      [[BMark.b0],
        diagonalLimitObserverEncodeBHist diagonal,
        [BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalLimitObserverEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist name]

def diagonalLimitObserverFromEventFlow :
    EventFlow → Option DiagonalLimitObserverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | diagonal :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | window :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tolerance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | sealRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realSeal :: rest11 =>
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
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | name ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (DiagonalLimitObserverUp.mk
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            diagonal)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            window)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            readback)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            tolerance)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            sealRow)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            realSeal)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            transport)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            route)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            provenance)
                                                                                          (diagonalLimitObserverDecodeBHist
                                                                                            name))
                                                                                  | _ ::
                                                                                      _ =>
                                                                                      none

private theorem diagonalLimitObserver_round_trip :
    ∀ x : DiagonalLimitObserverUp,
      diagonalLimitObserverFromEventFlow
        (diagonalLimitObserverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk diagonal window readback tolerance sealRow realSeal transport route provenance name =>
      change
        some
          (DiagonalLimitObserverUp.mk
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist diagonal))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist window))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist readback))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist tolerance))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist sealRow))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist realSeal))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist transport))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist route))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist provenance))
            (diagonalLimitObserverDecodeBHist
              (diagonalLimitObserverEncodeBHist name))) =
          some
            (DiagonalLimitObserverUp.mk diagonal window readback tolerance sealRow realSeal
              transport route provenance name)
      rw [diagonalLimitObserver_decode_encode_bhist diagonal,
        diagonalLimitObserver_decode_encode_bhist window,
        diagonalLimitObserver_decode_encode_bhist readback,
        diagonalLimitObserver_decode_encode_bhist tolerance,
        diagonalLimitObserver_decode_encode_bhist sealRow,
        diagonalLimitObserver_decode_encode_bhist realSeal,
        diagonalLimitObserver_decode_encode_bhist transport,
        diagonalLimitObserver_decode_encode_bhist route,
        diagonalLimitObserver_decode_encode_bhist provenance,
        diagonalLimitObserver_decode_encode_bhist name]

private theorem diagonalLimitObserverToEventFlow_injective
    {x y : DiagonalLimitObserverUp} :
    diagonalLimitObserverToEventFlow x =
      diagonalLimitObserverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalLimitObserverFromEventFlow
          (diagonalLimitObserverToEventFlow x) =
        diagonalLimitObserverFromEventFlow
          (diagonalLimitObserverToEventFlow y) :=
    congrArg diagonalLimitObserverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalLimitObserver_round_trip x).symm
      (Eq.trans hread (diagonalLimitObserver_round_trip y)))

instance diagonalLimitObserverBHistCarrier :
    BHistCarrier DiagonalLimitObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalLimitObserverToEventFlow
  fromEventFlow := diagonalLimitObserverFromEventFlow

instance diagonalLimitObserverChapterTasteGate :
    ChapterTasteGate DiagonalLimitObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      diagonalLimitObserverFromEventFlow
        (diagonalLimitObserverToEventFlow x) = some x
    exact diagonalLimitObserver_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalLimitObserverToEventFlow_injective heq)

instance diagonalLimitObserverFieldFaithful :
    FieldFaithful DiagonalLimitObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | DiagonalLimitObserverUp.mk diagonal window readback tolerance sealRow realSeal transport
        route provenance name =>
        [diagonal, window, readback, tolerance, sealRow, realSeal, transport, route,
          provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk diagonal window readback tolerance sealRow realSeal transport route provenance name =>
        cases y with
        | mk diagonal' window' readback' tolerance' sealRow' realSeal' transport' route'
            provenance' name' =>
            cases hfields
            rfl

instance diagonalLimitObserverNontrivial :
    Nontrivial DiagonalLimitObserverUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨DiagonalLimitObserverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalLimitObserverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DiagonalLimitObserverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

theorem DiagonalLimitObserverTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      diagonalLimitObserverDecodeBHist
        (diagonalLimitObserverEncodeBHist h) = h) ∧
      (∀ x : DiagonalLimitObserverUp,
        diagonalLimitObserverFromEventFlow
          (diagonalLimitObserverToEventFlow x) = some x) ∧
        (∀ x y : DiagonalLimitObserverUp,
          diagonalLimitObserverToEventFlow x =
            diagonalLimitObserverToEventFlow y → x = y) ∧
          diagonalLimitObserverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diagonalLimitObserver_decode_encode_bhist
  · constructor
    · exact diagonalLimitObserver_round_trip
    · constructor
      · intro x y heq
        exact diagonalLimitObserverToEventFlow_injective heq
      · rfl

end BEDC.Derived.DiagonalLimitObserverUp
