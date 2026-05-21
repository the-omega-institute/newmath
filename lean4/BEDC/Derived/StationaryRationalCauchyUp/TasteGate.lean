import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StationaryRationalCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StationaryRationalCauchyUp : Type where
  | mk (ratSeed streamSchedule regularMember dyadicLedger realSeal provenance nameCert : BHist) :
      StationaryRationalCauchyUp

def StationaryRationalCauchyUpTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b0, BMark.b1, BMark.b1]

def stationaryRationalCauchyUpEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stationaryRationalCauchyUpEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stationaryRationalCauchyUpEncodeBHist h

def stationaryRationalCauchyUpDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stationaryRationalCauchyUpDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stationaryRationalCauchyUpDecodeBHist tail)

private theorem stationaryRationalCauchyUp_decode_encode_bhist :
    ∀ h : BHist,
      stationaryRationalCauchyUpDecodeBHist (stationaryRationalCauchyUpEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def stationaryRationalCauchyUpToEventFlow : StationaryRationalCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StationaryRationalCauchyUp.mk ratSeed streamSchedule regularMember dyadicLedger realSeal
      provenance nameCert =>
      [StationaryRationalCauchyUpTasteGate_single_carrier_alignment_tag,
        stationaryRationalCauchyUpEncodeBHist ratSeed,
        stationaryRationalCauchyUpEncodeBHist streamSchedule,
        stationaryRationalCauchyUpEncodeBHist regularMember,
        stationaryRationalCauchyUpEncodeBHist dyadicLedger,
        stationaryRationalCauchyUpEncodeBHist realSeal,
        stationaryRationalCauchyUpEncodeBHist provenance,
        stationaryRationalCauchyUpEncodeBHist nameCert]

def stationaryRationalCauchyUpFromEventFlow :
    EventFlow → Option StationaryRationalCauchyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | ratSeed :: rest1 =>
          match rest1 with
          | [] => none
          | streamSchedule :: rest2 =>
              match rest2 with
              | [] => none
              | regularMember :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicLedger :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | nameCert :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (StationaryRationalCauchyUp.mk
                                          (stationaryRationalCauchyUpDecodeBHist ratSeed)
                                          (stationaryRationalCauchyUpDecodeBHist
                                            streamSchedule)
                                          (stationaryRationalCauchyUpDecodeBHist regularMember)
                                          (stationaryRationalCauchyUpDecodeBHist dyadicLedger)
                                          (stationaryRationalCauchyUpDecodeBHist realSeal)
                                          (stationaryRationalCauchyUpDecodeBHist provenance)
                                          (stationaryRationalCauchyUpDecodeBHist nameCert))
                                  | _ :: _ => none

private theorem stationaryRationalCauchyUp_round_trip :
    ∀ x : StationaryRationalCauchyUp,
      stationaryRationalCauchyUpFromEventFlow (stationaryRationalCauchyUpToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk ratSeed streamSchedule regularMember dyadicLedger realSeal provenance nameCert =>
      change
        some
          (StationaryRationalCauchyUp.mk
            (stationaryRationalCauchyUpDecodeBHist
              (stationaryRationalCauchyUpEncodeBHist ratSeed))
            (stationaryRationalCauchyUpDecodeBHist
              (stationaryRationalCauchyUpEncodeBHist streamSchedule))
            (stationaryRationalCauchyUpDecodeBHist
              (stationaryRationalCauchyUpEncodeBHist regularMember))
            (stationaryRationalCauchyUpDecodeBHist
              (stationaryRationalCauchyUpEncodeBHist dyadicLedger))
            (stationaryRationalCauchyUpDecodeBHist
              (stationaryRationalCauchyUpEncodeBHist realSeal))
            (stationaryRationalCauchyUpDecodeBHist
              (stationaryRationalCauchyUpEncodeBHist provenance))
            (stationaryRationalCauchyUpDecodeBHist
              (stationaryRationalCauchyUpEncodeBHist nameCert))) =
          some
            (StationaryRationalCauchyUp.mk ratSeed streamSchedule regularMember dyadicLedger
              realSeal provenance nameCert)
      rw [stationaryRationalCauchyUp_decode_encode_bhist ratSeed,
        stationaryRationalCauchyUp_decode_encode_bhist streamSchedule,
        stationaryRationalCauchyUp_decode_encode_bhist regularMember,
        stationaryRationalCauchyUp_decode_encode_bhist dyadicLedger,
        stationaryRationalCauchyUp_decode_encode_bhist realSeal,
        stationaryRationalCauchyUp_decode_encode_bhist provenance,
        stationaryRationalCauchyUp_decode_encode_bhist nameCert]

private theorem stationaryRationalCauchyUpToEventFlow_injective
    {x y : StationaryRationalCauchyUp} :
    stationaryRationalCauchyUpToEventFlow x = stationaryRationalCauchyUpToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stationaryRationalCauchyUpFromEventFlow (stationaryRationalCauchyUpToEventFlow x) =
        stationaryRationalCauchyUpFromEventFlow (stationaryRationalCauchyUpToEventFlow y) :=
    congrArg stationaryRationalCauchyUpFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (stationaryRationalCauchyUp_round_trip x).symm
      (Eq.trans hread (stationaryRationalCauchyUp_round_trip y)))

instance stationaryRationalCauchyUpBHistCarrier :
    BHistCarrier StationaryRationalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stationaryRationalCauchyUpToEventFlow
  fromEventFlow := stationaryRationalCauchyUpFromEventFlow

instance stationaryRationalCauchyUpChapterTasteGate :
    ChapterTasteGate StationaryRationalCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stationaryRationalCauchyUpFromEventFlow (stationaryRationalCauchyUpToEventFlow x) =
        some x
    exact stationaryRationalCauchyUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (stationaryRationalCauchyUpToEventFlow_injective heq)

theorem StationaryRationalCauchyUpTasteGate_single_carrier_alignment_ChapterTasteGate :
    Nonempty (BEDC.Meta.TasteGate.BHistCarrier StationaryRationalCauchyUp) ∧
      Nonempty (BEDC.Meta.TasteGate.ChapterTasteGate StationaryRationalCauchyUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨stationaryRationalCauchyUpBHistCarrier⟩,
      ⟨stationaryRationalCauchyUpChapterTasteGate⟩⟩

end BEDC.Derived.StationaryRationalCauchyUp
