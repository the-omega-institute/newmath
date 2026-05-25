import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealCompletionFiniteRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealCompletionFiniteRouteUp : Type where
  | mk (D W R A M J U H C P N : BHist) : RealCompletionFiniteRouteUp

def realCompletionFiniteRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realCompletionFiniteRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realCompletionFiniteRouteEncodeBHist h

def realCompletionFiniteRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realCompletionFiniteRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realCompletionFiniteRouteDecodeBHist tail)

private theorem RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realCompletionFiniteRouteToEventFlow : RealCompletionFiniteRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealCompletionFiniteRouteUp.mk D W R A M J U H C P N =>
      [realCompletionFiniteRouteEncodeBHist D,
        realCompletionFiniteRouteEncodeBHist W,
        realCompletionFiniteRouteEncodeBHist R,
        realCompletionFiniteRouteEncodeBHist A,
        realCompletionFiniteRouteEncodeBHist M,
        realCompletionFiniteRouteEncodeBHist J,
        realCompletionFiniteRouteEncodeBHist U,
        realCompletionFiniteRouteEncodeBHist H,
        realCompletionFiniteRouteEncodeBHist C,
        realCompletionFiniteRouteEncodeBHist P,
        realCompletionFiniteRouteEncodeBHist N]

def realCompletionFiniteRouteFromEventFlow : EventFlow → Option RealCompletionFiniteRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | D :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | R :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | M :: rest4 =>
                      match rest4 with
                      | [] => none
                      | J :: rest5 =>
                          match rest5 with
                          | [] => none
                          | U :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (RealCompletionFiniteRouteUp.mk
                                                      (realCompletionFiniteRouteDecodeBHist D)
                                                      (realCompletionFiniteRouteDecodeBHist W)
                                                      (realCompletionFiniteRouteDecodeBHist R)
                                                      (realCompletionFiniteRouteDecodeBHist A)
                                                      (realCompletionFiniteRouteDecodeBHist M)
                                                      (realCompletionFiniteRouteDecodeBHist J)
                                                      (realCompletionFiniteRouteDecodeBHist U)
                                                      (realCompletionFiniteRouteDecodeBHist H)
                                                      (realCompletionFiniteRouteDecodeBHist C)
                                                      (realCompletionFiniteRouteDecodeBHist P)
                                                      (realCompletionFiniteRouteDecodeBHist N))
                                              | _extra :: _rest => none

private theorem realCompletionFiniteRoute_round_trip :
    ∀ x : RealCompletionFiniteRouteUp,
      realCompletionFiniteRouteFromEventFlow (realCompletionFiniteRouteToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W R A M J U H C P N =>
      change
        some
          (RealCompletionFiniteRouteUp.mk
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist D))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist W))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist R))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist A))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist M))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist J))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist U))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist H))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist C))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist P))
            (realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist N))) =
          some (RealCompletionFiniteRouteUp.mk D W R A M J U H C P N)
      rw [RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode D,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode W,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode R,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode A,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode M,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode J,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode U,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode H,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode C,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode P,
        RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode N]

private theorem realCompletionFiniteRouteToEventFlow_injective
    {x y : RealCompletionFiniteRouteUp} :
    realCompletionFiniteRouteToEventFlow x = realCompletionFiniteRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realCompletionFiniteRouteFromEventFlow (realCompletionFiniteRouteToEventFlow x) =
        realCompletionFiniteRouteFromEventFlow (realCompletionFiniteRouteToEventFlow y) :=
    congrArg realCompletionFiniteRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realCompletionFiniteRoute_round_trip x).symm
      (Eq.trans hread (realCompletionFiniteRoute_round_trip y)))

instance realCompletionFiniteRouteBHistCarrier :
    BHistCarrier RealCompletionFiniteRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realCompletionFiniteRouteToEventFlow
  fromEventFlow := realCompletionFiniteRouteFromEventFlow

instance realCompletionFiniteRouteChapterTasteGate :
    ChapterTasteGate RealCompletionFiniteRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realCompletionFiniteRouteFromEventFlow (realCompletionFiniteRouteToEventFlow x) =
        some x
    exact realCompletionFiniteRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realCompletionFiniteRouteToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RealCompletionFiniteRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realCompletionFiniteRouteChapterTasteGate

theorem RealCompletionFiniteRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realCompletionFiniteRouteDecodeBHist (realCompletionFiniteRouteEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealCompletionFiniteRouteUp) ∧
        Nonempty (ChapterTasteGate RealCompletionFiniteRouteUp) ∧
          realCompletionFiniteRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RealCompletionFiniteRouteTasteGate_single_carrier_alignment_decode,
      ⟨realCompletionFiniteRouteBHistCarrier⟩,
      ⟨realCompletionFiniteRouteChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealCompletionFiniteRouteUp
