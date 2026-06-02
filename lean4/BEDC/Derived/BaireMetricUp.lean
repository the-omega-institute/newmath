import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireMetricUp : Type where
  | mk (B W D R U S H C P N : BHist) : BaireMetricUp
  deriving DecidableEq

def baireMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: baireMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: baireMetricEncodeBHist h

def baireMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (baireMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (baireMetricDecodeBHist tail)

private theorem BaireMetricNamecertObligations_decode :
    ∀ h : BHist, baireMetricDecodeBHist (baireMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def baireMetricToEventFlow : BaireMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BaireMetricUp.mk B W D R U S H C P N =>
      [baireMetricEncodeBHist B,
        baireMetricEncodeBHist W,
        baireMetricEncodeBHist D,
        baireMetricEncodeBHist R,
        baireMetricEncodeBHist U,
        baireMetricEncodeBHist S,
        baireMetricEncodeBHist H,
        baireMetricEncodeBHist C,
        baireMetricEncodeBHist P,
        baireMetricEncodeBHist N]

private def baireMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => baireMetricEventAtDefault index rest

def baireMetricFromEventFlow (ef : EventFlow) : Option BaireMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireMetricUp.mk
      (baireMetricDecodeBHist (baireMetricEventAtDefault 0 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 1 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 2 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 3 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 4 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 5 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 6 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 7 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 8 ef))
      (baireMetricDecodeBHist (baireMetricEventAtDefault 9 ef)))

private theorem BaireMetricNamecertObligations_round_trip (x : BaireMetricUp) :
    baireMetricFromEventFlow (baireMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B W D R U S H C P N =>
      change
        some
          (BaireMetricUp.mk
            (baireMetricDecodeBHist (baireMetricEncodeBHist B))
            (baireMetricDecodeBHist (baireMetricEncodeBHist W))
            (baireMetricDecodeBHist (baireMetricEncodeBHist D))
            (baireMetricDecodeBHist (baireMetricEncodeBHist R))
            (baireMetricDecodeBHist (baireMetricEncodeBHist U))
            (baireMetricDecodeBHist (baireMetricEncodeBHist S))
            (baireMetricDecodeBHist (baireMetricEncodeBHist H))
            (baireMetricDecodeBHist (baireMetricEncodeBHist C))
            (baireMetricDecodeBHist (baireMetricEncodeBHist P))
            (baireMetricDecodeBHist (baireMetricEncodeBHist N))) =
          some (BaireMetricUp.mk B W D R U S H C P N)
      rw [BaireMetricNamecertObligations_decode B,
        BaireMetricNamecertObligations_decode W,
        BaireMetricNamecertObligations_decode D,
        BaireMetricNamecertObligations_decode R,
        BaireMetricNamecertObligations_decode U,
        BaireMetricNamecertObligations_decode S,
        BaireMetricNamecertObligations_decode H,
        BaireMetricNamecertObligations_decode C,
        BaireMetricNamecertObligations_decode P,
        BaireMetricNamecertObligations_decode N]

private theorem BaireMetricNamecertObligations_toEventFlow_injective
    {x y : BaireMetricUp} :
    baireMetricToEventFlow x = baireMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      baireMetricFromEventFlow (baireMetricToEventFlow x) =
        baireMetricFromEventFlow (baireMetricToEventFlow y) :=
    congrArg baireMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireMetricNamecertObligations_round_trip x).symm
      (Eq.trans hread (BaireMetricNamecertObligations_round_trip y)))

instance baireMetricBHistCarrier : BHistCarrier BaireMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := baireMetricToEventFlow
  fromEventFlow := baireMetricFromEventFlow

instance baireMetricChapterTasteGate : ChapterTasteGate BaireMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change baireMetricFromEventFlow (baireMetricToEventFlow x) = some x
    exact BaireMetricNamecertObligations_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireMetricNamecertObligations_toEventFlow_injective heq)

theorem BaireMetricNamecertObligations (x : BaireMetricUp) :
    Nonempty (BHistCarrier BaireMetricUp) ∧ Nonempty (ChapterTasteGate BaireMetricUp) ∧
      baireMetricEncodeBHist BHist.Empty = ([] : List BMark) ∧
        baireMetricFromEventFlow (baireMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨baireMetricBHistCarrier⟩, ⟨baireMetricChapterTasteGate⟩, rfl,
      BaireMetricNamecertObligations_round_trip x⟩

end BEDC.Derived.BaireMetricUp
