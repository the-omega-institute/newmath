import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InverseLimitMetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InverseLimitMetricUp : Type where
  | mk (D Pi W Q R L H C P N : BHist) : InverseLimitMetricUp
  deriving DecidableEq

def inverseLimitMetricEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: inverseLimitMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: inverseLimitMetricEncodeBHist h

def inverseLimitMetricDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (inverseLimitMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (inverseLimitMetricDecodeBHist tail)

private theorem inverseLimitMetric_decode_encode :
    ∀ h : BHist,
      inverseLimitMetricDecodeBHist
          (inverseLimitMetricEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def inverseLimitMetricFields :
    InverseLimitMetricUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | InverseLimitMetricUp.mk D Pi W Q R L H C P N => [D, Pi, W, Q, R, L, H, C, P, N]

def inverseLimitMetricToEventFlow :
    InverseLimitMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | InverseLimitMetricUp.mk D Pi W Q R L H C P N =>
      [inverseLimitMetricEncodeBHist D,
        inverseLimitMetricEncodeBHist Pi,
        inverseLimitMetricEncodeBHist W,
        inverseLimitMetricEncodeBHist Q,
        inverseLimitMetricEncodeBHist R,
        inverseLimitMetricEncodeBHist L,
        inverseLimitMetricEncodeBHist H,
        inverseLimitMetricEncodeBHist C,
        inverseLimitMetricEncodeBHist P,
        inverseLimitMetricEncodeBHist N]

private def inverseLimitMetricEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => inverseLimitMetricEventAt index rest

def inverseLimitMetricFromEventFlow :
    EventFlow → Option InverseLimitMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (InverseLimitMetricUp.mk
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 0 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 1 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 2 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 3 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 4 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 5 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 6 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 7 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 8 ef))
        (inverseLimitMetricDecodeBHist (inverseLimitMetricEventAt 9 ef)))

private theorem inverseLimitMetric_round_trip :
    ∀ x : InverseLimitMetricUp,
      inverseLimitMetricFromEventFlow
          (inverseLimitMetricToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D Pi W Q R L H C P N =>
      change
        some
          (InverseLimitMetricUp.mk
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist D))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist Pi))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist W))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist Q))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist R))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist L))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist H))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist C))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist P))
            (inverseLimitMetricDecodeBHist
              (inverseLimitMetricEncodeBHist N))) =
          some (InverseLimitMetricUp.mk D Pi W Q R L H C P N)
      rw [inverseLimitMetric_decode_encode D,
        inverseLimitMetric_decode_encode Pi,
        inverseLimitMetric_decode_encode W,
        inverseLimitMetric_decode_encode Q,
        inverseLimitMetric_decode_encode R,
        inverseLimitMetric_decode_encode L,
        inverseLimitMetric_decode_encode H,
        inverseLimitMetric_decode_encode C,
        inverseLimitMetric_decode_encode P,
        inverseLimitMetric_decode_encode N]

private theorem InverseLimitMetricToEventFlow_injective
    {x y : InverseLimitMetricUp} :
    inverseLimitMetricToEventFlow x =
        inverseLimitMetricToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          inverseLimitMetricFromEventFlow
            (inverseLimitMetricToEventFlow x) :=
        (inverseLimitMetric_round_trip x).symm
      _ =
          inverseLimitMetricFromEventFlow
            (inverseLimitMetricToEventFlow y) :=
        congrArg inverseLimitMetricFromEventFlow hxy
      _ = some y := inverseLimitMetric_round_trip y
  exact Option.some.inj hsome

private theorem inverseLimitMetric_field_faithful :
    ∀ x y : InverseLimitMetricUp,
      inverseLimitMetricFields x =
          inverseLimitMetricFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 Pi1 W1 Q1 R1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 Pi2 W2 Q2 R2 L2 H2 C2 P2 N2 =>
          injection hfields with hD tail0
          injection tail0 with hPi tail1
          injection tail1 with hW tail2
          injection tail2 with hQ tail3
          injection tail3 with hR tail4
          injection tail4 with hL tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hD
          subst hPi
          subst hW
          subst hQ
          subst hR
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance inverseLimitMetricBHistCarrier :
    BHistCarrier InverseLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := inverseLimitMetricToEventFlow
  fromEventFlow := inverseLimitMetricFromEventFlow

instance inverseLimitMetricChapterTasteGate :
    ChapterTasteGate InverseLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      inverseLimitMetricFromEventFlow
          (inverseLimitMetricToEventFlow x) =
        some x
    exact inverseLimitMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (InverseLimitMetricToEventFlow_injective heq)

instance inverseLimitMetricFieldFaithful :
    FieldFaithful InverseLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := inverseLimitMetricFields
  field_faithful := inverseLimitMetric_field_faithful

instance inverseLimitMetricNontrivial :
    Nontrivial InverseLimitMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨InverseLimitMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      InverseLimitMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate InverseLimitMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inverseLimitMetricChapterTasteGate

theorem InverseLimitMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      inverseLimitMetricDecodeBHist
          (inverseLimitMetricEncodeBHist h) =
        h) ∧
      inverseLimitMetricFields
          (InverseLimitMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact inverseLimitMetric_decode_encode
  · rfl

end BEDC.Derived.InverseLimitMetricUp
