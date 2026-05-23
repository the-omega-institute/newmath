import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMetricUp : Type where
  | mk :
      (r0 r1 w d q e h c p n :
        BHist) ->
      RegularCauchyMetricUp
  deriving DecidableEq

def regularCauchyMetricEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMetricEncodeBHist h

def regularCauchyMetricDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMetricDecodeBHist tail)

private theorem RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyMetricFields : RegularCauchyMetricUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMetricUp.mk r0 r1 w d q e h
      c p n =>
      [r0, r1, w, d, q, e, h, c,
        p, n]

def regularCauchyMetricEncodeCarrier : RegularCauchyMetricUp -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMetricUp.mk r0 r1 w d q e h
      c p n =>
      append r0
        (append r1
          (append w
            (append d
              (append q
                (append e (append h (append c (append p n))))))))

def regularCauchyMetricToEventFlow : RegularCauchyMetricUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMetricUp.mk r0 r1 w d q e h
      c p n =>
      [regularCauchyMetricEncodeBHist r0,
        regularCauchyMetricEncodeBHist r1,
        regularCauchyMetricEncodeBHist w,
        regularCauchyMetricEncodeBHist d,
        regularCauchyMetricEncodeBHist q,
        regularCauchyMetricEncodeBHist e,
        regularCauchyMetricEncodeBHist h,
        regularCauchyMetricEncodeBHist c,
        regularCauchyMetricEncodeBHist p,
        regularCauchyMetricEncodeBHist n]

private def regularCauchyMetricEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMetricEventAtDefault index rest

def regularCauchyMetricFromEventFlow (ef : EventFlow) : Option RegularCauchyMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
      (RegularCauchyMetricUp.mk
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 0 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 1 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 2 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 3 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 4 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 5 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 6 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 7 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 8 ef))
      (regularCauchyMetricDecodeBHist (regularCauchyMetricEventAtDefault 9 ef)))

private theorem RegularCauchyMetricTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyMetricUp,
      regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk r0 r1 w d q e h c p n =>
      change
        some
          (RegularCauchyMetricUp.mk
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist r0))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist r1))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist w))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist d))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist q))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist e))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist h))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist c))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist p))
            (regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist n))) =
          some
            (RegularCauchyMetricUp.mk r0 r1 w d q e
              h c p n)
      rw [RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode r0,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode r1,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode w,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode d,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode q,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode e,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode h,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode c,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode p,
        RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode n]

private theorem RegularCauchyMetricTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyMetricUp} :
    regularCauchyMetricToEventFlow x = regularCauchyMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) =
        regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow y) :=
    congrArg regularCauchyMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyMetricTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyMetricBHistCarrier : BHistCarrier RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMetricToEventFlow
  fromEventFlow := regularCauchyMetricFromEventFlow

instance regularCauchyMetricChapterTasteGate : ChapterTasteGate RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x
    exact RegularCauchyMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMetricChapterTasteGate

theorem RegularCauchyMetricTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyMetricDecodeBHist (regularCauchyMetricEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyMetricUp,
        regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyMetricUp,
        regularCauchyMetricToEventFlow x = regularCauchyMetricToEventFlow y -> x = y) ∧
      regularCauchyMetricEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyMetricTasteGate_single_carrier_alignment_decode_encode
  constructor
  · exact RegularCauchyMetricTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact RegularCauchyMetricTasteGate_single_carrier_alignment_toEventFlow_injective heq
  · rfl

theorem RegularCauchyMetricTasteGate_single_carrier_alignment_carrier_cont :
    ∀ x : RegularCauchyMetricUp,
      Cont (regularCauchyMetricEncodeCarrier x)
        (regularCauchyMetricEncodeCarrier x)
        (append (regularCauchyMetricEncodeCarrier x) (regularCauchyMetricEncodeCarrier x)) := by
  -- BEDC touchpoint anchor: BHist Cont BMark
  intro x
  rfl

end BEDC.Derived.RegularCauchyMetricUp
