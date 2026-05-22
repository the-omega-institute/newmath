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

def regularCauchyMetricEncodeRawEvent : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMetricEncodeRawEvent h
  | BHist.e1 h => BMark.b1 :: regularCauchyMetricEncodeRawEvent h

def regularCauchyMetricDecodeRawEvent : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMetricDecodeRawEvent tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMetricDecodeRawEvent tail)

private theorem regularCauchyMetric_decode_encode_bhist :
    forall h : BHist,
      regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent h) = h := by
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

def regularCauchyMetricEncodeBHist : RegularCauchyMetricUp -> BHist
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
      [regularCauchyMetricEncodeRawEvent r0,
        regularCauchyMetricEncodeRawEvent r1,
        regularCauchyMetricEncodeRawEvent w,
        regularCauchyMetricEncodeRawEvent d,
        regularCauchyMetricEncodeRawEvent q,
        regularCauchyMetricEncodeRawEvent e,
        regularCauchyMetricEncodeRawEvent h,
        regularCauchyMetricEncodeRawEvent c,
        regularCauchyMetricEncodeRawEvent p,
        regularCauchyMetricEncodeRawEvent n]

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
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 0 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 1 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 2 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 3 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 4 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 5 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 6 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 7 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 8 ef))
      (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEventAtDefault 9 ef)))

private theorem regularCauchyMetric_round_trip :
    forall x : RegularCauchyMetricUp,
      regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk r0 r1 w d q e h c p n =>
      change
        some
          (RegularCauchyMetricUp.mk
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent r0))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent r1))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent w))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent d))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent q))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent e))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent h))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent c))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent p))
            (regularCauchyMetricDecodeRawEvent (regularCauchyMetricEncodeRawEvent n))) =
          some
            (RegularCauchyMetricUp.mk r0 r1 w d q e
              h c p n)
      rw [regularCauchyMetric_decode_encode_bhist r0,
        regularCauchyMetric_decode_encode_bhist r1,
        regularCauchyMetric_decode_encode_bhist w,
        regularCauchyMetric_decode_encode_bhist d,
        regularCauchyMetric_decode_encode_bhist q,
        regularCauchyMetric_decode_encode_bhist e,
        regularCauchyMetric_decode_encode_bhist h,
        regularCauchyMetric_decode_encode_bhist c,
        regularCauchyMetric_decode_encode_bhist p,
        regularCauchyMetric_decode_encode_bhist n]

private theorem regularCauchyMetricToEventFlow_injective {x y : RegularCauchyMetricUp} :
    regularCauchyMetricToEventFlow x = regularCauchyMetricToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) =
        regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow y) :=
    congrArg regularCauchyMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (regularCauchyMetric_round_trip x).symm
      (Eq.trans hread (regularCauchyMetric_round_trip y)))

instance regularCauchyMetricBHistCarrier : BHistCarrier RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMetricToEventFlow
  fromEventFlow := regularCauchyMetricFromEventFlow

instance regularCauchyMetricChapterTasteGate : ChapterTasteGate RegularCauchyMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMetricFromEventFlow (regularCauchyMetricToEventFlow x) = some x
    exact regularCauchyMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyMetricToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMetricChapterTasteGate

theorem RegularCauchyMetricTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyMetricUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyMetricUp) ∧
        (∀ x : RegularCauchyMetricUp,
          Cont (regularCauchyMetricEncodeBHist x)
            (regularCauchyMetricEncodeBHist x)
            (append (regularCauchyMetricEncodeBHist x) (regularCauchyMetricEncodeBHist x))) := by
  -- BEDC touchpoint anchor: BHist Cont BMark ChapterTasteGate BHistCarrier
  exact
    ⟨⟨regularCauchyMetricBHistCarrier⟩, ⟨regularCauchyMetricChapterTasteGate⟩, by
      intro x
      rfl⟩

end BEDC.Derived.RegularCauchyMetricUp
