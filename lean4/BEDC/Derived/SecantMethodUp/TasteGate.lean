import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SecantMethodUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SecantMethodUp : Type where
  | mk (F X Y D R W Q E H C P N : BHist) : SecantMethodUp
  deriving DecidableEq

def secantMethodTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b0, BMark.b1, BMark.b1]

def secantMethodEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: secantMethodEncodeBHist h
  | BHist.e1 h => BMark.b1 :: secantMethodEncodeBHist h

def secantMethodDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (secantMethodDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (secantMethodDecodeBHist tail)

private theorem SecantMethodTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, secantMethodDecodeBHist (secantMethodEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def secantMethodFields : SecantMethodUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SecantMethodUp.mk F X Y D R W Q E H C P N => [F, X, Y, D, R, W, Q, E, H, C, P, N]

def secantMethodToEventFlow : SecantMethodUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SecantMethodUp.mk F X Y D R W Q E H C P N =>
      [secantMethodTag,
        secantMethodEncodeBHist F,
        secantMethodEncodeBHist X,
        secantMethodEncodeBHist Y,
        secantMethodEncodeBHist D,
        secantMethodEncodeBHist R,
        secantMethodEncodeBHist W,
        secantMethodEncodeBHist Q,
        secantMethodEncodeBHist E,
        secantMethodEncodeBHist H,
        secantMethodEncodeBHist C,
        secantMethodEncodeBHist P,
        secantMethodEncodeBHist N]

private def secantMethodEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => secantMethodEventAt index rest

def secantMethodFromEventFlow : EventFlow → Option SecantMethodUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (SecantMethodUp.mk
          (secantMethodDecodeBHist (secantMethodEventAt 1 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 2 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 3 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 4 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 5 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 6 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 7 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 8 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 9 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 10 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 11 ef))
          (secantMethodDecodeBHist (secantMethodEventAt 12 ef)))

private theorem SecantMethodTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SecantMethodUp, secantMethodFromEventFlow (secantMethodToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F X Y D R W Q E H C P N =>
      change
        some
          (SecantMethodUp.mk
            (secantMethodDecodeBHist (secantMethodEncodeBHist F))
            (secantMethodDecodeBHist (secantMethodEncodeBHist X))
            (secantMethodDecodeBHist (secantMethodEncodeBHist Y))
            (secantMethodDecodeBHist (secantMethodEncodeBHist D))
            (secantMethodDecodeBHist (secantMethodEncodeBHist R))
            (secantMethodDecodeBHist (secantMethodEncodeBHist W))
            (secantMethodDecodeBHist (secantMethodEncodeBHist Q))
            (secantMethodDecodeBHist (secantMethodEncodeBHist E))
            (secantMethodDecodeBHist (secantMethodEncodeBHist H))
            (secantMethodDecodeBHist (secantMethodEncodeBHist C))
            (secantMethodDecodeBHist (secantMethodEncodeBHist P))
            (secantMethodDecodeBHist (secantMethodEncodeBHist N))) =
          some (SecantMethodUp.mk F X Y D R W Q E H C P N)
      rw [SecantMethodTasteGate_single_carrier_alignment_decode_encode F,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode X,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode Y,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode D,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode R,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode W,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode Q,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode E,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode H,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode C,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode P,
        SecantMethodTasteGate_single_carrier_alignment_decode_encode N]

private theorem SecantMethodTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SecantMethodUp} :
    secantMethodToEventFlow x = secantMethodToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      secantMethodFromEventFlow (secantMethodToEventFlow x) =
        secantMethodFromEventFlow (secantMethodToEventFlow y) :=
    congrArg secantMethodFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SecantMethodTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (SecantMethodTasteGate_single_carrier_alignment_round_trip y)))

private theorem SecantMethodTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : SecantMethodUp, secantMethodFields x = secantMethodFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 X1 Y1 D1 R1 W1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 X2 Y2 D2 R2 W2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance secantMethodBHistCarrier : BHistCarrier SecantMethodUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := secantMethodToEventFlow
  fromEventFlow := secantMethodFromEventFlow

instance secantMethodChapterTasteGate : ChapterTasteGate SecantMethodUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change secantMethodFromEventFlow (secantMethodToEventFlow x) = some x
    exact SecantMethodTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SecantMethodTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem SecantMethodTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SecantMethodUp) ∧
      Nonempty (ChapterTasteGate SecantMethodUp) ∧
        (∀ x : SecantMethodUp, secantMethodFromEventFlow (secantMethodToEventFlow x) = some x) ∧
          (∀ x y : SecantMethodUp, secantMethodFields x = secantMethodFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨secantMethodBHistCarrier⟩, ⟨secantMethodChapterTasteGate⟩,
      SecantMethodTasteGate_single_carrier_alignment_round_trip,
      SecantMethodTasteGate_single_carrier_alignment_fields_faithful⟩

end BEDC.Derived.SecantMethodUp
