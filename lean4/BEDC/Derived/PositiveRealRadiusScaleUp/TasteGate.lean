import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PositiveRealRadiusScaleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PositiveRealRadiusScaleUp : Type where
  | mk (U E D S Q F H C P N : BHist) : PositiveRealRadiusScaleUp
  deriving DecidableEq

def positiveRealRadiusScaleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: positiveRealRadiusScaleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: positiveRealRadiusScaleEncodeBHist h

def positiveRealRadiusScaleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (positiveRealRadiusScaleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (positiveRealRadiusScaleDecodeBHist tail)

private theorem positiveRealRadiusScale_decode_encode_bhist :
    ∀ h : BHist,
      positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem positiveRealRadiusScale_mk_congr
    {U U' E E' D D' S S' Q Q' F F' H H' C C' P P' N N' : BHist}
    (hU : U' = U) (hE : E' = E) (hD : D' = D) (hS : S' = S) (hQ : Q' = Q)
    (hF : F' = F) (hH : H' = H) (hC : C' = C) (hP : P' = P)
    (hN : N' = N) :
    PositiveRealRadiusScaleUp.mk U' E' D' S' Q' F' H' C' P' N' =
      PositiveRealRadiusScaleUp.mk U E D S Q F H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hU
  cases hE
  cases hD
  cases hS
  cases hQ
  cases hF
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def positiveRealRadiusScaleFields : PositiveRealRadiusScaleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PositiveRealRadiusScaleUp.mk U E D S Q F H C P N => [U, E, D, S, Q, F, H, C, P, N]

def positiveRealRadiusScaleToEventFlow : PositiveRealRadiusScaleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (positiveRealRadiusScaleFields x).map positiveRealRadiusScaleEncodeBHist

private def positiveRealRadiusScaleRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => positiveRealRadiusScaleRawAt index rest

def positiveRealRadiusScaleFromEventFlow (flow : EventFlow) : Option PositiveRealRadiusScaleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PositiveRealRadiusScaleUp.mk
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 0 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 1 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 2 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 3 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 4 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 5 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 6 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 7 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 8 flow))
      (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleRawAt 9 flow)))

private theorem positiveRealRadiusScale_round_trip :
    ∀ x : PositiveRealRadiusScaleUp,
      positiveRealRadiusScaleFromEventFlow (positiveRealRadiusScaleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U E D S Q F H C P N =>
      change
        some
          (PositiveRealRadiusScaleUp.mk
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist U))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist E))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist D))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist S))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist Q))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist F))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist H))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist C))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist P))
            (positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist N))) =
          some (PositiveRealRadiusScaleUp.mk U E D S Q F H C P N)
      exact
        congrArg some
          (positiveRealRadiusScale_mk_congr
            (positiveRealRadiusScale_decode_encode_bhist U)
            (positiveRealRadiusScale_decode_encode_bhist E)
            (positiveRealRadiusScale_decode_encode_bhist D)
            (positiveRealRadiusScale_decode_encode_bhist S)
            (positiveRealRadiusScale_decode_encode_bhist Q)
            (positiveRealRadiusScale_decode_encode_bhist F)
            (positiveRealRadiusScale_decode_encode_bhist H)
            (positiveRealRadiusScale_decode_encode_bhist C)
            (positiveRealRadiusScale_decode_encode_bhist P)
            (positiveRealRadiusScale_decode_encode_bhist N))

private theorem positiveRealRadiusScaleToEventFlow_injective {x y : PositiveRealRadiusScaleUp} :
    positiveRealRadiusScaleToEventFlow x = positiveRealRadiusScaleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      positiveRealRadiusScaleFromEventFlow (positiveRealRadiusScaleToEventFlow x) =
        positiveRealRadiusScaleFromEventFlow (positiveRealRadiusScaleToEventFlow y) :=
    congrArg positiveRealRadiusScaleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (positiveRealRadiusScale_round_trip x).symm
      (Eq.trans hread (positiveRealRadiusScale_round_trip y)))

private theorem positiveRealRadiusScale_fields_faithful :
    ∀ x y : PositiveRealRadiusScaleUp,
      positiveRealRadiusScaleFields x = positiveRealRadiusScaleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ E₁ D₁ S₁ Q₁ F₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk U₂ E₂ D₂ S₂ Q₂ F₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hU tail0
          injection tail0 with hE tail1
          injection tail1 with hD tail2
          injection tail2 with hS tail3
          injection tail3 with hQ tail4
          injection tail4 with hF tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hU
          subst hE
          subst hD
          subst hS
          subst hQ
          subst hF
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance positiveRealRadiusScaleBHistCarrier : BHistCarrier PositiveRealRadiusScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := positiveRealRadiusScaleToEventFlow
  fromEventFlow := positiveRealRadiusScaleFromEventFlow

instance positiveRealRadiusScaleChapterTasteGate : ChapterTasteGate PositiveRealRadiusScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change positiveRealRadiusScaleFromEventFlow (positiveRealRadiusScaleToEventFlow x) =
      some x
    exact positiveRealRadiusScale_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (positiveRealRadiusScaleToEventFlow_injective heq)

instance positiveRealRadiusScaleFieldFaithful : FieldFaithful PositiveRealRadiusScaleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := positiveRealRadiusScaleFields
  field_faithful := positiveRealRadiusScale_fields_faithful

def taste_gate : ChapterTasteGate PositiveRealRadiusScaleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  positiveRealRadiusScaleChapterTasteGate

theorem PositiveRealRadiusScaleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      positiveRealRadiusScaleDecodeBHist (positiveRealRadiusScaleEncodeBHist h) = h) ∧
      (∀ x : PositiveRealRadiusScaleUp,
        positiveRealRadiusScaleFromEventFlow (positiveRealRadiusScaleToEventFlow x) =
          some x) ∧
        (∀ x y : PositiveRealRadiusScaleUp,
          positiveRealRadiusScaleToEventFlow x = positiveRealRadiusScaleToEventFlow y →
            x = y) ∧
          positiveRealRadiusScaleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact positiveRealRadiusScale_decode_encode_bhist
  · constructor
    · exact positiveRealRadiusScale_round_trip
    · constructor
      · intro x y heq
        exact positiveRealRadiusScaleToEventFlow_injective heq
      · rfl

end BEDC.Derived.PositiveRealRadiusScaleUp
