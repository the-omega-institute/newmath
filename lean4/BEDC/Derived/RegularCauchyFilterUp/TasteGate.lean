import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFilterUp : Type where
  | mk (B R T D M E H C P N : BHist) : RegularCauchyFilterUp
  deriving DecidableEq

def regularCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFilterEncodeBHist h

def regularCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFilterDecodeBHist tail)

private theorem regularCauchyFilter_decode_encode :
    ∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFilterToEventFlow : RegularCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFilterUp.mk B R T D M E H C P N =>
      [regularCauchyFilterEncodeBHist B, regularCauchyFilterEncodeBHist R,
        regularCauchyFilterEncodeBHist T, regularCauchyFilterEncodeBHist D,
        regularCauchyFilterEncodeBHist M, regularCauchyFilterEncodeBHist E,
        regularCauchyFilterEncodeBHist H, regularCauchyFilterEncodeBHist C,
        regularCauchyFilterEncodeBHist P, regularCauchyFilterEncodeBHist N]

def regularCauchyFilterFromEventFlow (flow : EventFlow) : Option RegularCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | B :: rest =>
      match rest with
      | [] => none
      | R :: rest =>
          match rest with
          | [] => none
          | T :: rest =>
              match rest with
              | [] => none
              | D :: rest =>
                  match rest with
                  | [] => none
                  | M :: rest =>
                      match rest with
                      | [] => none
                      | E :: rest =>
                          match rest with
                          | [] => none
                          | H :: rest =>
                              match rest with
                              | [] => none
                              | C :: rest =>
                                  match rest with
                                  | [] => none
                                  | P :: rest =>
                                      match rest with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (RegularCauchyFilterUp.mk
                                                  (regularCauchyFilterDecodeBHist B)
                                                  (regularCauchyFilterDecodeBHist R)
                                                  (regularCauchyFilterDecodeBHist T)
                                                  (regularCauchyFilterDecodeBHist D)
                                                  (regularCauchyFilterDecodeBHist M)
                                                  (regularCauchyFilterDecodeBHist E)
                                                  (regularCauchyFilterDecodeBHist H)
                                                  (regularCauchyFilterDecodeBHist C)
                                                  (regularCauchyFilterDecodeBHist P)
                                                  (regularCauchyFilterDecodeBHist N))
                                          | _ :: _ => none

private theorem regularCauchyFilter_round_trip :
    ∀ x : RegularCauchyFilterUp,
      regularCauchyFilterFromEventFlow (regularCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B R T D M E H C P N =>
      rw [regularCauchyFilterToEventFlow, regularCauchyFilterFromEventFlow,
        regularCauchyFilter_decode_encode B, regularCauchyFilter_decode_encode R,
        regularCauchyFilter_decode_encode T, regularCauchyFilter_decode_encode D,
        regularCauchyFilter_decode_encode M, regularCauchyFilter_decode_encode E,
        regularCauchyFilter_decode_encode H, regularCauchyFilter_decode_encode C,
        regularCauchyFilter_decode_encode P, regularCauchyFilter_decode_encode N]

private theorem regularCauchyFilterToEventFlow_injective {x y : RegularCauchyFilterUp} :
    regularCauchyFilterToEventFlow x = regularCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFilterFromEventFlow (regularCauchyFilterToEventFlow x) =
        regularCauchyFilterFromEventFlow (regularCauchyFilterToEventFlow y) :=
    congrArg regularCauchyFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyFilter_round_trip x).symm
      (Eq.trans hread (regularCauchyFilter_round_trip y)))

instance regularCauchyFilterBHistCarrier : BHistCarrier RegularCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFilterToEventFlow
  fromEventFlow := regularCauchyFilterFromEventFlow

instance regularCauchyFilterChapterTasteGate : ChapterTasteGate RegularCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyFilterFromEventFlow (regularCauchyFilterToEventFlow x) = some x
    exact regularCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyFilterToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFilterChapterTasteGate

theorem RegularCauchyFilterTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyFilterDecodeBHist (regularCauchyFilterEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyFilterUp,
        regularCauchyFilterFromEventFlow (regularCauchyFilterToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyFilterUp,
        regularCauchyFilterToEventFlow x = regularCauchyFilterToEventFlow y → x = y) ∧
      regularCauchyFilterEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyFilter_decode_encode,
      regularCauchyFilter_round_trip,
      fun _ _ heq => regularCauchyFilterToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyFilterUp
