import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusCompletionSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusCompletionSelectorUp : Type where
  | mk (M W Q D E R H C P N : BHist) : CauchyModulusCompletionSelectorUp
  deriving DecidableEq

def cauchyModulusCompletionSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusCompletionSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusCompletionSelectorEncodeBHist h

def cauchyModulusCompletionSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusCompletionSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusCompletionSelectorDecodeBHist tail)

def cauchyModulusCompletionSelectorFields :
    CauchyModulusCompletionSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusCompletionSelectorUp.mk M W Q D E R H C P N =>
      [M, W, Q, D, E, R, H, C, P, N]

private theorem cauchyModulusCompletionSelector_decode_encode_bhist :
    ∀ h : BHist,
      cauchyModulusCompletionSelectorDecodeBHist
          (cauchyModulusCompletionSelectorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusCompletionSelectorToEventFlow :
    CauchyModulusCompletionSelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyModulusCompletionSelectorFields x).map
      cauchyModulusCompletionSelectorEncodeBHist

def cauchyModulusCompletionSelectorFromEventFlow :
    EventFlow → Option CauchyModulusCompletionSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | W :: rest1 =>
          match rest1 with
          | [] => none
          | Q :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (CauchyModulusCompletionSelectorUp.mk
                                                  (cauchyModulusCompletionSelectorDecodeBHist M)
                                                  (cauchyModulusCompletionSelectorDecodeBHist W)
                                                  (cauchyModulusCompletionSelectorDecodeBHist Q)
                                                  (cauchyModulusCompletionSelectorDecodeBHist D)
                                                  (cauchyModulusCompletionSelectorDecodeBHist E)
                                                  (cauchyModulusCompletionSelectorDecodeBHist R)
                                                  (cauchyModulusCompletionSelectorDecodeBHist H)
                                                  (cauchyModulusCompletionSelectorDecodeBHist C)
                                                  (cauchyModulusCompletionSelectorDecodeBHist P)
                                                  (cauchyModulusCompletionSelectorDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchyModulusCompletionSelector_round_trip :
    ∀ x : CauchyModulusCompletionSelectorUp,
      cauchyModulusCompletionSelectorFromEventFlow
        (cauchyModulusCompletionSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M W Q D E R H C P N =>
      change
        some
          (CauchyModulusCompletionSelectorUp.mk
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist M))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist W))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist Q))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist D))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist E))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist R))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist H))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist C))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist P))
            (cauchyModulusCompletionSelectorDecodeBHist
              (cauchyModulusCompletionSelectorEncodeBHist N))) =
          some (CauchyModulusCompletionSelectorUp.mk M W Q D E R H C P N)
      rw [cauchyModulusCompletionSelector_decode_encode_bhist M,
        cauchyModulusCompletionSelector_decode_encode_bhist W,
        cauchyModulusCompletionSelector_decode_encode_bhist Q,
        cauchyModulusCompletionSelector_decode_encode_bhist D,
        cauchyModulusCompletionSelector_decode_encode_bhist E,
        cauchyModulusCompletionSelector_decode_encode_bhist R,
        cauchyModulusCompletionSelector_decode_encode_bhist H,
        cauchyModulusCompletionSelector_decode_encode_bhist C,
        cauchyModulusCompletionSelector_decode_encode_bhist P,
        cauchyModulusCompletionSelector_decode_encode_bhist N]

private theorem cauchyModulusCompletionSelectorToEventFlow_injective
    {x y : CauchyModulusCompletionSelectorUp} :
    cauchyModulusCompletionSelectorToEventFlow x =
        cauchyModulusCompletionSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusCompletionSelectorFromEventFlow
          (cauchyModulusCompletionSelectorToEventFlow x) =
        cauchyModulusCompletionSelectorFromEventFlow
          (cauchyModulusCompletionSelectorToEventFlow y) :=
    congrArg cauchyModulusCompletionSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusCompletionSelector_round_trip x).symm
      (Eq.trans hread (cauchyModulusCompletionSelector_round_trip y)))

instance cauchyModulusCompletionSelectorBHistCarrier :
    BHistCarrier CauchyModulusCompletionSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusCompletionSelectorToEventFlow
  fromEventFlow := cauchyModulusCompletionSelectorFromEventFlow

instance cauchyModulusCompletionSelectorChapterTasteGate :
    ChapterTasteGate CauchyModulusCompletionSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusCompletionSelectorFromEventFlow
          (cauchyModulusCompletionSelectorToEventFlow x) =
        some x
    exact cauchyModulusCompletionSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusCompletionSelectorToEventFlow_injective heq)

theorem CauchyModulusCompletionSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusCompletionSelectorDecodeBHist
        (cauchyModulusCompletionSelectorEncodeBHist h) = h) ∧
      (∀ x : CauchyModulusCompletionSelectorUp,
        cauchyModulusCompletionSelectorFromEventFlow
          (cauchyModulusCompletionSelectorToEventFlow x) = some x) ∧
      (∀ x y : CauchyModulusCompletionSelectorUp,
        cauchyModulusCompletionSelectorToEventFlow x =
          cauchyModulusCompletionSelectorToEventFlow y → x = y) ∧
      cauchyModulusCompletionSelectorEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      (∃ x y : CauchyModulusCompletionSelectorUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyModulusCompletionSelector_decode_encode_bhist
  constructor
  · exact cauchyModulusCompletionSelector_round_trip
  constructor
  · intro x y heq
    exact cauchyModulusCompletionSelectorToEventFlow_injective heq
  constructor
  · rfl
  · exact
      ⟨CauchyModulusCompletionSelectorUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        CauchyModulusCompletionSelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩

end BEDC.Derived.CauchyModulusCompletionSelectorUp
