import BEDC.Derived.CauchyModulusChoiceUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusChoiceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def cauchyModulusChoiceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusChoiceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusChoiceEncodeBHist h

def cauchyModulusChoiceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusChoiceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusChoiceDecodeBHist tail)

private theorem cauchyModulusChoice_decode_encode_bhist :
    ∀ h : BHist,
      cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusChoiceFields :
    BEDC.Derived.CauchyModulusChoiceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchyModulusChoiceUp.mk M N W Q D R H C P L =>
      [M, N, W, Q, D, R, H, C, P, L]

def cauchyModulusChoiceToEventFlow :
    BEDC.Derived.CauchyModulusChoiceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.CauchyModulusChoiceUp.mk M N W Q D R H C P L =>
      cauchyModulusChoiceEncodeBHist M ::
        cauchyModulusChoiceEncodeBHist N ::
          cauchyModulusChoiceEncodeBHist W ::
            cauchyModulusChoiceEncodeBHist Q ::
              cauchyModulusChoiceEncodeBHist D ::
                cauchyModulusChoiceEncodeBHist R ::
                  cauchyModulusChoiceEncodeBHist H ::
                    cauchyModulusChoiceEncodeBHist C ::
                      cauchyModulusChoiceEncodeBHist P ::
                        cauchyModulusChoiceEncodeBHist L :: []

def cauchyModulusChoiceFromEventFlow :
    EventFlow → Option BEDC.Derived.CauchyModulusChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    match flow with
    | [] => none
    | M :: rest0 =>
      match rest0 with
      | [] => none
      | N :: rest1 =>
        match rest1 with
        | [] => none
        | W :: rest2 =>
          match rest2 with
          | [] => none
          | Q :: rest3 =>
            match rest3 with
            | [] => none
            | D :: rest4 =>
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
                      | L :: rest9 =>
                        match rest9 with
                        | [] =>
                          some
                            (BEDC.Derived.CauchyModulusChoiceUp.mk
                              (cauchyModulusChoiceDecodeBHist M)
                              (cauchyModulusChoiceDecodeBHist N)
                              (cauchyModulusChoiceDecodeBHist W)
                              (cauchyModulusChoiceDecodeBHist Q)
                              (cauchyModulusChoiceDecodeBHist D)
                              (cauchyModulusChoiceDecodeBHist R)
                              (cauchyModulusChoiceDecodeBHist H)
                              (cauchyModulusChoiceDecodeBHist C)
                              (cauchyModulusChoiceDecodeBHist P)
                              (cauchyModulusChoiceDecodeBHist L))
                        | _ :: _ => none

private theorem cauchyModulusChoice_round_trip
    (x : BEDC.Derived.CauchyModulusChoiceUp) :
    cauchyModulusChoiceFromEventFlow (cauchyModulusChoiceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M N W Q D R H C P L =>
      change
        some
            (BEDC.Derived.CauchyModulusChoiceUp.mk
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist M))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist N))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist W))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist Q))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist D))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist R))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist H))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist C))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist P))
              (cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist L))) =
          some (BEDC.Derived.CauchyModulusChoiceUp.mk M N W Q D R H C P L)
      rw [cauchyModulusChoice_decode_encode_bhist M,
        cauchyModulusChoice_decode_encode_bhist N,
        cauchyModulusChoice_decode_encode_bhist W,
        cauchyModulusChoice_decode_encode_bhist Q,
        cauchyModulusChoice_decode_encode_bhist D,
        cauchyModulusChoice_decode_encode_bhist R,
        cauchyModulusChoice_decode_encode_bhist H,
        cauchyModulusChoice_decode_encode_bhist C,
        cauchyModulusChoice_decode_encode_bhist P,
        cauchyModulusChoice_decode_encode_bhist L]

private theorem cauchyModulusChoiceToEventFlow_injective
    {x y : BEDC.Derived.CauchyModulusChoiceUp} :
    cauchyModulusChoiceToEventFlow x = cauchyModulusChoiceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusChoiceFromEventFlow (cauchyModulusChoiceToEventFlow x) =
        cauchyModulusChoiceFromEventFlow (cauchyModulusChoiceToEventFlow y) :=
    congrArg cauchyModulusChoiceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusChoice_round_trip x).symm
      (Eq.trans hread (cauchyModulusChoice_round_trip y)))

instance cauchyModulusChoiceBHistCarrier :
    BHistCarrier BEDC.Derived.CauchyModulusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusChoiceToEventFlow
  fromEventFlow := cauchyModulusChoiceFromEventFlow

instance cauchyModulusChoiceChapterTasteGate :
    ChapterTasteGate BEDC.Derived.CauchyModulusChoiceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusChoiceFromEventFlow (cauchyModulusChoiceToEventFlow x) = some x
    exact cauchyModulusChoice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusChoiceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BEDC.Derived.CauchyModulusChoiceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusChoiceChapterTasteGate

theorem CauchyModulusChoiceTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyModulusChoiceDecodeBHist (cauchyModulusChoiceEncodeBHist h) = h) ∧
      (∀ x : BEDC.Derived.CauchyModulusChoiceUp,
        cauchyModulusChoiceFromEventFlow (cauchyModulusChoiceToEventFlow x) = some x) ∧
      (∀ x y : BEDC.Derived.CauchyModulusChoiceUp,
        cauchyModulusChoiceToEventFlow x = cauchyModulusChoiceToEventFlow y -> x = y) ∧
      cauchyModulusChoiceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨cauchyModulusChoice_decode_encode_bhist,
      cauchyModulusChoice_round_trip,
      (fun _ _ heq => cauchyModulusChoiceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyModulusChoiceUp
