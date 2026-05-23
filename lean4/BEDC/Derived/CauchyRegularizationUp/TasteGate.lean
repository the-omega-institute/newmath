import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRegularizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRegularizationUp : Type where
  | mk (S M D W R E H C P N : BHist) : CauchyRegularizationUp
  deriving DecidableEq

def cauchyRegularizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRegularizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRegularizationEncodeBHist h

def cauchyRegularizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRegularizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRegularizationDecodeBHist tail)

private theorem cauchyRegularizationDecode_encode_bhist :
    ∀ h : BHist,
      cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyRegularizationToEventFlow : CauchyRegularizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRegularizationUp.mk S M D W R E H C P N =>
      [cauchyRegularizationEncodeBHist S,
        cauchyRegularizationEncodeBHist M,
        cauchyRegularizationEncodeBHist D,
        cauchyRegularizationEncodeBHist W,
        cauchyRegularizationEncodeBHist R,
        cauchyRegularizationEncodeBHist E,
        cauchyRegularizationEncodeBHist H,
        cauchyRegularizationEncodeBHist C,
        cauchyRegularizationEncodeBHist P,
        cauchyRegularizationEncodeBHist N]

def cauchyRegularizationFromEventFlow : EventFlow → Option CauchyRegularizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (CauchyRegularizationUp.mk
                                                  (cauchyRegularizationDecodeBHist S)
                                                  (cauchyRegularizationDecodeBHist M)
                                                  (cauchyRegularizationDecodeBHist D)
                                                  (cauchyRegularizationDecodeBHist W)
                                                  (cauchyRegularizationDecodeBHist R)
                                                  (cauchyRegularizationDecodeBHist E)
                                                  (cauchyRegularizationDecodeBHist H)
                                                  (cauchyRegularizationDecodeBHist C)
                                                  (cauchyRegularizationDecodeBHist P)
                                                  (cauchyRegularizationDecodeBHist N))
                                          | _ :: _ => none

private theorem cauchyRegularization_round_trip :
    ∀ x : CauchyRegularizationUp,
      cauchyRegularizationFromEventFlow (cauchyRegularizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M D W R E H C P N =>
      change
        some
          (CauchyRegularizationUp.mk
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist S))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist M))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist D))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist W))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist R))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist E))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist H))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist C))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist P))
            (cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist N))) =
          some (CauchyRegularizationUp.mk S M D W R E H C P N)
      rw [cauchyRegularizationDecode_encode_bhist S,
        cauchyRegularizationDecode_encode_bhist M,
        cauchyRegularizationDecode_encode_bhist D,
        cauchyRegularizationDecode_encode_bhist W,
        cauchyRegularizationDecode_encode_bhist R,
        cauchyRegularizationDecode_encode_bhist E,
        cauchyRegularizationDecode_encode_bhist H,
        cauchyRegularizationDecode_encode_bhist C,
        cauchyRegularizationDecode_encode_bhist P,
        cauchyRegularizationDecode_encode_bhist N]

private theorem cauchyRegularizationToEventFlow_injective
    {x y : CauchyRegularizationUp} :
    cauchyRegularizationToEventFlow x = cauchyRegularizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRegularizationFromEventFlow (cauchyRegularizationToEventFlow x) =
        cauchyRegularizationFromEventFlow (cauchyRegularizationToEventFlow y) :=
    congrArg cauchyRegularizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyRegularization_round_trip x).symm
      (Eq.trans hread (cauchyRegularization_round_trip y)))

instance cauchyRegularizationBHistCarrier : BHistCarrier CauchyRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRegularizationToEventFlow
  fromEventFlow := cauchyRegularizationFromEventFlow

instance cauchyRegularizationChapterTasteGate : ChapterTasteGate CauchyRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRegularizationFromEventFlow (cauchyRegularizationToEventFlow x) = some x
    exact cauchyRegularization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRegularizationToEventFlow_injective heq)

theorem CauchyRegularizationTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyRegularizationUp) ∧
      Nonempty (ChapterTasteGate CauchyRegularizationUp) ∧
        ∃ x : CauchyRegularizationUp,
          cauchyRegularizationToEventFlow x =
            cauchyRegularizationToEventFlow
              (CauchyRegularizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨cauchyRegularizationBHistCarrier⟩
  · constructor
    · exact ⟨cauchyRegularizationChapterTasteGate⟩
    · exact
        ⟨CauchyRegularizationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          rfl⟩

namespace TasteGate

theorem CauchyRegularizationTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRegularizationDecodeBHist (cauchyRegularizationEncodeBHist h) = h) ∧
      (∀ x : CauchyRegularizationUp,
        cauchyRegularizationFromEventFlow (cauchyRegularizationToEventFlow x) = some x) ∧
        (∀ x y : CauchyRegularizationUp,
          cauchyRegularizationToEventFlow x = cauchyRegularizationToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate CauchyRegularizationUp) ∧
            cauchyRegularizationEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cauchyRegularizationDecode_encode_bhist,
      cauchyRegularization_round_trip,
      (fun _ _ heq => cauchyRegularizationToEventFlow_injective heq),
      ⟨cauchyRegularizationChapterTasteGate⟩,
      rfl⟩

end TasteGate

end BEDC.Derived.CauchyRegularizationUp
