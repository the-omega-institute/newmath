import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PolishBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PolishBasisUp : Type where
  | mk (M D K S R I F H C P N : BHist) : PolishBasisUp
  deriving DecidableEq

def polishBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: polishBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: polishBasisEncodeBHist h

def polishBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (polishBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (polishBasisDecodeBHist tail)

private theorem PolishBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, polishBasisDecodeBHist (polishBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def polishBasisFields : PolishBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PolishBasisUp.mk M D K S R I F H C P N => [M, D, K, S, R, I, F, H, C, P, N]

def polishBasisToEventFlow : PolishBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (polishBasisFields x).map polishBasisEncodeBHist

def polishBasisFromEventFlow : EventFlow → Option PolishBasisUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | K :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | R :: rest4 =>
                      match rest4 with
                      | [] => none
                      | I :: rest5 =>
                          match rest5 with
                          | [] => none
                          | F :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (PolishBasisUp.mk
                                                      (polishBasisDecodeBHist M)
                                                      (polishBasisDecodeBHist D)
                                                      (polishBasisDecodeBHist K)
                                                      (polishBasisDecodeBHist S)
                                                      (polishBasisDecodeBHist R)
                                                      (polishBasisDecodeBHist I)
                                                      (polishBasisDecodeBHist F)
                                                      (polishBasisDecodeBHist H)
                                                      (polishBasisDecodeBHist C)
                                                      (polishBasisDecodeBHist P)
                                                      (polishBasisDecodeBHist N))
                                              | _ :: _ => none

private theorem PolishBasisTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PolishBasisUp, polishBasisFromEventFlow (polishBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M D K S R I F H C P N =>
      change
        some
          (PolishBasisUp.mk
            (polishBasisDecodeBHist (polishBasisEncodeBHist M))
            (polishBasisDecodeBHist (polishBasisEncodeBHist D))
            (polishBasisDecodeBHist (polishBasisEncodeBHist K))
            (polishBasisDecodeBHist (polishBasisEncodeBHist S))
            (polishBasisDecodeBHist (polishBasisEncodeBHist R))
            (polishBasisDecodeBHist (polishBasisEncodeBHist I))
            (polishBasisDecodeBHist (polishBasisEncodeBHist F))
            (polishBasisDecodeBHist (polishBasisEncodeBHist H))
            (polishBasisDecodeBHist (polishBasisEncodeBHist C))
            (polishBasisDecodeBHist (polishBasisEncodeBHist P))
            (polishBasisDecodeBHist (polishBasisEncodeBHist N))) =
          some (PolishBasisUp.mk M D K S R I F H C P N)
      rw [PolishBasisTasteGate_single_carrier_alignment_decode_encode M,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode D,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode K,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode S,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode R,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode I,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode F,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode H,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode C,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode P,
        PolishBasisTasteGate_single_carrier_alignment_decode_encode N]

private theorem PolishBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PolishBasisUp} :
    polishBasisToEventFlow x = polishBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      polishBasisFromEventFlow (polishBasisToEventFlow x) =
        polishBasisFromEventFlow (polishBasisToEventFlow y) :=
    congrArg polishBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PolishBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PolishBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem PolishBasisTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : PolishBasisUp, polishBasisFields x = polishBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 D1 K1 S1 R1 I1 F1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 D2 K2 S2 R2 I2 F2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance polishBasisBHistCarrier : BHistCarrier PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := polishBasisToEventFlow
  fromEventFlow := polishBasisFromEventFlow

instance polishBasisChapterTasteGate : ChapterTasteGate PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change polishBasisFromEventFlow (polishBasisToEventFlow x) = some x
    exact PolishBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PolishBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance polishBasisFieldFaithful : FieldFaithful PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := polishBasisFields
  field_faithful := PolishBasisTasteGate_single_carrier_alignment_fields_faithful

instance polishBasisNontrivial : Nontrivial PolishBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PolishBasisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PolishBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PolishBasisTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PolishBasisUp) ∧ Nonempty (FieldFaithful PolishBasisUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial PolishBasisUp) ∧
        polishBasisEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨polishBasisChapterTasteGate⟩, ⟨polishBasisFieldFaithful⟩, ⟨polishBasisNontrivial⟩, rfl⟩

end BEDC.Derived.PolishBasisUp
