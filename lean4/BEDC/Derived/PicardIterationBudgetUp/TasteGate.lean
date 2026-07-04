import BEDC.Derived.PicardIterationBudgetUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PicardIterationBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def picardIterationBudgetFields :
    PicardIterationBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PicardIterationBudgetUp.mk S K W D E H C P N => [S, K, W, D, E, H, C, P, N]

def picardIterationBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: picardIterationBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: picardIterationBudgetEncodeBHist h

def picardIterationBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (picardIterationBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (picardIterationBudgetDecodeBHist tail)

private theorem PicardIterationBudgetTasteGate_decode_encode :
    ∀ h : BHist,
      picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def picardIterationBudgetToEventFlow :
    PicardIterationBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map picardIterationBudgetEncodeBHist (picardIterationBudgetFields x)

def picardIterationBudgetFromEventFlow :
    EventFlow → Option PicardIterationBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (PicardIterationBudgetUp.mk
                                              (picardIterationBudgetDecodeBHist S)
                                              (picardIterationBudgetDecodeBHist K)
                                              (picardIterationBudgetDecodeBHist W)
                                              (picardIterationBudgetDecodeBHist D)
                                              (picardIterationBudgetDecodeBHist E)
                                              (picardIterationBudgetDecodeBHist H)
                                              (picardIterationBudgetDecodeBHist C)
                                              (picardIterationBudgetDecodeBHist P)
                                              (picardIterationBudgetDecodeBHist N))
                                      | _ :: _ => none

private theorem PicardIterationBudgetTasteGate_round_trip :
    ∀ x : PicardIterationBudgetUp,
      picardIterationBudgetFromEventFlow (picardIterationBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S K W D E H C P N =>
      change
        some
          (PicardIterationBudgetUp.mk
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist S))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist K))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist W))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist D))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist E))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist H))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist C))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist P))
            (picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist N))) =
          some (PicardIterationBudgetUp.mk S K W D E H C P N)
      rw [PicardIterationBudgetTasteGate_decode_encode S,
        PicardIterationBudgetTasteGate_decode_encode K,
        PicardIterationBudgetTasteGate_decode_encode W,
        PicardIterationBudgetTasteGate_decode_encode D,
        PicardIterationBudgetTasteGate_decode_encode E,
        PicardIterationBudgetTasteGate_decode_encode H,
        PicardIterationBudgetTasteGate_decode_encode C,
        PicardIterationBudgetTasteGate_decode_encode P,
        PicardIterationBudgetTasteGate_decode_encode N]

private theorem PicardIterationBudgetTasteGate_toEventFlow_injective
    {x y : PicardIterationBudgetUp} :
    picardIterationBudgetToEventFlow x = picardIterationBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      picardIterationBudgetFromEventFlow (picardIterationBudgetToEventFlow x) =
        picardIterationBudgetFromEventFlow (picardIterationBudgetToEventFlow y) :=
    congrArg picardIterationBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PicardIterationBudgetTasteGate_round_trip x).symm
      (Eq.trans hread (PicardIterationBudgetTasteGate_round_trip y)))

private theorem PicardIterationBudgetTasteGate_fields :
    ∀ x y : PicardIterationBudgetUp,
      picardIterationBudgetFields x = picardIterationBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 K1 W1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 K2 W2 D2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance picardIterationBudgetBHistCarrier : BHistCarrier PicardIterationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := picardIterationBudgetToEventFlow
  fromEventFlow := picardIterationBudgetFromEventFlow

instance picardIterationBudgetChapterTasteGate :
    ChapterTasteGate PicardIterationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change picardIterationBudgetFromEventFlow (picardIterationBudgetToEventFlow x) = some x
    exact PicardIterationBudgetTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PicardIterationBudgetTasteGate_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PicardIterationBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  picardIterationBudgetChapterTasteGate

instance picardIterationBudgetFieldFaithful : FieldFaithful PicardIterationBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := picardIterationBudgetFields
  field_faithful := PicardIterationBudgetTasteGate_fields

theorem PicardIterationBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist, picardIterationBudgetDecodeBHist (picardIterationBudgetEncodeBHist h) = h) ∧
      (∀ x : PicardIterationBudgetUp,
        picardIterationBudgetFromEventFlow (picardIterationBudgetToEventFlow x) = some x) ∧
      (∀ x y : PicardIterationBudgetUp,
        picardIterationBudgetToEventFlow x = picardIterationBudgetToEventFlow y → x = y) ∧
      picardIterationBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨PicardIterationBudgetTasteGate_decode_encode,
      PicardIterationBudgetTasteGate_round_trip,
      fun _x _y heq => PicardIterationBudgetTasteGate_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.PicardIterationBudgetUp
