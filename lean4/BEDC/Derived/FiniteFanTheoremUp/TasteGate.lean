import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteFanTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteFanTheoremUp : Type where
  | mk (S C B I W H T P N : BHist) : FiniteFanTheoremUp
  deriving DecidableEq

def FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist :
    BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 :: FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 :: FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist h

def FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
        (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FiniteFanTheoremTasteGate_single_carrier_alignment_fields :
    FiniteFanTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteFanTheoremUp.mk S C B I W H T P N => [S, C, B, I, W, H, T, P, N]

def FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow :
    FiniteFanTheoremUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (FiniteFanTheoremTasteGate_single_carrier_alignment_fields x).map
      FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist

def FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option FiniteFanTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | B :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | W :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | T :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (FiniteFanTheoremUp.mk
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist S)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist C)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist B)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist I)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist W)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist H)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist T)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist P)
                                              (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist N))
                                      | _ :: _ => none

private theorem FiniteFanTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : FiniteFanTheoremUp,
      FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow
        (FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S C B I W H T P N =>
      change
        some
          (FiniteFanTheoremUp.mk
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist S))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist C))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist B))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist I))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist W))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist H))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist T))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist P))
            (FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
              (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (FiniteFanTheoremUp.mk S C B I W H T P N)
      rw [FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode S,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode C,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode B,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode I,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode W,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode H,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode T,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode P,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteFanTheoremUp} :
    FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow x =
      FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow x) =
        FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteFanTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteFanTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance finiteFanTheoremBHistCarrier : BHistCarrier FiniteFanTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow

instance finiteFanTheoremChapterTasteGate : ChapterTasteGate FiniteFanTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow
        (FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact FiniteFanTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate FiniteFanTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteFanTheoremChapterTasteGate

theorem FiniteFanTheoremTasteGate_single_carrier_alignment :
    (forall S C B I W H T P N : BHist,
      FiniteFanTheoremTasteGate_single_carrier_alignment_fields
        (FiniteFanTheoremUp.mk S C B I W H T P N) =
          [S, C, B, I, W, H, T, P, N]) ∧
      (forall h : BHist,
        FiniteFanTheoremTasteGate_single_carrier_alignment_decodeBHist
          (FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist h) = h) ∧
        FiniteFanTheoremTasteGate_single_carrier_alignment_encodeBHist
          (BHist.e1 BHist.Empty) = [BMark.b1] ∧
          Nonempty (ChapterTasteGate FiniteFanTheoremUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  have gate : ChapterTasteGate FiniteFanTheoremUp := {
    round_trip := by
      intro x
      change
        FiniteFanTheoremTasteGate_single_carrier_alignment_fromEventFlow
          (FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow x) = some x
      exact FiniteFanTheoremTasteGate_single_carrier_alignment_round_trip x
    layer_separation := by
      intro x y hxy heq
      exact hxy (FiniteFanTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq) }
  constructor
  · intro S C B I W H T P N
    rfl
  · constructor
    · exact FiniteFanTheoremTasteGate_single_carrier_alignment_decode_encode
    · constructor
      · rfl
      · exact ⟨gate⟩

end BEDC.Derived.FiniteFanTheoremUp
