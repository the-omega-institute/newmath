import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerContinuityPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BrouwerContinuityPrincipleUp : Type where
  | mk (B Q S W R E M H C P N : BHist) : BrouwerContinuityPrincipleUp
  deriving DecidableEq

def brouwerContinuityPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerContinuityPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerContinuityPrincipleEncodeBHist h

def brouwerContinuityPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerContinuityPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerContinuityPrincipleDecodeBHist tail)

private theorem brouwerContinuityPrincipleDecode_encode_bhist :
    ∀ h : BHist,
      brouwerContinuityPrincipleDecodeBHist (brouwerContinuityPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def brouwerContinuityPrincipleToEventFlow : BrouwerContinuityPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerContinuityPrincipleUp.mk B Q S W R E M H C P N =>
      [[BMark.b0],
        brouwerContinuityPrincipleEncodeBHist B,
        [BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        brouwerContinuityPrincipleEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        brouwerContinuityPrincipleEncodeBHist N]

private def brouwerContinuityPrincipleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerContinuityPrincipleEventAtDefault index rest

def brouwerContinuityPrincipleFromEventFlow (ef : EventFlow) :
    Option BrouwerContinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerContinuityPrincipleUp.mk
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 1 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 3 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 5 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 7 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 9 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 11 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 13 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 15 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 17 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 19 ef))
      (brouwerContinuityPrincipleDecodeBHist
        (brouwerContinuityPrincipleEventAtDefault 21 ef)))

private theorem brouwerContinuityPrinciple_round_trip :
    ∀ x : BrouwerContinuityPrincipleUp,
      brouwerContinuityPrincipleFromEventFlow
          (brouwerContinuityPrincipleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B Q S W R E M H C P N =>
      change
        some
          (BrouwerContinuityPrincipleUp.mk
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist B))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist Q))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist S))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist W))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist R))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist E))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist M))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist H))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist C))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist P))
            (brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist N))) =
          some (BrouwerContinuityPrincipleUp.mk B Q S W R E M H C P N)
      rw [brouwerContinuityPrincipleDecode_encode_bhist B,
        brouwerContinuityPrincipleDecode_encode_bhist Q,
        brouwerContinuityPrincipleDecode_encode_bhist S,
        brouwerContinuityPrincipleDecode_encode_bhist W,
        brouwerContinuityPrincipleDecode_encode_bhist R,
        brouwerContinuityPrincipleDecode_encode_bhist E,
        brouwerContinuityPrincipleDecode_encode_bhist M,
        brouwerContinuityPrincipleDecode_encode_bhist H,
        brouwerContinuityPrincipleDecode_encode_bhist C,
        brouwerContinuityPrincipleDecode_encode_bhist P,
        brouwerContinuityPrincipleDecode_encode_bhist N]

private theorem brouwerContinuityPrincipleToEventFlow_injective
    {x y : BrouwerContinuityPrincipleUp} :
    brouwerContinuityPrincipleToEventFlow x =
      brouwerContinuityPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerContinuityPrincipleFromEventFlow
          (brouwerContinuityPrincipleToEventFlow x) =
        brouwerContinuityPrincipleFromEventFlow
          (brouwerContinuityPrincipleToEventFlow y) :=
    congrArg brouwerContinuityPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (brouwerContinuityPrinciple_round_trip x).symm
      (Eq.trans hread (brouwerContinuityPrinciple_round_trip y)))

instance brouwerContinuityPrincipleBHistCarrier :
    BHistCarrier BrouwerContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerContinuityPrincipleToEventFlow
  fromEventFlow := brouwerContinuityPrincipleFromEventFlow

instance brouwerContinuityPrincipleChapterTasteGate :
    ChapterTasteGate BrouwerContinuityPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      brouwerContinuityPrincipleFromEventFlow (brouwerContinuityPrincipleToEventFlow x) =
        some x
    exact brouwerContinuityPrinciple_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (brouwerContinuityPrincipleToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BrouwerContinuityPrincipleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brouwerContinuityPrincipleChapterTasteGate

theorem BrouwerContinuityPrincipleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BrouwerContinuityPrincipleUp) ∧
      brouwerContinuityPrincipleEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ h : BHist,
          brouwerContinuityPrincipleDecodeBHist
              (brouwerContinuityPrincipleEncodeBHist h) =
            h) ∧
          (∀ x : BrouwerContinuityPrincipleUp,
            brouwerContinuityPrincipleFromEventFlow
                (brouwerContinuityPrincipleToEventFlow x) =
              some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨brouwerContinuityPrincipleChapterTasteGate⟩, rfl,
      brouwerContinuityPrincipleDecode_encode_bhist,
      brouwerContinuityPrinciple_round_trip⟩

end BEDC.Derived.BrouwerContinuityPrincipleUp
