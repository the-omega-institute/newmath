import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContinuousIntervalImageUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContinuousIntervalImageUp : Type where
  | mk (B J F V W R E H C P N : BHist) : ContinuousIntervalImageUp
  deriving DecidableEq

def continuousIntervalImageEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: continuousIntervalImageEncodeBHist h
  | BHist.e1 h => BMark.b1 :: continuousIntervalImageEncodeBHist h

def continuousIntervalImageDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (continuousIntervalImageDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (continuousIntervalImageDecodeBHist tail)

private theorem continuousIntervalImageDecode_encode :
    ∀ h : BHist,
      continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def continuousIntervalImageToEventFlow : ContinuousIntervalImageUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousIntervalImageUp.mk B J F V W R E H C P N =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        continuousIntervalImageEncodeBHist B,
        continuousIntervalImageEncodeBHist J,
        continuousIntervalImageEncodeBHist F,
        continuousIntervalImageEncodeBHist V,
        continuousIntervalImageEncodeBHist W,
        continuousIntervalImageEncodeBHist R,
        continuousIntervalImageEncodeBHist E,
        continuousIntervalImageEncodeBHist H,
        continuousIntervalImageEncodeBHist C,
        continuousIntervalImageEncodeBHist P,
        continuousIntervalImageEncodeBHist N]

private def continuousIntervalImageEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => continuousIntervalImageEventAtDefault index rest

def continuousIntervalImageFromEventFlow :
    EventFlow → Option ContinuousIntervalImageUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ContinuousIntervalImageUp.mk
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 1 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 2 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 3 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 4 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 5 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 6 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 7 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 8 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 9 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 10 ef))
      (continuousIntervalImageDecodeBHist (continuousIntervalImageEventAtDefault 11 ef)))

private theorem continuousIntervalImage_round_trip :
    ∀ x : ContinuousIntervalImageUp,
      continuousIntervalImageFromEventFlow (continuousIntervalImageToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B J F V W R E H C P N =>
      change
        some
          (ContinuousIntervalImageUp.mk
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist B))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist J))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist F))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist V))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist W))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist R))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist E))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist H))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist C))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist P))
            (continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist N))) =
          some (ContinuousIntervalImageUp.mk B J F V W R E H C P N)
      rw [continuousIntervalImageDecode_encode B, continuousIntervalImageDecode_encode J,
        continuousIntervalImageDecode_encode F, continuousIntervalImageDecode_encode V,
        continuousIntervalImageDecode_encode W, continuousIntervalImageDecode_encode R,
        continuousIntervalImageDecode_encode E, continuousIntervalImageDecode_encode H,
        continuousIntervalImageDecode_encode C, continuousIntervalImageDecode_encode P,
        continuousIntervalImageDecode_encode N]

private theorem continuousIntervalImageToEventFlow_injective
    {x y : ContinuousIntervalImageUp} :
    continuousIntervalImageToEventFlow x = continuousIntervalImageToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      continuousIntervalImageFromEventFlow (continuousIntervalImageToEventFlow x) =
        continuousIntervalImageFromEventFlow (continuousIntervalImageToEventFlow y) :=
    congrArg continuousIntervalImageFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (continuousIntervalImage_round_trip x).symm
      (Eq.trans hread (continuousIntervalImage_round_trip y)))

private def continuousIntervalImageFields : ContinuousIntervalImageUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContinuousIntervalImageUp.mk B J F V W R E H C P N => [B, J, F, V, W, R, E, H, C, P, N]

private theorem continuousIntervalImage_field_faithful :
    ∀ x y : ContinuousIntervalImageUp,
      continuousIntervalImageFields x = continuousIntervalImageFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 J1 F1 V1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 J2 F2 V2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance continuousIntervalImageBHistCarrier : BHistCarrier ContinuousIntervalImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := continuousIntervalImageToEventFlow
  fromEventFlow := continuousIntervalImageFromEventFlow

instance continuousIntervalImageChapterTasteGate :
    ChapterTasteGate ContinuousIntervalImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change continuousIntervalImageFromEventFlow (continuousIntervalImageToEventFlow x) = some x
    exact continuousIntervalImage_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (continuousIntervalImageToEventFlow_injective heq)

instance continuousIntervalImageFieldFaithful :
    FieldFaithful ContinuousIntervalImageUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := continuousIntervalImageFields
  field_faithful := continuousIntervalImage_field_faithful

def taste_gate : ChapterTasteGate ContinuousIntervalImageUp :=
  -- BEDC touchpoint anchor: BHist BMark
  continuousIntervalImageChapterTasteGate

theorem ContinuousIntervalImageTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      continuousIntervalImageDecodeBHist (continuousIntervalImageEncodeBHist h) = h) ∧
      (∀ x : ContinuousIntervalImageUp,
        continuousIntervalImageFromEventFlow (continuousIntervalImageToEventFlow x) = some x) ∧
        (∀ x y : ContinuousIntervalImageUp,
          continuousIntervalImageToEventFlow x = continuousIntervalImageToEventFlow y → x = y) ∧
          continuousIntervalImageEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨continuousIntervalImageDecode_encode,
      continuousIntervalImage_round_trip,
      (fun _ _ heq => continuousIntervalImageToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContinuousIntervalImageUp
