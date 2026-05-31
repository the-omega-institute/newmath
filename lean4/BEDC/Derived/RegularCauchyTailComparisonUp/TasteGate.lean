import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailComparisonUp : Type where
  | mk (X Y W D I Z E H C P N : BHist) : RegularCauchyTailComparisonUp
  deriving DecidableEq

def regularCauchyTailComparisonEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailComparisonEncodeBHist h

def regularCauchyTailComparisonDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailComparisonDecodeBHist tail)

private theorem regularCauchyTailComparisonDecode_encode :
    ∀ h : BHist,
      regularCauchyTailComparisonDecodeBHist
          (regularCauchyTailComparisonEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailComparisonToEventFlow : RegularCauchyTailComparisonUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailComparisonUp.mk X Y W D I Z E H C P N =>
      [regularCauchyTailComparisonEncodeBHist X,
        regularCauchyTailComparisonEncodeBHist Y,
        regularCauchyTailComparisonEncodeBHist W,
        regularCauchyTailComparisonEncodeBHist D,
        regularCauchyTailComparisonEncodeBHist I,
        regularCauchyTailComparisonEncodeBHist Z,
        regularCauchyTailComparisonEncodeBHist E,
        regularCauchyTailComparisonEncodeBHist H,
        regularCauchyTailComparisonEncodeBHist C,
        regularCauchyTailComparisonEncodeBHist P,
        regularCauchyTailComparisonEncodeBHist N]

def regularCauchyTailComparisonFromEventFlow :
    EventFlow -> Option RegularCauchyTailComparisonUp
  -- BEDC touchpoint anchor: BHist BMark
  | X :: Y :: W :: D :: I :: Z :: E :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyTailComparisonUp.mk
          (regularCauchyTailComparisonDecodeBHist X)
          (regularCauchyTailComparisonDecodeBHist Y)
          (regularCauchyTailComparisonDecodeBHist W)
          (regularCauchyTailComparisonDecodeBHist D)
          (regularCauchyTailComparisonDecodeBHist I)
          (regularCauchyTailComparisonDecodeBHist Z)
          (regularCauchyTailComparisonDecodeBHist E)
          (regularCauchyTailComparisonDecodeBHist H)
          (regularCauchyTailComparisonDecodeBHist C)
          (regularCauchyTailComparisonDecodeBHist P)
          (regularCauchyTailComparisonDecodeBHist N))
  | _ => none

private theorem regularCauchyTailComparison_round_trip :
    ∀ x : RegularCauchyTailComparisonUp,
      regularCauchyTailComparisonFromEventFlow
          (regularCauchyTailComparisonToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y W D I Z E H C P N =>
      change
        some
            (RegularCauchyTailComparisonUp.mk
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist X))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist Y))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist W))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist D))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist I))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist Z))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist E))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist H))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist C))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist P))
              (regularCauchyTailComparisonDecodeBHist
                (regularCauchyTailComparisonEncodeBHist N))) =
          some (RegularCauchyTailComparisonUp.mk X Y W D I Z E H C P N)
      rw [regularCauchyTailComparisonDecode_encode X,
        regularCauchyTailComparisonDecode_encode Y,
        regularCauchyTailComparisonDecode_encode W,
        regularCauchyTailComparisonDecode_encode D,
        regularCauchyTailComparisonDecode_encode I,
        regularCauchyTailComparisonDecode_encode Z,
        regularCauchyTailComparisonDecode_encode E,
        regularCauchyTailComparisonDecode_encode H,
        regularCauchyTailComparisonDecode_encode C,
        regularCauchyTailComparisonDecode_encode P,
        regularCauchyTailComparisonDecode_encode N]

private theorem regularCauchyTailComparisonToEventFlow_injective
    {x y : RegularCauchyTailComparisonUp} :
    regularCauchyTailComparisonToEventFlow x = regularCauchyTailComparisonToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailComparisonFromEventFlow (regularCauchyTailComparisonToEventFlow x) =
        regularCauchyTailComparisonFromEventFlow (regularCauchyTailComparisonToEventFlow y) :=
    congrArg regularCauchyTailComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailComparison_round_trip x).symm
      (Eq.trans hread (regularCauchyTailComparison_round_trip y)))

instance regularCauchyTailComparisonBHistCarrier :
    BHistCarrier RegularCauchyTailComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailComparisonToEventFlow
  fromEventFlow := regularCauchyTailComparisonFromEventFlow

instance regularCauchyTailComparisonChapterTasteGate :
    ChapterTasteGate RegularCauchyTailComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailComparisonFromEventFlow
          (regularCauchyTailComparisonToEventFlow x) =
        some x
    exact regularCauchyTailComparison_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyTailComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailComparisonChapterTasteGate

theorem RegularCauchyTailComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailComparisonDecodeBHist (regularCauchyTailComparisonEncodeBHist h) = h) ∧
      Nonempty RegularCauchyTailComparisonUp ∧
        regularCauchyTailComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyTailComparisonDecode_encode,
      ⟨RegularCauchyTailComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyTailComparisonUp
