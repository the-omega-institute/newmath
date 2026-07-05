import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicNormalFormUp : Type where
  | mk (S M E Z R L H C P N : BHist) : DyadicNormalFormUp
  deriving DecidableEq

def dyadicNormalFormEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicNormalFormEncodeBHist h

def dyadicNormalFormDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicNormalFormDecodeBHist tail)

private theorem dyadicNormalFormDecode_encode :
    ∀ h : BHist, dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicNormalFormFields : DyadicNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicNormalFormUp.mk S M E Z R L H C P N => [S, M, E, Z, R, L, H, C, P, N]

def dyadicNormalFormToEventFlow : DyadicNormalFormUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicNormalFormFields x).map dyadicNormalFormEncodeBHist

private def dyadicNormalFormEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicNormalFormEventAt index rest

def dyadicNormalFormFromEventFlow (ef : EventFlow) : Option DyadicNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicNormalFormUp.mk
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 0 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 1 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 2 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 3 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 4 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 5 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 6 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 7 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 8 ef))
      (dyadicNormalFormDecodeBHist (dyadicNormalFormEventAt 9 ef)))

private theorem dyadicNormalForm_round_trip (x : DyadicNormalFormUp) :
    dyadicNormalFormFromEventFlow (dyadicNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S M E Z R L H C P N =>
      change
        some
          (DyadicNormalFormUp.mk
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist S))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist M))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist E))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist Z))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist R))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist L))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist H))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist C))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist P))
            (dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist N))) =
          some (DyadicNormalFormUp.mk S M E Z R L H C P N)
      rw [dyadicNormalFormDecode_encode S, dyadicNormalFormDecode_encode M,
        dyadicNormalFormDecode_encode E, dyadicNormalFormDecode_encode Z,
        dyadicNormalFormDecode_encode R, dyadicNormalFormDecode_encode L,
        dyadicNormalFormDecode_encode H, dyadicNormalFormDecode_encode C,
        dyadicNormalFormDecode_encode P, dyadicNormalFormDecode_encode N]

private theorem dyadicNormalFormToEventFlow_injective {x y : DyadicNormalFormUp} :
    dyadicNormalFormToEventFlow x = dyadicNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicNormalFormFromEventFlow (dyadicNormalFormToEventFlow x) =
        dyadicNormalFormFromEventFlow (dyadicNormalFormToEventFlow y) :=
    congrArg dyadicNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicNormalForm_round_trip x).symm
      (Eq.trans hread (dyadicNormalForm_round_trip y)))

instance dyadicNormalFormBHistCarrier : BHistCarrier DyadicNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicNormalFormToEventFlow
  fromEventFlow := dyadicNormalFormFromEventFlow

instance dyadicNormalFormChapterTasteGate : ChapterTasteGate DyadicNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicNormalFormFromEventFlow (dyadicNormalFormToEventFlow x) = some x
    exact dyadicNormalForm_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicNormalFormToEventFlow_injective heq)

def dyadicNormalFormTasteGate : ChapterTasteGate DyadicNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicNormalFormChapterTasteGate

theorem DyadicNormalFormTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicNormalFormDecodeBHist (dyadicNormalFormEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicNormalFormUp) ∧
        Nonempty (ChapterTasteGate DyadicNormalFormUp) ∧
          dyadicNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicNormalFormDecode_encode
  · constructor
    · exact Nonempty.intro dyadicNormalFormBHistCarrier
    · constructor
      · exact Nonempty.intro dyadicNormalFormChapterTasteGate
      · rfl

end BEDC.Derived.DyadicNormalFormUp
