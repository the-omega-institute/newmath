import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RapidCauchyNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RapidCauchyNameUp : Type where
  | mk (R0 S D Q E H C P N : BHist) : RapidCauchyNameUp
  deriving DecidableEq

def rapidCauchyNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rapidCauchyNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rapidCauchyNameEncodeBHist h

def rapidCauchyNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rapidCauchyNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rapidCauchyNameDecodeBHist tail)

private theorem rapidCauchyNameDecode_encode :
    ∀ h : BHist,
      rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rapidCauchyNameFields : RapidCauchyNameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RapidCauchyNameUp.mk R0 S D Q E H C P N => [R0, S, D, Q, E, H, C, P, N]

def rapidCauchyNameToEventFlow : RapidCauchyNameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rapidCauchyNameFields x).map rapidCauchyNameEncodeBHist

private def rapidCauchyNameEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => rapidCauchyNameEventAtDefault index rest

def rapidCauchyNameFromEventFlow (ef : EventFlow) : Option RapidCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RapidCauchyNameUp.mk
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 0 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 1 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 2 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 3 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 4 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 5 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 6 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 7 ef))
      (rapidCauchyNameDecodeBHist (rapidCauchyNameEventAtDefault 8 ef)))

private theorem rapidCauchyName_round_trip :
    ∀ x : RapidCauchyNameUp,
      rapidCauchyNameFromEventFlow (rapidCauchyNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 S D Q E H C P N =>
      change
        some
          (RapidCauchyNameUp.mk
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist R0))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist S))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist D))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist Q))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist E))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist H))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist C))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist P))
            (rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist N))) =
          some (RapidCauchyNameUp.mk R0 S D Q E H C P N)
      rw [rapidCauchyNameDecode_encode R0, rapidCauchyNameDecode_encode S,
        rapidCauchyNameDecode_encode D, rapidCauchyNameDecode_encode Q,
        rapidCauchyNameDecode_encode E, rapidCauchyNameDecode_encode H,
        rapidCauchyNameDecode_encode C, rapidCauchyNameDecode_encode P,
        rapidCauchyNameDecode_encode N]

private theorem rapidCauchyNameToEventFlow_injective
    {x y : RapidCauchyNameUp} :
    rapidCauchyNameToEventFlow x = rapidCauchyNameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rapidCauchyNameFromEventFlow (rapidCauchyNameToEventFlow x) =
        rapidCauchyNameFromEventFlow (rapidCauchyNameToEventFlow y) :=
    congrArg rapidCauchyNameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rapidCauchyName_round_trip x).symm
      (Eq.trans hread (rapidCauchyName_round_trip y)))

instance rapidCauchyNameBHistCarrier :
    BHistCarrier RapidCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rapidCauchyNameToEventFlow
  fromEventFlow := rapidCauchyNameFromEventFlow

instance rapidCauchyNameChapterTasteGate :
    ChapterTasteGate RapidCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rapidCauchyNameFromEventFlow (rapidCauchyNameToEventFlow x) = some x
    exact rapidCauchyName_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rapidCauchyNameToEventFlow_injective heq)

theorem RapidCauchyNameTasteGate_single_carrier_alignment :
    (∀ h : BHist, rapidCauchyNameDecodeBHist (rapidCauchyNameEncodeBHist h) = h) ∧
      (∀ x : RapidCauchyNameUp,
        rapidCauchyNameFromEventFlow (rapidCauchyNameToEventFlow x) = some x) ∧
      (∀ x y : RapidCauchyNameUp,
        rapidCauchyNameToEventFlow x = rapidCauchyNameToEventFlow y → x = y) ∧
      rapidCauchyNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨rapidCauchyNameDecode_encode,
      rapidCauchyName_round_trip,
      fun _ _ heq => rapidCauchyNameToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RapidCauchyNameUp
