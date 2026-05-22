import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AdmissibleRepresentationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AdmissibleRepresentationUp : Type where
  | mk (X K W R D E F H C P N : BHist) : AdmissibleRepresentationUp
  deriving DecidableEq

def admissibleRepresentationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: admissibleRepresentationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: admissibleRepresentationEncodeBHist h

def admissibleRepresentationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (admissibleRepresentationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (admissibleRepresentationDecodeBHist tail)

private theorem AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def admissibleRepresentationFields : AdmissibleRepresentationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AdmissibleRepresentationUp.mk X K W R D E F H C P N => [X, K, W, R, D, E, F, H, C, P, N]

def admissibleRepresentationToEventFlow : AdmissibleRepresentationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => admissibleRepresentationFields x |>.map admissibleRepresentationEncodeBHist

private def admissibleRepresentationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => admissibleRepresentationEventAt index rest

def admissibleRepresentationFromEventFlow (ef : EventFlow) :
    Option AdmissibleRepresentationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AdmissibleRepresentationUp.mk
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 0 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 1 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 2 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 3 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 4 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 5 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 6 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 7 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 8 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 9 ef))
      (admissibleRepresentationDecodeBHist (admissibleRepresentationEventAt 10 ef)))

private theorem AdmissibleRepresentationTasteGate_single_carrier_alignment_round_trip
    (x : AdmissibleRepresentationUp) :
    admissibleRepresentationFromEventFlow (admissibleRepresentationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X K W R D E F H C P N =>
      change
        some
          (AdmissibleRepresentationUp.mk
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist X))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist K))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist W))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist R))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist D))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist E))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist F))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist H))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist C))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist P))
            (admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist N))) =
          some (AdmissibleRepresentationUp.mk X K W R D E F H C P N)
      rw [AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode X,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode K,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode W,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode R,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode D,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode E,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode F,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode H,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode C,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode P,
        AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode N]

private theorem AdmissibleRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AdmissibleRepresentationUp} :
    admissibleRepresentationToEventFlow x = admissibleRepresentationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      admissibleRepresentationFromEventFlow (admissibleRepresentationToEventFlow x) =
        admissibleRepresentationFromEventFlow (admissibleRepresentationToEventFlow y) :=
    congrArg admissibleRepresentationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AdmissibleRepresentationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (AdmissibleRepresentationTasteGate_single_carrier_alignment_round_trip y)))

instance admissibleRepresentationBHistCarrier : BHistCarrier AdmissibleRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := admissibleRepresentationToEventFlow
  fromEventFlow := admissibleRepresentationFromEventFlow

instance admissibleRepresentationChapterTasteGate :
    ChapterTasteGate AdmissibleRepresentationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      admissibleRepresentationFromEventFlow (admissibleRepresentationToEventFlow x) = some x
    exact AdmissibleRepresentationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AdmissibleRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem AdmissibleRepresentationTasteGate_single_carrier_alignment :
    (∀ h : BHist, admissibleRepresentationDecodeBHist (admissibleRepresentationEncodeBHist h) = h) ∧
      (∀ x : AdmissibleRepresentationUp,
        admissibleRepresentationFromEventFlow (admissibleRepresentationToEventFlow x) = some x) ∧
        (∀ x y : AdmissibleRepresentationUp,
          admissibleRepresentationToEventFlow x = admissibleRepresentationToEventFlow y → x = y) ∧
          admissibleRepresentationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨AdmissibleRepresentationTasteGate_single_carrier_alignment_decode_encode,
      AdmissibleRepresentationTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AdmissibleRepresentationTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.AdmissibleRepresentationUp
