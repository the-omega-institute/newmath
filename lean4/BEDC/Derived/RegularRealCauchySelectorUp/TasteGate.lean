import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularRealCauchySelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularRealCauchySelectorUp : Type where
  | mk (R0 M D W Q E H C P N : BHist) : RegularRealCauchySelectorUp
  deriving DecidableEq

def regularRealCauchySelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularRealCauchySelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularRealCauchySelectorEncodeBHist h

def regularRealCauchySelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularRealCauchySelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularRealCauchySelectorDecodeBHist tail)

private theorem RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularRealCauchySelectorFields : RegularRealCauchySelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularRealCauchySelectorUp.mk R0 M D W Q E H C P N => [R0, M, D, W, Q, E, H, C, P, N]

def regularRealCauchySelectorToEventFlow : RegularRealCauchySelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularRealCauchySelectorFields x).map regularRealCauchySelectorEncodeBHist

private def regularRealCauchySelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularRealCauchySelectorEventAtDefault index rest

def regularRealCauchySelectorFromEventFlow (ef : EventFlow) :
    Option RegularRealCauchySelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularRealCauchySelectorUp.mk
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 0 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 1 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 2 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 3 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 4 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 5 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 6 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 7 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 8 ef))
      (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEventAtDefault 9 ef)))

private theorem regularRealCauchySelector_round_trip :
    ∀ x : RegularRealCauchySelectorUp,
      regularRealCauchySelectorFromEventFlow (regularRealCauchySelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 M D W Q E H C P N =>
      change
        some
            (RegularRealCauchySelectorUp.mk
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist R0))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist M))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist D))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist W))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist Q))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist E))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist H))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist C))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist P))
              (regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist N))) =
          some (RegularRealCauchySelectorUp.mk R0 M D W Q E H C P N)
      rw [RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode R0,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode M,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode D,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode W,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode Q,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode E,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode H,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode C,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode P,
        RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode N]

private theorem regularRealCauchySelectorToEventFlow_injective
    {x y : RegularRealCauchySelectorUp} :
    regularRealCauchySelectorToEventFlow x = regularRealCauchySelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularRealCauchySelectorFromEventFlow (regularRealCauchySelectorToEventFlow x) =
        regularRealCauchySelectorFromEventFlow (regularRealCauchySelectorToEventFlow y) :=
    congrArg regularRealCauchySelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularRealCauchySelector_round_trip x).symm
      (Eq.trans hread (regularRealCauchySelector_round_trip y)))

instance regularRealCauchySelectorBHistCarrier : BHistCarrier RegularRealCauchySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularRealCauchySelectorToEventFlow
  fromEventFlow := regularRealCauchySelectorFromEventFlow

instance regularRealCauchySelectorChapterTasteGate :
    ChapterTasteGate RegularRealCauchySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularRealCauchySelectorFromEventFlow (regularRealCauchySelectorToEventFlow x) =
      some x
    exact regularRealCauchySelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularRealCauchySelectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularRealCauchySelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularRealCauchySelectorChapterTasteGate

theorem RegularRealCauchySelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularRealCauchySelectorDecodeBHist (regularRealCauchySelectorEncodeBHist h) = h) ∧
      (∀ x : RegularRealCauchySelectorUp,
        regularRealCauchySelectorFromEventFlow (regularRealCauchySelectorToEventFlow x) =
          some x) ∧
        (∀ x y : RegularRealCauchySelectorUp,
          regularRealCauchySelectorToEventFlow x =
            regularRealCauchySelectorToEventFlow y → x = y) ∧
          regularRealCauchySelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularRealCauchySelectorTasteGate_single_carrier_alignment_decode,
      regularRealCauchySelector_round_trip,
      (fun _ _ heq => regularRealCauchySelectorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularRealCauchySelectorUp
