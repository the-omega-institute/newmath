import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchySequentialCompletenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchySequentialCompletenessUp : Type where
  | mk (D S R M L U H C P N : BHist) : RegularCauchySequentialCompletenessUp
  deriving DecidableEq

def regularCauchySequentialCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchySequentialCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchySequentialCompletenessEncodeBHist h

def regularCauchySequentialCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchySequentialCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchySequentialCompletenessDecodeBHist tail)

private theorem RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchySequentialCompletenessFields :
    RegularCauchySequentialCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchySequentialCompletenessUp.mk D S R M L U H C P N =>
      [D, S, R, M, L, U, H, C, P, N]

def regularCauchySequentialCompletenessToEventFlow :
    RegularCauchySequentialCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchySequentialCompletenessEncodeBHist
        (regularCauchySequentialCompletenessFields x)

private def regularCauchySequentialCompletenessRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchySequentialCompletenessRawAt index rest

def regularCauchySequentialCompletenessFromEventFlow :
    EventFlow → Option RegularCauchySequentialCompletenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (RegularCauchySequentialCompletenessUp.mk
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 0 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 1 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 2 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 3 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 4 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 5 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 6 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 7 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 8 flow))
          (regularCauchySequentialCompletenessDecodeBHist
            (regularCauchySequentialCompletenessRawAt 9 flow)))

private theorem RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchySequentialCompletenessUp,
      regularCauchySequentialCompletenessFromEventFlow
        (regularCauchySequentialCompletenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R M L U H C P N =>
      change
        some
          (RegularCauchySequentialCompletenessUp.mk
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist D))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist S))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist R))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist M))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist L))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist U))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist H))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist C))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist P))
            (regularCauchySequentialCompletenessDecodeBHist
              (regularCauchySequentialCompletenessEncodeBHist N))) =
          some (RegularCauchySequentialCompletenessUp.mk D S R M L U H C P N)
      rw [RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode D,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode S,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode R,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode M,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode L,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode U,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode H,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode C,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode P,
        RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchySequentialCompletenessUp} :
    regularCauchySequentialCompletenessToEventFlow x =
      regularCauchySequentialCompletenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchySequentialCompletenessFromEventFlow
          (regularCauchySequentialCompletenessToEventFlow x) =
        regularCauchySequentialCompletenessFromEventFlow
          (regularCauchySequentialCompletenessToEventFlow y) :=
    congrArg regularCauchySequentialCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchySequentialCompletenessBHistCarrier :
    BHistCarrier RegularCauchySequentialCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchySequentialCompletenessToEventFlow
  fromEventFlow := regularCauchySequentialCompletenessFromEventFlow

instance regularCauchySequentialCompletenessChapterTasteGate :
    ChapterTasteGate RegularCauchySequentialCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchySequentialCompletenessFromEventFlow
        (regularCauchySequentialCompletenessToEventFlow x) = some x
    exact RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchySequentialCompletenessDecodeBHist
        (regularCauchySequentialCompletenessEncodeBHist h) = h) ∧
      (∀ x : RegularCauchySequentialCompletenessUp,
        regularCauchySequentialCompletenessFromEventFlow
          (regularCauchySequentialCompletenessToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchySequentialCompletenessUp,
          regularCauchySequentialCompletenessToEventFlow x =
            regularCauchySequentialCompletenessToEventFlow y → x = y) ∧
          regularCauchySequentialCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_decode,
      RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact
          RegularCauchySequentialCompletenessUpTasteGate_single_carrier_alignment_toEventFlow_injective
            heq,
      rfl⟩

end BEDC.Derived.RegularCauchySequentialCompletenessUp
