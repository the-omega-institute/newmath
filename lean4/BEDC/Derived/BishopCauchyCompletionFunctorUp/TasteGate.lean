import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopCauchyCompletionFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopCauchyCompletionFunctorUp : Type where
  | mk (S T R E F U H C P N : BHist) : BishopCauchyCompletionFunctorUp
  deriving DecidableEq

def bishopCauchyCompletionFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopCauchyCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopCauchyCompletionFunctorEncodeBHist h

def bishopCauchyCompletionFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopCauchyCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopCauchyCompletionFunctorDecodeBHist tail)

private theorem BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopCauchyCompletionFunctorDecodeBHist
        (bishopCauchyCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopCauchyCompletionFunctorFields : BishopCauchyCompletionFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopCauchyCompletionFunctorUp.mk S T R E F U H C P N => [S, T, R, E, F, U, H, C, P, N]

def bishopCauchyCompletionFunctorToEventFlow :
    BishopCauchyCompletionFunctorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (bishopCauchyCompletionFunctorFields x).map
      bishopCauchyCompletionFunctorEncodeBHist

private def bishopCauchyCompletionFunctorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopCauchyCompletionFunctorEventAtDefault index rest

def bishopCauchyCompletionFunctorFromEventFlow :
    EventFlow → Option BishopCauchyCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (BishopCauchyCompletionFunctorUp.mk
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 0 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 1 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 2 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 3 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 4 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 5 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 6 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 7 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 8 ef))
        (bishopCauchyCompletionFunctorDecodeBHist
          (bishopCauchyCompletionFunctorEventAtDefault 9 ef)))

private theorem BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopCauchyCompletionFunctorUp,
      bishopCauchyCompletionFunctorFromEventFlow
        (bishopCauchyCompletionFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T R E F U H C P N =>
      change
        some
          (BishopCauchyCompletionFunctorUp.mk
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist S))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist T))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist R))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist E))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist F))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist U))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist H))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist C))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist P))
            (bishopCauchyCompletionFunctorDecodeBHist
              (bishopCauchyCompletionFunctorEncodeBHist N))) =
          some (BishopCauchyCompletionFunctorUp.mk S T R E F U H C P N)
      rw [BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode S,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode T,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode R,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode E,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode F,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode U,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode H,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode C,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode P,
        BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode N]

private theorem BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BishopCauchyCompletionFunctorUp} :
    bishopCauchyCompletionFunctorToEventFlow x =
      bishopCauchyCompletionFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopCauchyCompletionFunctorFromEventFlow
          (bishopCauchyCompletionFunctorToEventFlow x) =
        bishopCauchyCompletionFunctorFromEventFlow
          (bishopCauchyCompletionFunctorToEventFlow y) :=
    congrArg bishopCauchyCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance bishopCauchyCompletionFunctorBHistCarrier :
    BHistCarrier BishopCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopCauchyCompletionFunctorToEventFlow
  fromEventFlow := bishopCauchyCompletionFunctorFromEventFlow

instance bishopCauchyCompletionFunctorChapterTasteGate :
    ChapterTasteGate BishopCauchyCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopCauchyCompletionFunctorFromEventFlow
        (bishopCauchyCompletionFunctorToEventFlow x) = some x
    exact BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate BishopCauchyCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopCauchyCompletionFunctorChapterTasteGate

theorem BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopCauchyCompletionFunctorDecodeBHist
        (bishopCauchyCompletionFunctorEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BishopCauchyCompletionFunctorUp) ∧
        Nonempty (ChapterTasteGate BishopCauchyCompletionFunctorUp) ∧
          bishopCauchyCompletionFunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopCauchyCompletionFunctorTasteGate_single_carrier_alignment_decode,
      ⟨bishopCauchyCompletionFunctorBHistCarrier⟩,
      ⟨bishopCauchyCompletionFunctorChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.BishopCauchyCompletionFunctorUp
