import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailFilterCofinalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailFilterCofinalityUp : Type where
  | mk (R C T F H P N : BHist) : RegularCauchyTailFilterCofinalityUp
  deriving DecidableEq

def regularCauchyTailFilterCofinalityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailFilterCofinalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailFilterCofinalityEncodeBHist h

def regularCauchyTailFilterCofinalityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailFilterCofinalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailFilterCofinalityDecodeBHist tail)

private theorem RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailFilterCofinalityFields :
    RegularCauchyTailFilterCofinalityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailFilterCofinalityUp.mk R C T F H P N => [R, C, T, F, H, P, N]

def regularCauchyTailFilterCofinalityToEventFlow :
    RegularCauchyTailFilterCofinalityUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyTailFilterCofinalityFields x).map
      regularCauchyTailFilterCofinalityEncodeBHist

private def regularCauchyTailFilterCofinalityEventAtDefault :
    Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyTailFilterCofinalityEventAtDefault index rest

def regularCauchyTailFilterCofinalityFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTailFilterCofinalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailFilterCofinalityUp.mk
      (regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEventAtDefault 0 ef))
      (regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEventAtDefault 1 ef))
      (regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEventAtDefault 2 ef))
      (regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEventAtDefault 3 ef))
      (regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEventAtDefault 4 ef))
      (regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEventAtDefault 5 ef))
      (regularCauchyTailFilterCofinalityDecodeBHist
        (regularCauchyTailFilterCofinalityEventAtDefault 6 ef)))

theorem RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment :
    forall x : RegularCauchyTailFilterCofinalityUp,
      regularCauchyTailFilterCofinalityFromEventFlow
        (regularCauchyTailFilterCofinalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R C T F H P N =>
      change
        some
          (RegularCauchyTailFilterCofinalityUp.mk
            (regularCauchyTailFilterCofinalityDecodeBHist
              (regularCauchyTailFilterCofinalityEncodeBHist R))
            (regularCauchyTailFilterCofinalityDecodeBHist
              (regularCauchyTailFilterCofinalityEncodeBHist C))
            (regularCauchyTailFilterCofinalityDecodeBHist
              (regularCauchyTailFilterCofinalityEncodeBHist T))
            (regularCauchyTailFilterCofinalityDecodeBHist
              (regularCauchyTailFilterCofinalityEncodeBHist F))
            (regularCauchyTailFilterCofinalityDecodeBHist
              (regularCauchyTailFilterCofinalityEncodeBHist H))
            (regularCauchyTailFilterCofinalityDecodeBHist
              (regularCauchyTailFilterCofinalityEncodeBHist P))
            (regularCauchyTailFilterCofinalityDecodeBHist
              (regularCauchyTailFilterCofinalityEncodeBHist N))) =
          some (RegularCauchyTailFilterCofinalityUp.mk R C T F H P N)
      rw [RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode R,
        RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode C,
        RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode T,
        RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode F,
        RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode H,
        RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode P,
        RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyTailFilterCofinalityUp} :
    regularCauchyTailFilterCofinalityToEventFlow x =
        regularCauchyTailFilterCofinalityToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailFilterCofinalityFromEventFlow
          (regularCauchyTailFilterCofinalityToEventFlow x) =
        regularCauchyTailFilterCofinalityFromEventFlow
          (regularCauchyTailFilterCofinalityToEventFlow y) :=
    congrArg regularCauchyTailFilterCofinalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment x).symm
      (Eq.trans hread
        (RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment y)))

instance regularCauchyTailFilterCofinalityBHistCarrier :
    BHistCarrier RegularCauchyTailFilterCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailFilterCofinalityToEventFlow
  fromEventFlow := regularCauchyTailFilterCofinalityFromEventFlow

instance regularCauchyTailFilterCofinalityChapterTasteGate :
    ChapterTasteGate RegularCauchyTailFilterCofinalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailFilterCofinalityFromEventFlow
        (regularCauchyTailFilterCofinalityToEventFlow x) = some x
    exact RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTailFilterCofinalityTasteGate_single_carrier_alignment_injective heq)

end BEDC.Derived.RegularCauchyTailFilterCofinalityUp
