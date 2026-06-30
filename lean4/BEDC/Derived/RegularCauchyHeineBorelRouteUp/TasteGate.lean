import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyHeineBorelRouteUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyHeineBorelRouteUp : Type where
  | mk (I D S Q E W F H C P N : BHist) : RegularCauchyHeineBorelRouteUp
  deriving DecidableEq

def regularCauchyHeineBorelRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyHeineBorelRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyHeineBorelRouteEncodeBHist h

def regularCauchyHeineBorelRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyHeineBorelRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyHeineBorelRouteDecodeBHist tail)

private theorem RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyHeineBorelRouteDecodeBHist
          (regularCauchyHeineBorelRouteEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyHeineBorelRouteFields :
    RegularCauchyHeineBorelRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyHeineBorelRouteUp.mk I D S Q E W F H C P N =>
      [I, D, S, Q, E, W, F, H, C, P, N]

def regularCauchyHeineBorelRouteToEventFlow :
    RegularCauchyHeineBorelRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyHeineBorelRouteUp.mk I D S Q E W F H C P N =>
      [regularCauchyHeineBorelRouteEncodeBHist I,
        regularCauchyHeineBorelRouteEncodeBHist D,
        regularCauchyHeineBorelRouteEncodeBHist S,
        regularCauchyHeineBorelRouteEncodeBHist Q,
        regularCauchyHeineBorelRouteEncodeBHist E,
        regularCauchyHeineBorelRouteEncodeBHist W,
        regularCauchyHeineBorelRouteEncodeBHist F,
        regularCauchyHeineBorelRouteEncodeBHist H,
        regularCauchyHeineBorelRouteEncodeBHist C,
        regularCauchyHeineBorelRouteEncodeBHist P,
        regularCauchyHeineBorelRouteEncodeBHist N]

def regularCauchyHeineBorelRouteFromEventFlow :
    EventFlow → Option RegularCauchyHeineBorelRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: D :: S :: Q :: E :: W :: F :: H :: C :: P :: N :: [] =>
      some
        (RegularCauchyHeineBorelRouteUp.mk
          (regularCauchyHeineBorelRouteDecodeBHist I)
          (regularCauchyHeineBorelRouteDecodeBHist D)
          (regularCauchyHeineBorelRouteDecodeBHist S)
          (regularCauchyHeineBorelRouteDecodeBHist Q)
          (regularCauchyHeineBorelRouteDecodeBHist E)
          (regularCauchyHeineBorelRouteDecodeBHist W)
          (regularCauchyHeineBorelRouteDecodeBHist F)
          (regularCauchyHeineBorelRouteDecodeBHist H)
          (regularCauchyHeineBorelRouteDecodeBHist C)
          (regularCauchyHeineBorelRouteDecodeBHist P)
          (regularCauchyHeineBorelRouteDecodeBHist N))
  | _ => none

private theorem RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyHeineBorelRouteUp,
      regularCauchyHeineBorelRouteFromEventFlow
          (regularCauchyHeineBorelRouteToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I D S Q E W F H C P N =>
      rw [regularCauchyHeineBorelRouteToEventFlow,
        regularCauchyHeineBorelRouteFromEventFlow,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode I,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode D,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode S,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode E,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode W,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode F,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode H,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode C,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode P,
        RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyHeineBorelRouteUp} :
    regularCauchyHeineBorelRouteToEventFlow x =
        regularCauchyHeineBorelRouteToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyHeineBorelRouteFromEventFlow
          (regularCauchyHeineBorelRouteToEventFlow x) =
        regularCauchyHeineBorelRouteFromEventFlow
          (regularCauchyHeineBorelRouteToEventFlow y) :=
    congrArg regularCauchyHeineBorelRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyHeineBorelRouteBHistCarrier :
    BHistCarrier RegularCauchyHeineBorelRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyHeineBorelRouteToEventFlow
  fromEventFlow := regularCauchyHeineBorelRouteFromEventFlow

instance regularCauchyHeineBorelRouteChapterTasteGate :
    ChapterTasteGate RegularCauchyHeineBorelRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyHeineBorelRouteFromEventFlow
          (regularCauchyHeineBorelRouteToEventFlow x) =
        some x
    exact RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyHeineBorelRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyHeineBorelRouteChapterTasteGate

theorem RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment :
    (∀ I D S Q E W F H C P N : BHist,
      regularCauchyHeineBorelRouteFields
          (RegularCauchyHeineBorelRouteUp.mk I D S Q E W F H C P N) =
        [I, D, S, Q, E, W, F, H, C, P, N]) ∧
      (∀ h : BHist,
        regularCauchyHeineBorelRouteDecodeBHist
            (regularCauchyHeineBorelRouteEncodeBHist h) =
          h) ∧
        regularCauchyHeineBorelRouteEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨by
      intro I D S Q E W F H C P N
      rfl,
      RegularCauchyHeineBorelRouteTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.RegularCauchyHeineBorelRouteUp.TasteGate
