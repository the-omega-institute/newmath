import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLocatedLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLocatedLimitUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (window tolerance readback interval locator realSeal transport replay provenance
      localName : BHist) : RegularCauchyLocatedLimitUp
  deriving DecidableEq

def regularCauchyLocatedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLocatedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLocatedLimitEncodeBHist h

def regularCauchyLocatedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLocatedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLocatedLimitDecodeBHist tail)

private theorem regularCauchyLocatedLimit_decode_encode :
    ∀ h : BHist,
      regularCauchyLocatedLimitDecodeBHist
          (regularCauchyLocatedLimitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLocatedLimitFields :
    RegularCauchyLocatedLimitUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyLocatedLimitUp.mk window tolerance readback interval locator realSeal
      transport replay provenance localName =>
      [window, tolerance, readback, interval, locator, realSeal, transport, replay,
        provenance, localName]

def regularCauchyLocatedLimitToEventFlow :
    RegularCauchyLocatedLimitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyLocatedLimitFields x).map regularCauchyLocatedLimitEncodeBHist

def regularCauchyLocatedLimitFromEventFlow :
    EventFlow → Option RegularCauchyLocatedLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | window :: tolerance :: readback :: interval :: locator :: realSeal :: transport ::
      replay :: provenance :: localName :: [] =>
      some
        (RegularCauchyLocatedLimitUp.mk
          (regularCauchyLocatedLimitDecodeBHist window)
          (regularCauchyLocatedLimitDecodeBHist tolerance)
          (regularCauchyLocatedLimitDecodeBHist readback)
          (regularCauchyLocatedLimitDecodeBHist interval)
          (regularCauchyLocatedLimitDecodeBHist locator)
          (regularCauchyLocatedLimitDecodeBHist realSeal)
          (regularCauchyLocatedLimitDecodeBHist transport)
          (regularCauchyLocatedLimitDecodeBHist replay)
          (regularCauchyLocatedLimitDecodeBHist provenance)
          (regularCauchyLocatedLimitDecodeBHist localName))
  | _ => none

private theorem regularCauchyLocatedLimit_round_trip :
    ∀ x : RegularCauchyLocatedLimitUp,
      regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk window tolerance readback interval locator realSeal transport replay provenance
      localName =>
      simp only [regularCauchyLocatedLimitToEventFlow, regularCauchyLocatedLimitFields,
        regularCauchyLocatedLimitFromEventFlow, List.map_cons, List.map_nil,
        regularCauchyLocatedLimit_decode_encode]

private theorem regularCauchyLocatedLimitToEventFlow_injective
    {x y : RegularCauchyLocatedLimitUp} :
    regularCauchyLocatedLimitToEventFlow x =
        regularCauchyLocatedLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          regularCauchyLocatedLimitFromEventFlow
            (regularCauchyLocatedLimitToEventFlow x) :=
        (regularCauchyLocatedLimit_round_trip x).symm
      _ =
          regularCauchyLocatedLimitFromEventFlow
            (regularCauchyLocatedLimitToEventFlow y) :=
        congrArg regularCauchyLocatedLimitFromEventFlow hxy
      _ = some y := regularCauchyLocatedLimit_round_trip y
  exact Option.some.inj optionEq

instance regularCauchyLocatedLimitBHistCarrier :
    BHistCarrier RegularCauchyLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLocatedLimitToEventFlow
  fromEventFlow := regularCauchyLocatedLimitFromEventFlow

instance regularCauchyLocatedLimitChapterTasteGate :
    ChapterTasteGate RegularCauchyLocatedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLocatedLimitFromEventFlow
          (regularCauchyLocatedLimitToEventFlow x) =
        some x
    exact regularCauchyLocatedLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLocatedLimitToEventFlow_injective heq)

end BEDC.Derived.RegularCauchyLocatedLimitUp
