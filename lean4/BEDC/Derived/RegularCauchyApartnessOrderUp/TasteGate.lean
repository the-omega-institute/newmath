import BEDC.FKernel.Package.Core
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyApartnessOrderUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyApartnessOrderUp : Type where
  | mk
      (source budget direction modulus window positiveBound readback realSeal transport replay
        provenance name : BHist) : RegularCauchyApartnessOrderUp
  deriving DecidableEq

def regularCauchyApartnessOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyApartnessOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyApartnessOrderEncodeBHist h

def regularCauchyApartnessOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyApartnessOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyApartnessOrderDecodeBHist tail)

private theorem regularCauchyApartnessOrderDecodeEncodeBHist :
    ∀ h : BHist,
      regularCauchyApartnessOrderDecodeBHist
        (regularCauchyApartnessOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyApartnessOrderFields :
    RegularCauchyApartnessOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyApartnessOrderUp.mk source budget direction modulus window positiveBound
      readback realSeal transport replay provenance name =>
      [source, budget, direction, modulus, window, positiveBound, readback, realSeal,
        transport, replay, provenance, name]

def regularCauchyApartnessOrderNameRow : RegularCauchyApartnessOrderUp → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyApartnessOrderUp.mk _ _ _ _ _ _ _ _ _ _ _ name => name

def regularCauchyApartnessOrderToEventFlow :
    RegularCauchyApartnessOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyApartnessOrderFields x).map
        regularCauchyApartnessOrderEncodeBHist

def regularCauchyApartnessOrderFromEventFlow :
    EventFlow → Option RegularCauchyApartnessOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | budget :: rest1 =>
          match rest1 with
          | [] => none
          | direction :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | window :: rest4 =>
                      match rest4 with
                      | [] => none
                      | positiveBound :: rest5 =>
                          match rest5 with
                          | [] => none
                          | readback :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | replay :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (RegularCauchyApartnessOrderUp.mk
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            source)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            budget)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            direction)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            modulus)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            window)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            positiveBound)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            readback)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            realSeal)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            transport)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            replay)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            provenance)
                                                          (regularCauchyApartnessOrderDecodeBHist
                                                            name))
                                                  | _ :: _ => none

private theorem regularCauchyApartnessOrder_round_trip :
    ∀ x : RegularCauchyApartnessOrderUp,
      regularCauchyApartnessOrderFromEventFlow
          (regularCauchyApartnessOrderToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source budget direction modulus window positiveBound readback realSeal transport replay
      provenance name =>
      change
        some
          (RegularCauchyApartnessOrderUp.mk
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist source))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist budget))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist direction))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist modulus))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist window))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist positiveBound))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist readback))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist realSeal))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist transport))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist replay))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist provenance))
            (regularCauchyApartnessOrderDecodeBHist
              (regularCauchyApartnessOrderEncodeBHist name))) =
          some
            (RegularCauchyApartnessOrderUp.mk source budget direction modulus window
              positiveBound readback realSeal transport replay provenance name)
      rw [regularCauchyApartnessOrderDecodeEncodeBHist source,
        regularCauchyApartnessOrderDecodeEncodeBHist budget,
        regularCauchyApartnessOrderDecodeEncodeBHist direction,
        regularCauchyApartnessOrderDecodeEncodeBHist modulus,
        regularCauchyApartnessOrderDecodeEncodeBHist window,
        regularCauchyApartnessOrderDecodeEncodeBHist positiveBound,
        regularCauchyApartnessOrderDecodeEncodeBHist readback,
        regularCauchyApartnessOrderDecodeEncodeBHist realSeal,
        regularCauchyApartnessOrderDecodeEncodeBHist transport,
        regularCauchyApartnessOrderDecodeEncodeBHist replay,
        regularCauchyApartnessOrderDecodeEncodeBHist provenance,
        regularCauchyApartnessOrderDecodeEncodeBHist name]

private theorem regularCauchyApartnessOrderToEventFlow_injective
    {x y : RegularCauchyApartnessOrderUp} :
    regularCauchyApartnessOrderToEventFlow x =
      regularCauchyApartnessOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyApartnessOrderFromEventFlow
          (regularCauchyApartnessOrderToEventFlow x) =
        regularCauchyApartnessOrderFromEventFlow
          (regularCauchyApartnessOrderToEventFlow y) :=
    congrArg regularCauchyApartnessOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyApartnessOrder_round_trip x).symm
      (Eq.trans hread (regularCauchyApartnessOrder_round_trip y)))

instance regularCauchyApartnessOrderBHistCarrier :
    BHistCarrier RegularCauchyApartnessOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyApartnessOrderToEventFlow
  fromEventFlow := regularCauchyApartnessOrderFromEventFlow

instance regularCauchyApartnessOrderChapterTasteGate :
    ChapterTasteGate RegularCauchyApartnessOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyApartnessOrderFromEventFlow
          (regularCauchyApartnessOrderToEventFlow x) =
        some x
    exact regularCauchyApartnessOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyApartnessOrderToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyApartnessOrderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyApartnessOrderChapterTasteGate

theorem RegularCauchyApartnessOrderTasteGate_single_carrier_alignment
    [AskSetup] [PackageSetup]
    {x y : RegularCauchyApartnessOrderUp}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyApartnessOrderToEventFlow x =
        regularCauchyApartnessOrderToEventFlow y →
      PkgSig bundle (regularCauchyApartnessOrderNameRow x) pkg →
        PkgSig bundle (regularCauchyApartnessOrderNameRow y) pkg →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg PkgSig
  intro heq _ _
  exact regularCauchyApartnessOrderToEventFlow_injective heq

end BEDC.Derived.RegularCauchyApartnessOrderUp.TasteGate
