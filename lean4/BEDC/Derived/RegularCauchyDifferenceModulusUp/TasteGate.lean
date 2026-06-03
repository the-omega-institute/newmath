import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDifferenceModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDifferenceModulusUp : Type where
  | mk (X Y WX WY QX QY Delta M E H C P N : BHist) :
      RegularCauchyDifferenceModulusUp
  deriving DecidableEq

def regularCauchyDifferenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDifferenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDifferenceModulusEncodeBHist h

def regularCauchyDifferenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDifferenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDifferenceModulusDecodeBHist tail)

private theorem regularCauchyDifferenceModulusDecode_encode :
    ∀ h : BHist,
      regularCauchyDifferenceModulusDecodeBHist
          (regularCauchyDifferenceModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDifferenceModulusToEventFlow :
    RegularCauchyDifferenceModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyDifferenceModulusUp.mk X Y WX WY QX QY Delta M E H C P N =>
      [regularCauchyDifferenceModulusEncodeBHist X,
        regularCauchyDifferenceModulusEncodeBHist Y,
        regularCauchyDifferenceModulusEncodeBHist WX,
        regularCauchyDifferenceModulusEncodeBHist WY,
        regularCauchyDifferenceModulusEncodeBHist QX,
        regularCauchyDifferenceModulusEncodeBHist QY,
        regularCauchyDifferenceModulusEncodeBHist Delta,
        regularCauchyDifferenceModulusEncodeBHist M,
        regularCauchyDifferenceModulusEncodeBHist E,
        regularCauchyDifferenceModulusEncodeBHist H,
        regularCauchyDifferenceModulusEncodeBHist C,
        regularCauchyDifferenceModulusEncodeBHist P,
        regularCauchyDifferenceModulusEncodeBHist N]

def regularCauchyDifferenceModulusFromEventFlow :
    EventFlow → Option RegularCauchyDifferenceModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest =>
      match rest with
      | [] => none
      | Y :: rest =>
          match rest with
          | [] => none
          | WX :: rest =>
              match rest with
              | [] => none
              | WY :: rest =>
                  match rest with
                  | [] => none
                  | QX :: rest =>
                      match rest with
                      | [] => none
                      | QY :: rest =>
                          match rest with
                          | [] => none
                          | Delta :: rest =>
                              match rest with
                              | [] => none
                              | M :: rest =>
                                  match rest with
                                  | [] => none
                                  | E :: rest =>
                                      match rest with
                                      | [] => none
                                      | H :: rest =>
                                          match rest with
                                          | [] => none
                                          | C :: rest =>
                                              match rest with
                                              | [] => none
                                              | P :: rest =>
                                                  match rest with
                                                  | [] => none
                                                  | N :: rest =>
                                                      match rest with
                                                      | [] =>
                                                          some
                                                            (RegularCauchyDifferenceModulusUp.mk
                                                              (regularCauchyDifferenceModulusDecodeBHist X)
                                                              (regularCauchyDifferenceModulusDecodeBHist Y)
                                                              (regularCauchyDifferenceModulusDecodeBHist WX)
                                                              (regularCauchyDifferenceModulusDecodeBHist WY)
                                                              (regularCauchyDifferenceModulusDecodeBHist QX)
                                                              (regularCauchyDifferenceModulusDecodeBHist QY)
                                                              (regularCauchyDifferenceModulusDecodeBHist Delta)
                                                              (regularCauchyDifferenceModulusDecodeBHist M)
                                                              (regularCauchyDifferenceModulusDecodeBHist E)
                                                              (regularCauchyDifferenceModulusDecodeBHist H)
                                                              (regularCauchyDifferenceModulusDecodeBHist C)
                                                              (regularCauchyDifferenceModulusDecodeBHist P)
                                                              (regularCauchyDifferenceModulusDecodeBHist N))
                                                      | _ :: _ => none

private theorem regularCauchyDifferenceModulus_round_trip :
    ∀ x : RegularCauchyDifferenceModulusUp,
      regularCauchyDifferenceModulusFromEventFlow
          (regularCauchyDifferenceModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y WX WY QX QY Delta M E H C P N =>
      rw [regularCauchyDifferenceModulusToEventFlow,
        regularCauchyDifferenceModulusFromEventFlow,
        regularCauchyDifferenceModulusDecode_encode X,
        regularCauchyDifferenceModulusDecode_encode Y,
        regularCauchyDifferenceModulusDecode_encode WX,
        regularCauchyDifferenceModulusDecode_encode WY,
        regularCauchyDifferenceModulusDecode_encode QX,
        regularCauchyDifferenceModulusDecode_encode QY,
        regularCauchyDifferenceModulusDecode_encode Delta,
        regularCauchyDifferenceModulusDecode_encode M,
        regularCauchyDifferenceModulusDecode_encode E,
        regularCauchyDifferenceModulusDecode_encode H,
        regularCauchyDifferenceModulusDecode_encode C,
        regularCauchyDifferenceModulusDecode_encode P,
        regularCauchyDifferenceModulusDecode_encode N]

private theorem regularCauchyDifferenceModulusToEventFlow_injective
    {x y : RegularCauchyDifferenceModulusUp} :
    regularCauchyDifferenceModulusToEventFlow x =
        regularCauchyDifferenceModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDifferenceModulusFromEventFlow
          (regularCauchyDifferenceModulusToEventFlow x) =
        regularCauchyDifferenceModulusFromEventFlow
          (regularCauchyDifferenceModulusToEventFlow y) :=
    congrArg regularCauchyDifferenceModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyDifferenceModulus_round_trip x).symm
      (Eq.trans hread (regularCauchyDifferenceModulus_round_trip y)))

instance regularCauchyDifferenceModulusBHistCarrier :
    BHistCarrier RegularCauchyDifferenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDifferenceModulusToEventFlow
  fromEventFlow := regularCauchyDifferenceModulusFromEventFlow

instance regularCauchyDifferenceModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyDifferenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDifferenceModulusFromEventFlow
          (regularCauchyDifferenceModulusToEventFlow x) =
        some x
    exact regularCauchyDifferenceModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDifferenceModulusToEventFlow_injective heq)

theorem RegularCauchyDifferenceModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyDifferenceModulusDecodeBHist
          (regularCauchyDifferenceModulusEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyDifferenceModulusUp,
        regularCauchyDifferenceModulusFromEventFlow
            (regularCauchyDifferenceModulusToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyDifferenceModulusUp,
        regularCauchyDifferenceModulusToEventFlow x =
            regularCauchyDifferenceModulusToEventFlow y →
          x = y) ∧
      regularCauchyDifferenceModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyDifferenceModulusDecode_encode,
      regularCauchyDifferenceModulus_round_trip,
      fun _ _ heq => regularCauchyDifferenceModulusToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.RegularCauchyDifferenceModulusUp
