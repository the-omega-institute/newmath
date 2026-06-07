import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyComparisonModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyComparisonModulusUp : Type where
  | mk (S0 S1 R0 R1 D mu W Q E H C P N : BHist) :
      RegularCauchyComparisonModulusUp
  deriving DecidableEq

def regularCauchyComparisonModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyComparisonModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyComparisonModulusEncodeBHist h

def regularCauchyComparisonModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyComparisonModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyComparisonModulusDecodeBHist tail)

private theorem regularCauchyComparisonModulusDecode_encode :
    ∀ h : BHist,
      regularCauchyComparisonModulusDecodeBHist
          (regularCauchyComparisonModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyComparisonModulusToEventFlow :
    RegularCauchyComparisonModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyComparisonModulusUp.mk S0 S1 R0 R1 D mu W Q E H C P N =>
      [regularCauchyComparisonModulusEncodeBHist S0,
        regularCauchyComparisonModulusEncodeBHist S1,
        regularCauchyComparisonModulusEncodeBHist R0,
        regularCauchyComparisonModulusEncodeBHist R1,
        regularCauchyComparisonModulusEncodeBHist D,
        regularCauchyComparisonModulusEncodeBHist mu,
        regularCauchyComparisonModulusEncodeBHist W,
        regularCauchyComparisonModulusEncodeBHist Q,
        regularCauchyComparisonModulusEncodeBHist E,
        regularCauchyComparisonModulusEncodeBHist H,
        regularCauchyComparisonModulusEncodeBHist C,
        regularCauchyComparisonModulusEncodeBHist P,
        regularCauchyComparisonModulusEncodeBHist N]

def regularCauchyComparisonModulusFromEventFlow :
    EventFlow → Option RegularCauchyComparisonModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S0, S1, R0, R1, D, mu, W, Q, E, H, C, P, N] =>
      some
        (RegularCauchyComparisonModulusUp.mk
          (regularCauchyComparisonModulusDecodeBHist S0)
          (regularCauchyComparisonModulusDecodeBHist S1)
          (regularCauchyComparisonModulusDecodeBHist R0)
          (regularCauchyComparisonModulusDecodeBHist R1)
          (regularCauchyComparisonModulusDecodeBHist D)
          (regularCauchyComparisonModulusDecodeBHist mu)
          (regularCauchyComparisonModulusDecodeBHist W)
          (regularCauchyComparisonModulusDecodeBHist Q)
          (regularCauchyComparisonModulusDecodeBHist E)
          (regularCauchyComparisonModulusDecodeBHist H)
          (regularCauchyComparisonModulusDecodeBHist C)
          (regularCauchyComparisonModulusDecodeBHist P)
          (regularCauchyComparisonModulusDecodeBHist N))
  | _ => none

private theorem regularCauchyComparisonModulus_round_trip :
    ∀ x : RegularCauchyComparisonModulusUp,
      regularCauchyComparisonModulusFromEventFlow
          (regularCauchyComparisonModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 R0 R1 D mu W Q E H C P N =>
      change
        some
            (RegularCauchyComparisonModulusUp.mk
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist S0))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist S1))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist R0))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist R1))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist D))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist mu))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist W))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist Q))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist E))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist H))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist C))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist P))
              (regularCauchyComparisonModulusDecodeBHist
                (regularCauchyComparisonModulusEncodeBHist N))) =
          some (RegularCauchyComparisonModulusUp.mk S0 S1 R0 R1 D mu W Q E H C P N)
      rw [regularCauchyComparisonModulusDecode_encode S0,
        regularCauchyComparisonModulusDecode_encode S1,
        regularCauchyComparisonModulusDecode_encode R0,
        regularCauchyComparisonModulusDecode_encode R1,
        regularCauchyComparisonModulusDecode_encode D,
        regularCauchyComparisonModulusDecode_encode mu,
        regularCauchyComparisonModulusDecode_encode W,
        regularCauchyComparisonModulusDecode_encode Q,
        regularCauchyComparisonModulusDecode_encode E,
        regularCauchyComparisonModulusDecode_encode H,
        regularCauchyComparisonModulusDecode_encode C,
        regularCauchyComparisonModulusDecode_encode P,
        regularCauchyComparisonModulusDecode_encode N]

private theorem regularCauchyComparisonModulusToEventFlow_injective
    {x y : RegularCauchyComparisonModulusUp} :
    regularCauchyComparisonModulusToEventFlow x =
        regularCauchyComparisonModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyComparisonModulusFromEventFlow
          (regularCauchyComparisonModulusToEventFlow x) =
        regularCauchyComparisonModulusFromEventFlow
          (regularCauchyComparisonModulusToEventFlow y) :=
    congrArg regularCauchyComparisonModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyComparisonModulus_round_trip x).symm
      (Eq.trans hread (regularCauchyComparisonModulus_round_trip y)))

private def regularCauchyComparisonModulusBHistCarrierDef :
    BHistCarrier RegularCauchyComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyComparisonModulusToEventFlow
  fromEventFlow := regularCauchyComparisonModulusFromEventFlow

instance regularCauchyComparisonModulusBHistCarrier :
    BHistCarrier RegularCauchyComparisonModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyComparisonModulusBHistCarrierDef

private def regularCauchyComparisonModulusChapterTasteGateDef :
    ChapterTasteGate RegularCauchyComparisonModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyComparisonModulusFromEventFlow
          (regularCauchyComparisonModulusToEventFlow x) =
        some x
    exact regularCauchyComparisonModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyComparisonModulusToEventFlow_injective heq)

instance regularCauchyComparisonModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyComparisonModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyComparisonModulusChapterTasteGateDef

theorem RegularCauchyComparisonModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyComparisonModulusDecodeBHist
          (regularCauchyComparisonModulusEncodeBHist h) =
        h) ∧
      regularCauchyComparisonModulusDecodeBHist
          (regularCauchyComparisonModulusEncodeBHist BHist.Empty) =
        BHist.Empty ∧
        regularCauchyComparisonModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · rfl
    · rfl

end BEDC.Derived.RegularCauchyComparisonModulusUp
