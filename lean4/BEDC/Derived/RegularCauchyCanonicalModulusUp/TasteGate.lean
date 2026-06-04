import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCanonicalModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCanonicalModulusUp : Type where
  | mk (D S R Q E H C P N : BHist) : RegularCauchyCanonicalModulusUp
  deriving DecidableEq

def regularCauchyCanonicalModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCanonicalModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCanonicalModulusEncodeBHist h

def regularCauchyCanonicalModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCanonicalModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCanonicalModulusDecodeBHist tail)

private theorem regularCauchyCanonicalModulusDecode_encode :
    ∀ h : BHist,
      regularCauchyCanonicalModulusDecodeBHist
          (regularCauchyCanonicalModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCanonicalModulusFields :
    RegularCauchyCanonicalModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCanonicalModulusUp.mk D S R Q E H C P N => [D, S, R, Q, E, H, C, P, N]

def regularCauchyCanonicalModulusToEventFlow :
    RegularCauchyCanonicalModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyCanonicalModulusFields x).map
    regularCauchyCanonicalModulusEncodeBHist

private def regularCauchyCanonicalModulusEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyCanonicalModulusEventAtDefault index rest

def regularCauchyCanonicalModulusFromEventFlow
    (ef : EventFlow) : Option RegularCauchyCanonicalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyCanonicalModulusUp.mk
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 0 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 1 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 2 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 3 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 4 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 5 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 6 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 7 ef))
      (regularCauchyCanonicalModulusDecodeBHist
        (regularCauchyCanonicalModulusEventAtDefault 8 ef)))

private theorem regularCauchyCanonicalModulus_round_trip :
    ∀ x : RegularCauchyCanonicalModulusUp,
      regularCauchyCanonicalModulusFromEventFlow
          (regularCauchyCanonicalModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R Q E H C P N =>
      change
        some
            (RegularCauchyCanonicalModulusUp.mk
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist D))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist S))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist R))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist Q))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist E))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist H))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist C))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist P))
              (regularCauchyCanonicalModulusDecodeBHist
                (regularCauchyCanonicalModulusEncodeBHist N))) =
          some (RegularCauchyCanonicalModulusUp.mk D S R Q E H C P N)
      rw [regularCauchyCanonicalModulusDecode_encode D,
        regularCauchyCanonicalModulusDecode_encode S,
        regularCauchyCanonicalModulusDecode_encode R,
        regularCauchyCanonicalModulusDecode_encode Q,
        regularCauchyCanonicalModulusDecode_encode E,
        regularCauchyCanonicalModulusDecode_encode H,
        regularCauchyCanonicalModulusDecode_encode C,
        regularCauchyCanonicalModulusDecode_encode P,
        regularCauchyCanonicalModulusDecode_encode N]

private theorem regularCauchyCanonicalModulusToEventFlow_injective
    {x y : RegularCauchyCanonicalModulusUp} :
    regularCauchyCanonicalModulusToEventFlow x =
        regularCauchyCanonicalModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCanonicalModulusFromEventFlow
          (regularCauchyCanonicalModulusToEventFlow x) =
        regularCauchyCanonicalModulusFromEventFlow
          (regularCauchyCanonicalModulusToEventFlow y) :=
    congrArg regularCauchyCanonicalModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyCanonicalModulus_round_trip x).symm
      (Eq.trans hread (regularCauchyCanonicalModulus_round_trip y)))

private def regularCauchyCanonicalModulusBHistCarrierDef :
    BHistCarrier RegularCauchyCanonicalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCanonicalModulusToEventFlow
  fromEventFlow := regularCauchyCanonicalModulusFromEventFlow

instance regularCauchyCanonicalModulusBHistCarrier :
    BHistCarrier RegularCauchyCanonicalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCanonicalModulusBHistCarrierDef

private def regularCauchyCanonicalModulusChapterTasteGateDef :
    ChapterTasteGate RegularCauchyCanonicalModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCanonicalModulusFromEventFlow
          (regularCauchyCanonicalModulusToEventFlow x) =
        some x
    exact regularCauchyCanonicalModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCanonicalModulusToEventFlow_injective heq)

instance regularCauchyCanonicalModulusChapterTasteGate :
    ChapterTasteGate RegularCauchyCanonicalModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCanonicalModulusChapterTasteGateDef

theorem RegularCauchyCanonicalModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCanonicalModulusDecodeBHist
          (regularCauchyCanonicalModulusEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyCanonicalModulusUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyCanonicalModulusUp) ∧
          regularCauchyCanonicalModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyCanonicalModulusDecode_encode
  · constructor
    · exact ⟨regularCauchyCanonicalModulusBHistCarrierDef⟩
    · constructor
      · exact ⟨regularCauchyCanonicalModulusChapterTasteGateDef⟩
      · rfl

end BEDC.Derived.RegularCauchyCanonicalModulusUp
