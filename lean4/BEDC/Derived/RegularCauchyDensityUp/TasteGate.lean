import BEDC.Derived.RegularCauchyDensityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDensityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def regularCauchyDensityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDensityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDensityEncodeBHist h

def regularCauchyDensityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDensityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDensityDecodeBHist tail)

private theorem RegularCauchyDensityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def regularCauchyDensityToEventFlow :
    BEDC.Derived.RegularCauchyDensityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BEDC.Derived.RegularCauchyDensityUp.mk Q S R A E H C P N =>
      [regularCauchyDensityEncodeBHist Q, regularCauchyDensityEncodeBHist S,
        regularCauchyDensityEncodeBHist R, regularCauchyDensityEncodeBHist A,
        regularCauchyDensityEncodeBHist E, regularCauchyDensityEncodeBHist H,
        regularCauchyDensityEncodeBHist C, regularCauchyDensityEncodeBHist P,
        regularCauchyDensityEncodeBHist N]

private def regularCauchyDensityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyDensityEventAtDefault index rest

def regularCauchyDensityFromEventFlow
    (ef : EventFlow) : Option BEDC.Derived.RegularCauchyDensityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BEDC.Derived.RegularCauchyDensityUp.mk
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 0 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 1 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 2 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 3 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 4 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 5 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 6 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 7 ef))
      (regularCauchyDensityDecodeBHist (regularCauchyDensityEventAtDefault 8 ef)))

private theorem RegularCauchyDensityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BEDC.Derived.RegularCauchyDensityUp,
      regularCauchyDensityFromEventFlow (regularCauchyDensityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S R A E H C P N =>
      change
        some
          (BEDC.Derived.RegularCauchyDensityUp.mk
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist Q))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist S))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist R))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist A))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist E))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist H))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist C))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist P))
            (regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist N))) =
          some (BEDC.Derived.RegularCauchyDensityUp.mk Q S R A E H C P N)
      rw [RegularCauchyDensityTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode S,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode R,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode A,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode E,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode H,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode C,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode P,
        RegularCauchyDensityTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyDensityTasteGate_single_carrier_alignment_injective
    {x y : BEDC.Derived.RegularCauchyDensityUp} :
    regularCauchyDensityToEventFlow x = regularCauchyDensityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyDensityFromEventFlow (regularCauchyDensityToEventFlow x) =
        regularCauchyDensityFromEventFlow (regularCauchyDensityToEventFlow y) :=
    congrArg regularCauchyDensityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RegularCauchyDensityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyDensityTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyDensityBHistCarrier :
    BHistCarrier BEDC.Derived.RegularCauchyDensityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDensityToEventFlow
  fromEventFlow := regularCauchyDensityFromEventFlow

instance regularCauchyDensityChapterTasteGate :
    ChapterTasteGate BEDC.Derived.RegularCauchyDensityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyDensityFromEventFlow (regularCauchyDensityToEventFlow x) = some x
    exact RegularCauchyDensityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyDensityTasteGate_single_carrier_alignment_injective heq)

theorem RegularCauchyDensityTasteGate_single_carrier_alignment :
    (∀ Q S R A E H C P N : BHist,
      BEDC.Derived.RegularCauchyDensityUp.fields
          (BEDC.Derived.RegularCauchyDensityUp.mk Q S R A E H C P N) =
        [Q, S, R, A, E, H, C, P, N]) ∧
      (∀ h : BHist,
        regularCauchyDensityDecodeBHist (regularCauchyDensityEncodeBHist h) = h) ∧
        regularCauchyDensityEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: RegularCauchyDensityUp BHist BMark ChapterTasteGate
  exact
    ⟨(by
        intro Q S R A E H C P N
        rfl),
      RegularCauchyDensityTasteGate_single_carrier_alignment_decode,
      rfl⟩

end BEDC.Derived.RegularCauchyDensityUp
