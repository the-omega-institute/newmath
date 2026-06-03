import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusCompressionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusCompressionUp : Type where
  | mk (S Q D R E H C P N : BHist) : RegularCauchyModulusCompressionUp
  deriving DecidableEq

def regularCauchyModulusCompressionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusCompressionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusCompressionEncodeBHist h

def regularCauchyModulusCompressionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusCompressionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusCompressionDecodeBHist tail)

private theorem RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyModulusCompressionFields :
    RegularCauchyModulusCompressionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusCompressionUp.mk S Q D R E H C P N => [S, Q, D, R, E, H, C, P, N]

def regularCauchyModulusCompressionToEventFlow :
    RegularCauchyModulusCompressionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (regularCauchyModulusCompressionFields x).map
    regularCauchyModulusCompressionEncodeBHist

private def regularCauchyModulusCompressionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyModulusCompressionEventAtDefault index rest

def regularCauchyModulusCompressionFromEventFlow (ef : EventFlow) :
    Option RegularCauchyModulusCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyModulusCompressionUp.mk
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 0 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 1 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 2 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 3 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 4 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 5 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 6 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 7 ef))
      (regularCauchyModulusCompressionDecodeBHist
        (regularCauchyModulusCompressionEventAtDefault 8 ef)))

private theorem RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyModulusCompressionUp,
      regularCauchyModulusCompressionFromEventFlow
        (regularCauchyModulusCompressionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D R E H C P N =>
      change
        some
          (RegularCauchyModulusCompressionUp.mk
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist S))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist Q))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist D))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist R))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist E))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist H))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist C))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist P))
            (regularCauchyModulusCompressionDecodeBHist
              (regularCauchyModulusCompressionEncodeBHist N))) =
          some (RegularCauchyModulusCompressionUp.mk S Q D R E H C P N)
      rw [RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode S,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode D,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode R,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode E,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode H,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode C,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode P,
        RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_injective
    {x y : RegularCauchyModulusCompressionUp} :
    regularCauchyModulusCompressionToEventFlow x =
      regularCauchyModulusCompressionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyModulusCompressionFromEventFlow
          (regularCauchyModulusCompressionToEventFlow x) =
        regularCauchyModulusCompressionFromEventFlow
          (regularCauchyModulusCompressionToEventFlow y) :=
    congrArg regularCauchyModulusCompressionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyModulusCompressionBHistCarrier :
    BHistCarrier RegularCauchyModulusCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusCompressionToEventFlow
  fromEventFlow := regularCauchyModulusCompressionFromEventFlow

instance regularCauchyModulusCompressionChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusCompressionFromEventFlow
          (regularCauchyModulusCompressionToEventFlow x) = some x
    exact RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_injective heq)

theorem RegularCauchyModulusCompressionTasteGate_single_carrier_alignment :
    (forall h : BHist, regularCauchyModulusCompressionDecodeBHist
      (regularCauchyModulusCompressionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyModulusCompressionUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyModulusCompressionUp) ∧
          regularCauchyModulusCompressionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyModulusCompressionTasteGate_single_carrier_alignment_decode,
      ⟨⟨regularCauchyModulusCompressionBHistCarrier⟩,
        ⟨regularCauchyModulusCompressionChapterTasteGate⟩,
        rfl⟩⟩

end BEDC.Derived.RegularCauchyModulusCompressionUp
