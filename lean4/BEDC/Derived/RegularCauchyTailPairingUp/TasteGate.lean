import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailPairingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailPairingUp : Type where
  | mk (S0 S1 R0 R1 D0 D1 W U E H C P N : BHist) : RegularCauchyTailPairingUp
  deriving DecidableEq

def regularCauchyTailPairingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailPairingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailPairingEncodeBHist h

def regularCauchyTailPairingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailPairingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailPairingDecodeBHist tail)

private theorem regularCauchyTailPairingDecode_encode :
    ∀ h : BHist,
      regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailPairingFields : RegularCauchyTailPairingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailPairingUp.mk S0 S1 R0 R1 D0 D1 W U E H C P N =>
      [S0, S1, R0, R1, D0, D1, W, U, E, H, C, P, N]

def regularCauchyTailPairingToEventFlow : RegularCauchyTailPairingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyTailPairingFields x).map regularCauchyTailPairingEncodeBHist

private def regularCauchyTailPairingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailPairingEventAtDefault index rest

def regularCauchyTailPairingFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTailPairingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailPairingUp.mk
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 0 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 1 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 2 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 3 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 4 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 5 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 6 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 7 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 8 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 9 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 10 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 11 ef))
      (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEventAtDefault 12 ef)))

private theorem regularCauchyTailPairing_round_trip :
    ∀ x : RegularCauchyTailPairingUp,
      regularCauchyTailPairingFromEventFlow (regularCauchyTailPairingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 R0 R1 D0 D1 W U E H C P N =>
      change
        some
          (RegularCauchyTailPairingUp.mk
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist S0))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist S1))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist R0))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist R1))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist D0))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist D1))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist W))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist U))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist E))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist H))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist C))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist P))
            (regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist N))) =
          some (RegularCauchyTailPairingUp.mk S0 S1 R0 R1 D0 D1 W U E H C P N)
      rw [regularCauchyTailPairingDecode_encode S0, regularCauchyTailPairingDecode_encode S1,
        regularCauchyTailPairingDecode_encode R0, regularCauchyTailPairingDecode_encode R1,
        regularCauchyTailPairingDecode_encode D0, regularCauchyTailPairingDecode_encode D1,
        regularCauchyTailPairingDecode_encode W, regularCauchyTailPairingDecode_encode U,
        regularCauchyTailPairingDecode_encode E, regularCauchyTailPairingDecode_encode H,
        regularCauchyTailPairingDecode_encode C, regularCauchyTailPairingDecode_encode P,
        regularCauchyTailPairingDecode_encode N]

private theorem regularCauchyTailPairingToEventFlow_injective
    {x y : RegularCauchyTailPairingUp} :
    regularCauchyTailPairingToEventFlow x = regularCauchyTailPairingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailPairingFromEventFlow (regularCauchyTailPairingToEventFlow x) =
        regularCauchyTailPairingFromEventFlow (regularCauchyTailPairingToEventFlow y) :=
    congrArg regularCauchyTailPairingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTailPairing_round_trip x).symm
      (Eq.trans hread (regularCauchyTailPairing_round_trip y)))

instance regularCauchyTailPairingBHistCarrier :
    BHistCarrier RegularCauchyTailPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailPairingToEventFlow
  fromEventFlow := regularCauchyTailPairingFromEventFlow

instance regularCauchyTailPairingChapterTasteGate :
    ChapterTasteGate RegularCauchyTailPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailPairingFromEventFlow (regularCauchyTailPairingToEventFlow x) =
        some x
    exact regularCauchyTailPairing_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTailPairingToEventFlow_injective heq)

instance regularCauchyTailPairingNontrivial :
    Nontrivial RegularCauchyTailPairingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailPairingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyTailPairingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyTailPairingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailPairingDecodeBHist (regularCauchyTailPairingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyTailPairingUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyTailPairingUp) ∧
      regularCauchyTailPairingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨regularCauchyTailPairingDecode_encode,
      ⟨regularCauchyTailPairingBHistCarrier⟩,
      ⟨regularCauchyTailPairingChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyTailPairingUp
