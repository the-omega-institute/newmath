import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SAdicSolenoidChargeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SAdicSolenoidChargeUp : Type where
  | mk
      (primeWindow primeRows localizationLedger denominatorCharge solenoidPhase visibleCircle
        compactFibre transport replay localName : BHist) :
      SAdicSolenoidChargeUp

def sAdicSolenoidChargeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sAdicSolenoidChargeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sAdicSolenoidChargeEncodeBHist h

def sAdicSolenoidChargeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sAdicSolenoidChargeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sAdicSolenoidChargeDecodeBHist tail)

private theorem SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sAdicSolenoidChargeFields : SAdicSolenoidChargeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SAdicSolenoidChargeUp.mk primeWindow primeRows localizationLedger denominatorCharge
      solenoidPhase visibleCircle compactFibre transport replay localName =>
      [primeWindow, primeRows, localizationLedger, denominatorCharge, solenoidPhase,
        visibleCircle, compactFibre, transport, replay, localName]

def sAdicSolenoidChargeToEventFlow : SAdicSolenoidChargeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sAdicSolenoidChargeFields x).map sAdicSolenoidChargeEncodeBHist

private def sAdicSolenoidChargeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sAdicSolenoidChargeEventAtDefault index rest

def sAdicSolenoidChargeFromEventFlow (ef : EventFlow) : Option SAdicSolenoidChargeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SAdicSolenoidChargeUp.mk
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 0 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 1 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 2 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 3 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 4 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 5 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 6 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 7 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 8 ef))
      (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEventAtDefault 9 ef)))

private theorem SAdicSolenoidChargeTasteGate_single_carrier_alignment_round_trip
    (x : SAdicSolenoidChargeUp) :
    sAdicSolenoidChargeFromEventFlow (sAdicSolenoidChargeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk primeWindow primeRows localizationLedger denominatorCharge solenoidPhase visibleCircle
      compactFibre transport replay localName =>
      change
        some
          (SAdicSolenoidChargeUp.mk
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist primeWindow))
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist primeRows))
            (sAdicSolenoidChargeDecodeBHist
              (sAdicSolenoidChargeEncodeBHist localizationLedger))
            (sAdicSolenoidChargeDecodeBHist
              (sAdicSolenoidChargeEncodeBHist denominatorCharge))
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist solenoidPhase))
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist visibleCircle))
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist compactFibre))
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist transport))
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist replay))
            (sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist localName))) =
          some
            (SAdicSolenoidChargeUp.mk primeWindow primeRows localizationLedger
              denominatorCharge solenoidPhase visibleCircle compactFibre transport replay
              localName)
      rw [SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode primeWindow,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode primeRows,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode localizationLedger,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode denominatorCharge,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode solenoidPhase,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode visibleCircle,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode compactFibre,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode transport,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode replay,
        SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode localName]

private theorem SAdicSolenoidChargeTasteGate_single_carrier_alignment_injective
    {x y : SAdicSolenoidChargeUp} :
    sAdicSolenoidChargeToEventFlow x = sAdicSolenoidChargeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sAdicSolenoidChargeFromEventFlow (sAdicSolenoidChargeToEventFlow x) =
        sAdicSolenoidChargeFromEventFlow (sAdicSolenoidChargeToEventFlow y) :=
    congrArg sAdicSolenoidChargeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SAdicSolenoidChargeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SAdicSolenoidChargeTasteGate_single_carrier_alignment_round_trip y)))

instance sAdicSolenoidChargeBHistCarrier : BHistCarrier SAdicSolenoidChargeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sAdicSolenoidChargeToEventFlow
  fromEventFlow := sAdicSolenoidChargeFromEventFlow

instance sAdicSolenoidChargeChapterTasteGate :
    ChapterTasteGate SAdicSolenoidChargeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sAdicSolenoidChargeFromEventFlow (sAdicSolenoidChargeToEventFlow x) = some x
    exact SAdicSolenoidChargeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SAdicSolenoidChargeTasteGate_single_carrier_alignment_injective heq)

def SAdicSolenoidChargeTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate SAdicSolenoidChargeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sAdicSolenoidChargeChapterTasteGate

theorem SAdicSolenoidChargeTasteGate_single_carrier_alignment :
    (∀ h : BHist, sAdicSolenoidChargeDecodeBHist (sAdicSolenoidChargeEncodeBHist h) = h) ∧
      (∀ x : SAdicSolenoidChargeUp,
        sAdicSolenoidChargeFromEventFlow (sAdicSolenoidChargeToEventFlow x) = some x) ∧
        (∀ x y : SAdicSolenoidChargeUp,
          sAdicSolenoidChargeToEventFlow x = sAdicSolenoidChargeToEventFlow y →
            x = y) ∧
          Nonempty (BHistCarrier SAdicSolenoidChargeUp) ∧
            Nonempty (ChapterTasteGate SAdicSolenoidChargeUp) ∧
              sAdicSolenoidChargeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SAdicSolenoidChargeTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact SAdicSolenoidChargeTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact SAdicSolenoidChargeTasteGate_single_carrier_alignment_injective heq
      · constructor
        · exact ⟨sAdicSolenoidChargeBHistCarrier⟩
        · constructor
          · exact ⟨sAdicSolenoidChargeChapterTasteGate⟩
          · rfl

end BEDC.Derived.SAdicSolenoidChargeUp
