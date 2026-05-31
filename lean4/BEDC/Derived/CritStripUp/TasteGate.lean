import BEDC.Derived.CritStripUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CritStripUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CritStripUp : Type where
  | mk (stripCoordinate boundaryClassifier ledgerWitness nameRow : BHist) : CritStripUp
  deriving DecidableEq

def critStripEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: critStripEncodeBHist h
  | BHist.e1 h => BMark.b1 :: critStripEncodeBHist h

def critStripDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (critStripDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (critStripDecodeBHist tail)

private theorem CritStripTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, critStripDecodeBHist (critStripEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem CritStripTasteGate_single_carrier_alignment_mk_congr
    {strip strip' classifier classifier' ledger ledger' name name' : BHist}
    (hStrip : strip' = strip) (hClassifier : classifier' = classifier)
    (hLedger : ledger' = ledger) (hName : name' = name) :
    CritStripUp.mk strip' classifier' ledger' name' =
      CritStripUp.mk strip classifier ledger name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hStrip
  cases hClassifier
  cases hLedger
  cases hName
  rfl

def critStripFields : CritStripUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CritStripUp.mk strip classifier ledger name => [strip, classifier, ledger, name]

def critStripToEventFlow : CritStripUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (critStripFields x).map critStripEncodeBHist

private def critStripRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => critStripRawAt n rest

private def critStripLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => critStripLengthEq n rest

def critStripFromEventFlow : EventFlow → Option CritStripUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match critStripLengthEq 4 flow with
      | true =>
          some
            (CritStripUp.mk
              (critStripDecodeBHist (critStripRawAt 0 flow))
              (critStripDecodeBHist (critStripRawAt 1 flow))
              (critStripDecodeBHist (critStripRawAt 2 flow))
              (critStripDecodeBHist (critStripRawAt 3 flow)))
      | false => none

private theorem critStrip_round_trip :
    ∀ x : CritStripUp, critStripFromEventFlow (critStripToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk strip classifier ledger name =>
      exact
        congrArg some
          (CritStripTasteGate_single_carrier_alignment_mk_congr
            (CritStripTasteGate_single_carrier_alignment_decode_encode strip)
            (CritStripTasteGate_single_carrier_alignment_decode_encode classifier)
            (CritStripTasteGate_single_carrier_alignment_decode_encode ledger)
            (CritStripTasteGate_single_carrier_alignment_decode_encode name))

private theorem critStripToEventFlow_injective {x y : CritStripUp} :
    critStripToEventFlow x = critStripToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      critStripFromEventFlow (critStripToEventFlow x) =
        critStripFromEventFlow (critStripToEventFlow y) :=
    congrArg critStripFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (critStrip_round_trip x).symm
      (Eq.trans hread (critStrip_round_trip y)))

instance critStripBHistCarrier : BHistCarrier CritStripUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := critStripToEventFlow
  fromEventFlow := critStripFromEventFlow

instance critStripChapterTasteGate : ChapterTasteGate CritStripUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change critStripFromEventFlow (critStripToEventFlow x) = some x
    exact critStrip_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (critStripToEventFlow_injective heq)

theorem CritStripTasteGate_single_carrier_alignment :
    (∀ h : BHist, critStripDecodeBHist (critStripEncodeBHist h) = h) ∧
      (∀ x : CritStripUp, critStripFromEventFlow (critStripToEventFlow x) = some x) ∧
        (∀ x y : CritStripUp, critStripToEventFlow x = critStripToEventFlow y -> x = y) ∧
          critStripEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CritStripTasteGate_single_carrier_alignment_decode_encode,
      critStrip_round_trip,
      (fun _ _ heq => critStripToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CritStripUp
