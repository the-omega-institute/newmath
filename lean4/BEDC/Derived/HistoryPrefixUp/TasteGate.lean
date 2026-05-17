import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HistoryPrefixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HistoryPrefixUp : Type where
  | mk
      (source prefixRow residualTail continuation compatibility evidence ledger name : BHist) :
      HistoryPrefixUp
  deriving DecidableEq

def historyPrefixEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: historyPrefixEncodeBHist h
  | BHist.e1 h => BMark.b1 :: historyPrefixEncodeBHist h

def historyPrefixDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (historyPrefixDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (historyPrefixDecodeBHist tail)

theorem HistoryPrefixTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, historyPrefixDecodeBHist (historyPrefixEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def historyPrefixFields : HistoryPrefixUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HistoryPrefixUp.mk source prefixRow residualTail continuation compatibility evidence ledger
      name =>
      [source, prefixRow, residualTail, continuation, compatibility, evidence, ledger, name]

def historyPrefixToEventFlow : HistoryPrefixUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (historyPrefixFields x).map historyPrefixEncodeBHist

private def historyPrefixEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => historyPrefixEventAtDefault index rest

def historyPrefixFromEventFlow (ef : EventFlow) : Option HistoryPrefixUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HistoryPrefixUp.mk
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 0 ef))
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 1 ef))
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 2 ef))
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 3 ef))
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 4 ef))
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 5 ef))
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 6 ef))
      (historyPrefixDecodeBHist (historyPrefixEventAtDefault 7 ef)))

private theorem HistoryPrefixTasteGate_single_carrier_alignment_mk_congr
    {source source' prefixRow prefixRow' residualTail residualTail' continuation continuation'
      compatibility compatibility' evidence evidence' ledger ledger' name name' : BHist}
    (hSource : source' = source)
    (hPrefix : prefixRow' = prefixRow)
    (hResidualTail : residualTail' = residualTail)
    (hContinuation : continuation' = continuation)
    (hCompatibility : compatibility' = compatibility)
    (hEvidence : evidence' = evidence)
    (hLedger : ledger' = ledger)
    (hName : name' = name) :
    HistoryPrefixUp.mk source' prefixRow' residualTail' continuation' compatibility'
        evidence' ledger' name' =
      HistoryPrefixUp.mk source prefixRow residualTail continuation compatibility evidence ledger
        name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hPrefix
  cases hResidualTail
  cases hContinuation
  cases hCompatibility
  cases hEvidence
  cases hLedger
  cases hName
  rfl

theorem HistoryPrefixTasteGate_single_carrier_alignment_round_trip :
    ∀ x : HistoryPrefixUp, historyPrefixFromEventFlow (historyPrefixToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source prefixRow residualTail continuation compatibility evidence ledger name =>
      change
        some
          (HistoryPrefixUp.mk
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist source))
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist prefixRow))
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist residualTail))
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist continuation))
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist compatibility))
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist evidence))
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist ledger))
            (historyPrefixDecodeBHist (historyPrefixEncodeBHist name))) =
          some
            (HistoryPrefixUp.mk source prefixRow residualTail continuation compatibility evidence
              ledger name)
      exact
        congrArg some
          (HistoryPrefixTasteGate_single_carrier_alignment_mk_congr
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode source)
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode prefixRow)
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode residualTail)
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode continuation)
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode compatibility)
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode evidence)
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode ledger)
            (HistoryPrefixTasteGate_single_carrier_alignment_decode_encode name))

theorem HistoryPrefixTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HistoryPrefixUp} :
    historyPrefixToEventFlow x = historyPrefixToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      historyPrefixFromEventFlow (historyPrefixToEventFlow x) =
        historyPrefixFromEventFlow (historyPrefixToEventFlow y) :=
    congrArg historyPrefixFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HistoryPrefixTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HistoryPrefixTasteGate_single_carrier_alignment_round_trip y)))

theorem HistoryPrefixTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : HistoryPrefixUp, historyPrefixFields x = historyPrefixFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ prefixRow₁ residualTail₁ continuation₁ compatibility₁ evidence₁ ledger₁ name₁ =>
      cases y with
      | mk source₂ prefixRow₂ residualTail₂ continuation₂ compatibility₂ evidence₂ ledger₂ name₂ =>
          cases hfields
          rfl

instance historyPrefixBHistCarrier : BHistCarrier HistoryPrefixUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := historyPrefixToEventFlow
  fromEventFlow := historyPrefixFromEventFlow

instance historyPrefixChapterTasteGate : ChapterTasteGate HistoryPrefixUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change historyPrefixFromEventFlow (historyPrefixToEventFlow x) = some x
    exact HistoryPrefixTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HistoryPrefixTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance historyPrefixFieldFaithful : FieldFaithful HistoryPrefixUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := historyPrefixFields
  field_faithful := HistoryPrefixTasteGate_single_carrier_alignment_fields_faithful

instance historyPrefixNontrivial : Nontrivial HistoryPrefixUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HistoryPrefixUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      HistoryPrefixUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HistoryPrefixTasteGate_single_carrier_alignment :
    (forall h : BHist, historyPrefixDecodeBHist (historyPrefixEncodeBHist h) = h) ∧
      (forall x : HistoryPrefixUp, historyPrefixFromEventFlow (historyPrefixToEventFlow x) =
        some x) ∧
        (forall x y : HistoryPrefixUp, historyPrefixToEventFlow x = historyPrefixToEventFlow y ->
          x = y) ∧ historyPrefixEncodeBHist BHist.Empty = ([] : List BMark) ∧
          (forall x y : HistoryPrefixUp, historyPrefixFields x = historyPrefixFields y ->
            x = y) ∧ (exists x y : HistoryPrefixUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact HistoryPrefixTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact HistoryPrefixTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact HistoryPrefixTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact HistoryPrefixTasteGate_single_carrier_alignment_fields_faithful
          · exact
              ⟨HistoryPrefixUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                HistoryPrefixUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.HistoryPrefixUp
