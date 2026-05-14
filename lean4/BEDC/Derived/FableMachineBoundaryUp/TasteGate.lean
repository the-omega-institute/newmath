import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FableMachineBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FableMachineBoundaryUp : Type where
  | mk :
      (history emptyBoundary ledger selector witness clock transport continuation provenance
        nameCert : BHist) →
      FableMachineBoundaryUp
  deriving DecidableEq

def fableMachineBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fableMachineBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fableMachineBoundaryEncodeBHist h

def fableMachineBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fableMachineBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fableMachineBoundaryDecodeBHist tail)

private theorem fableMachineBoundaryDecodeEncodeBHist :
    ∀ h : BHist,
      fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def fableMachineBoundaryFields : FableMachineBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FableMachineBoundaryUp.mk history emptyBoundary ledger selector witness clock transport
      continuation provenance nameCert =>
      [history, emptyBoundary, ledger, selector, witness, clock, transport, continuation,
        provenance, nameCert]

def fableMachineBoundaryToEventFlow : FableMachineBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (fableMachineBoundaryFields x).map fableMachineBoundaryEncodeBHist

def fableMachineBoundaryFromEventFlow : EventFlow → Option FableMachineBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | history :: rest0 =>
      match rest0 with
      | [] => none
      | emptyBoundary :: rest1 =>
          match rest1 with
          | [] => none
          | ledger :: rest2 =>
              match rest2 with
              | [] => none
              | selector :: rest3 =>
                  match rest3 with
                  | [] => none
                  | witness :: rest4 =>
                      match rest4 with
                      | [] => none
                      | clock :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FableMachineBoundaryUp.mk
                                                  (fableMachineBoundaryDecodeBHist history)
                                                  (fableMachineBoundaryDecodeBHist
                                                    emptyBoundary)
                                                  (fableMachineBoundaryDecodeBHist ledger)
                                                  (fableMachineBoundaryDecodeBHist selector)
                                                  (fableMachineBoundaryDecodeBHist witness)
                                                  (fableMachineBoundaryDecodeBHist clock)
                                                  (fableMachineBoundaryDecodeBHist transport)
                                                  (fableMachineBoundaryDecodeBHist
                                                    continuation)
                                                  (fableMachineBoundaryDecodeBHist
                                                    provenance)
                                                  (fableMachineBoundaryDecodeBHist nameCert))
                                          | _ :: _ => none

private theorem fableMachineBoundary_round_trip :
    ∀ x : FableMachineBoundaryUp,
      fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk history emptyBoundary ledger selector witness clock transport continuation provenance
      nameCert =>
      change
        some
          (FableMachineBoundaryUp.mk
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist history))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist emptyBoundary))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist ledger))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist selector))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist witness))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist clock))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist transport))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist continuation))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist provenance))
            (fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist nameCert))) =
          some
            (FableMachineBoundaryUp.mk history emptyBoundary ledger selector witness clock
              transport continuation provenance nameCert)
      rw [fableMachineBoundaryDecodeEncodeBHist history,
        fableMachineBoundaryDecodeEncodeBHist emptyBoundary,
        fableMachineBoundaryDecodeEncodeBHist ledger,
        fableMachineBoundaryDecodeEncodeBHist selector,
        fableMachineBoundaryDecodeEncodeBHist witness,
        fableMachineBoundaryDecodeEncodeBHist clock,
        fableMachineBoundaryDecodeEncodeBHist transport,
        fableMachineBoundaryDecodeEncodeBHist continuation,
        fableMachineBoundaryDecodeEncodeBHist provenance,
        fableMachineBoundaryDecodeEncodeBHist nameCert]

private theorem fableMachineBoundaryToEventFlow_injective {x y : FableMachineBoundaryUp} :
    fableMachineBoundaryToEventFlow x = fableMachineBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk history₁ emptyBoundary₁ ledger₁ selector₁ witness₁ clock₁ transport₁ continuation₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk history₂ emptyBoundary₂ ledger₂ selector₂ witness₂ clock₂ transport₂ continuation₂
          provenance₂ nameCert₂ =>
          intro heq
          injection heq with hhistoryRaw tail0
          injection tail0 with hemptyBoundaryRaw tail1
          injection tail1 with hledgerRaw tail2
          injection tail2 with hselectorRaw tail3
          injection tail3 with hwitnessRaw tail4
          injection tail4 with hclockRaw tail5
          injection tail5 with htransportRaw tail6
          injection tail6 with hcontinuationRaw tail7
          injection tail7 with hprovenanceRaw tail8
          injection tail8 with hnameCertRaw _
          have hhistory : history₁ = history₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist history₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hhistoryRaw)
                (fableMachineBoundaryDecodeEncodeBHist history₂))
          have hemptyBoundary : emptyBoundary₁ = emptyBoundary₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist emptyBoundary₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hemptyBoundaryRaw)
                (fableMachineBoundaryDecodeEncodeBHist emptyBoundary₂))
          have hledger : ledger₁ = ledger₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist ledger₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hledgerRaw)
                (fableMachineBoundaryDecodeEncodeBHist ledger₂))
          have hselector : selector₁ = selector₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist selector₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hselectorRaw)
                (fableMachineBoundaryDecodeEncodeBHist selector₂))
          have hwitness : witness₁ = witness₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist witness₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hwitnessRaw)
                (fableMachineBoundaryDecodeEncodeBHist witness₂))
          have hclock : clock₁ = clock₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist clock₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hclockRaw)
                (fableMachineBoundaryDecodeEncodeBHist clock₂))
          have htransport : transport₁ = transport₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist transport₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist htransportRaw)
                (fableMachineBoundaryDecodeEncodeBHist transport₂))
          have hcontinuation : continuation₁ = continuation₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist continuation₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hcontinuationRaw)
                (fableMachineBoundaryDecodeEncodeBHist continuation₂))
          have hprovenance : provenance₁ = provenance₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist provenance₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hprovenanceRaw)
                (fableMachineBoundaryDecodeEncodeBHist provenance₂))
          have hnameCert : nameCert₁ = nameCert₂ :=
            Eq.trans (fableMachineBoundaryDecodeEncodeBHist nameCert₁).symm
              (Eq.trans (congrArg fableMachineBoundaryDecodeBHist hnameCertRaw)
                (fableMachineBoundaryDecodeEncodeBHist nameCert₂))
          cases hhistory
          cases hemptyBoundary
          cases hledger
          cases hselector
          cases hwitness
          cases hclock
          cases htransport
          cases hcontinuation
          cases hprovenance
          cases hnameCert
          rfl

private theorem fableMachineBoundary_fields_faithful :
    ∀ x y : FableMachineBoundaryUp,
      fableMachineBoundaryFields x = fableMachineBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk history₁ emptyBoundary₁ ledger₁ selector₁ witness₁ clock₁ transport₁ continuation₁
      provenance₁ nameCert₁ =>
      cases y with
      | mk history₂ emptyBoundary₂ ledger₂ selector₂ witness₂ clock₂ transport₂ continuation₂
          provenance₂ nameCert₂ =>
          injection hfields with hhistory tail0
          injection tail0 with hemptyBoundary tail1
          injection tail1 with hledger tail2
          injection tail2 with hselector tail3
          injection tail3 with hwitness tail4
          injection tail4 with hclock tail5
          injection tail5 with htransport tail6
          injection tail6 with hcontinuation tail7
          injection tail7 with hprovenance tail8
          injection tail8 with hnameCert _
          subst hhistory
          subst hemptyBoundary
          subst hledger
          subst hselector
          subst hwitness
          subst hclock
          subst htransport
          subst hcontinuation
          subst hprovenance
          subst hnameCert
          rfl

instance fableMachineBoundaryBHistCarrier : BHistCarrier FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fableMachineBoundaryToEventFlow
  fromEventFlow := fableMachineBoundaryFromEventFlow

instance fableMachineBoundaryChapterTasteGate : ChapterTasteGate FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) = some x
    exact fableMachineBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fableMachineBoundaryToEventFlow_injective heq)

def taste_gate : ChapterTasteGate FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) = some x
    exact fableMachineBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fableMachineBoundaryToEventFlow_injective heq)

instance fableMachineBoundaryFieldFaithful : FieldFaithful FableMachineBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fableMachineBoundaryFields
  field_faithful := fableMachineBoundary_fields_faithful

theorem FableMachineBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, fableMachineBoundaryDecodeBHist (fableMachineBoundaryEncodeBHist h) = h) ∧
      (∀ x : FableMachineBoundaryUp,
        fableMachineBoundaryFromEventFlow (fableMachineBoundaryToEventFlow x) = some x) ∧
        (∀ x y : FableMachineBoundaryUp,
          fableMachineBoundaryToEventFlow x = fableMachineBoundaryToEventFlow y → x = y) ∧
          fableMachineBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact fableMachineBoundaryDecodeEncodeBHist
  · constructor
    · exact fableMachineBoundary_round_trip
    · constructor
      · intro x y heq
        exact fableMachineBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.FableMachineBoundaryUp
