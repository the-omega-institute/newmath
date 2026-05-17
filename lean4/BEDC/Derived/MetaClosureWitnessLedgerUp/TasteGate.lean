import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaClosureWitnessLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaClosureWitnessLedgerUp : Type where
  | mk :
      (witness classifierTransport directionalTransport dependencyAudit replacement componentHsame
        continuation provenance localName : BHist) →
      MetaClosureWitnessLedgerUp
  deriving DecidableEq

def metaClosureWitnessLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaClosureWitnessLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaClosureWitnessLedgerEncodeBHist h

def metaClosureWitnessLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaClosureWitnessLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaClosureWitnessLedgerDecodeBHist tail)

private theorem metaClosureWitnessLedgerDecodeEncodeBHist :
    ∀ h : BHist,
      metaClosureWitnessLedgerDecodeBHist (metaClosureWitnessLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaClosureWitnessLedgerFields : MetaClosureWitnessLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaClosureWitnessLedgerUp.mk witness classifierTransport directionalTransport
      dependencyAudit replacement componentHsame continuation provenance localName =>
      [witness, classifierTransport, directionalTransport, dependencyAudit, replacement,
        componentHsame, continuation, provenance, localName]

def metaClosureWitnessLedgerToEventFlow : MetaClosureWitnessLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaClosureWitnessLedgerUp.mk witness classifierTransport directionalTransport
      dependencyAudit replacement componentHsame continuation provenance localName =>
      [metaClosureWitnessLedgerEncodeBHist witness,
        metaClosureWitnessLedgerEncodeBHist classifierTransport,
        metaClosureWitnessLedgerEncodeBHist directionalTransport,
        metaClosureWitnessLedgerEncodeBHist dependencyAudit,
        metaClosureWitnessLedgerEncodeBHist replacement,
        metaClosureWitnessLedgerEncodeBHist componentHsame,
        metaClosureWitnessLedgerEncodeBHist continuation,
        metaClosureWitnessLedgerEncodeBHist provenance,
        metaClosureWitnessLedgerEncodeBHist localName]

def metaClosureWitnessLedgerFromEventFlow :
    EventFlow → Option MetaClosureWitnessLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | witness :: rest0 =>
      match rest0 with
      | [] => none
      | classifierTransport :: rest1 =>
          match rest1 with
          | [] => none
          | directionalTransport :: rest2 =>
              match rest2 with
              | [] => none
              | dependencyAudit :: rest3 =>
                  match rest3 with
                  | [] => none
                  | replacement :: rest4 =>
                      match rest4 with
                      | [] => none
                      | componentHsame :: rest5 =>
                          match rest5 with
                          | [] => none
                          | continuation :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (MetaClosureWitnessLedgerUp.mk
                                              (metaClosureWitnessLedgerDecodeBHist witness)
                                              (metaClosureWitnessLedgerDecodeBHist
                                                classifierTransport)
                                              (metaClosureWitnessLedgerDecodeBHist
                                                directionalTransport)
                                              (metaClosureWitnessLedgerDecodeBHist
                                                dependencyAudit)
                                              (metaClosureWitnessLedgerDecodeBHist replacement)
                                              (metaClosureWitnessLedgerDecodeBHist
                                                componentHsame)
                                              (metaClosureWitnessLedgerDecodeBHist continuation)
                                              (metaClosureWitnessLedgerDecodeBHist provenance)
                                              (metaClosureWitnessLedgerDecodeBHist localName))
                                      | _ :: _ => none

private theorem metaClosureWitnessLedger_round_trip :
    ∀ x : MetaClosureWitnessLedgerUp,
      metaClosureWitnessLedgerFromEventFlow (metaClosureWitnessLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk witness classifierTransport directionalTransport dependencyAudit replacement
      componentHsame continuation provenance localName =>
      change
        some
          (MetaClosureWitnessLedgerUp.mk
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist witness))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist classifierTransport))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist directionalTransport))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist dependencyAudit))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist replacement))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist componentHsame))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist continuation))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist provenance))
            (metaClosureWitnessLedgerDecodeBHist
              (metaClosureWitnessLedgerEncodeBHist localName))) =
          some
            (MetaClosureWitnessLedgerUp.mk witness classifierTransport directionalTransport
              dependencyAudit replacement componentHsame continuation provenance localName)
      rw [metaClosureWitnessLedgerDecodeEncodeBHist witness,
        metaClosureWitnessLedgerDecodeEncodeBHist classifierTransport,
        metaClosureWitnessLedgerDecodeEncodeBHist directionalTransport,
        metaClosureWitnessLedgerDecodeEncodeBHist dependencyAudit,
        metaClosureWitnessLedgerDecodeEncodeBHist replacement,
        metaClosureWitnessLedgerDecodeEncodeBHist componentHsame,
        metaClosureWitnessLedgerDecodeEncodeBHist continuation,
        metaClosureWitnessLedgerDecodeEncodeBHist provenance,
        metaClosureWitnessLedgerDecodeEncodeBHist localName]

private theorem metaClosureWitnessLedgerToEventFlow_injective
    {x y : MetaClosureWitnessLedgerUp} :
    metaClosureWitnessLedgerToEventFlow x = metaClosureWitnessLedgerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaClosureWitnessLedgerFromEventFlow (metaClosureWitnessLedgerToEventFlow x) =
        metaClosureWitnessLedgerFromEventFlow (metaClosureWitnessLedgerToEventFlow y) :=
    congrArg metaClosureWitnessLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaClosureWitnessLedger_round_trip x).symm
      (Eq.trans hread (metaClosureWitnessLedger_round_trip y)))

private theorem metaClosureWitnessLedger_field_faithful :
    ∀ x y : MetaClosureWitnessLedgerUp,
      metaClosureWitnessLedgerFields x = metaClosureWitnessLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk witness₁ classifierTransport₁ directionalTransport₁ dependencyAudit₁ replacement₁
      componentHsame₁ continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk witness₂ classifierTransport₂ directionalTransport₂ dependencyAudit₂ replacement₂
          componentHsame₂ continuation₂ provenance₂ localName₂ =>
          injection hfields with hwitness tail0
          injection tail0 with hclassifierTransport tail1
          injection tail1 with hdirectionalTransport tail2
          injection tail2 with hdependencyAudit tail3
          injection tail3 with hreplacement tail4
          injection tail4 with hcomponentHsame tail5
          injection tail5 with hcontinuation tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hlocalName _
          subst hwitness
          subst hclassifierTransport
          subst hdirectionalTransport
          subst hdependencyAudit
          subst hreplacement
          subst hcomponentHsame
          subst hcontinuation
          subst hprovenance
          subst hlocalName
          rfl

instance metaClosureWitnessLedgerBHistCarrier : BHistCarrier MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaClosureWitnessLedgerToEventFlow
  fromEventFlow := metaClosureWitnessLedgerFromEventFlow

instance metaClosureWitnessLedgerChapterTasteGate :
    ChapterTasteGate MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaClosureWitnessLedgerFromEventFlow (metaClosureWitnessLedgerToEventFlow x) =
      some x
    exact metaClosureWitnessLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaClosureWitnessLedgerToEventFlow_injective heq)

instance metaClosureWitnessLedgerFieldFaithful : FieldFaithful MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaClosureWitnessLedgerFields
  field_faithful := metaClosureWitnessLedger_field_faithful

instance metaClosureWitnessLedgerNontrivial : Nontrivial MetaClosureWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaClosureWitnessLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaClosureWitnessLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaClosureWitnessLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaClosureWitnessLedgerChapterTasteGate

theorem MetaClosureWitnessLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaClosureWitnessLedgerDecodeBHist
      (metaClosureWitnessLedgerEncodeBHist h) = h) ∧
      (∀ x : MetaClosureWitnessLedgerUp,
        metaClosureWitnessLedgerFromEventFlow (metaClosureWitnessLedgerToEventFlow x) =
          some x) ∧
        (∀ x y : MetaClosureWitnessLedgerUp,
          metaClosureWitnessLedgerToEventFlow x = metaClosureWitnessLedgerToEventFlow y →
            x = y) ∧
          metaClosureWitnessLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaClosureWitnessLedgerDecodeEncodeBHist
  · constructor
    · exact metaClosureWitnessLedger_round_trip
    · constructor
      · intro x y heq
        cases x with
        | mk witness₁ classifierTransport₁ directionalTransport₁ dependencyAudit₁
            replacement₁ componentHsame₁ continuation₁ provenance₁ localName₁ =>
            cases y with
            | mk witness₂ classifierTransport₂ directionalTransport₂ dependencyAudit₂
                replacement₂ componentHsame₂ continuation₂ provenance₂ localName₂ =>
                injection heq with hwitness tail0
                injection tail0 with hclassifierTransport tail1
                injection tail1 with hdirectionalTransport tail2
                injection tail2 with hdependencyAudit tail3
                injection tail3 with hreplacement tail4
                injection tail4 with hcomponentHsame tail5
                injection tail5 with hcontinuation tail6
                injection tail6 with hprovenance tail7
                injection tail7 with hlocalName _
                have witnessEq : witness₁ = witness₂ := by
                  have hdecode := congrArg metaClosureWitnessLedgerDecodeBHist hwitness
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist witness₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist witness₂] at hdecode
                  exact hdecode
                have classifierTransportEq : classifierTransport₁ = classifierTransport₂ := by
                  have hdecode :=
                    congrArg metaClosureWitnessLedgerDecodeBHist hclassifierTransport
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist classifierTransport₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist classifierTransport₂] at hdecode
                  exact hdecode
                have directionalTransportEq :
                    directionalTransport₁ = directionalTransport₂ := by
                  have hdecode :=
                    congrArg metaClosureWitnessLedgerDecodeBHist hdirectionalTransport
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist directionalTransport₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist directionalTransport₂] at hdecode
                  exact hdecode
                have dependencyAuditEq : dependencyAudit₁ = dependencyAudit₂ := by
                  have hdecode := congrArg metaClosureWitnessLedgerDecodeBHist hdependencyAudit
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist dependencyAudit₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist dependencyAudit₂] at hdecode
                  exact hdecode
                have replacementEq : replacement₁ = replacement₂ := by
                  have hdecode := congrArg metaClosureWitnessLedgerDecodeBHist hreplacement
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist replacement₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist replacement₂] at hdecode
                  exact hdecode
                have componentHsameEq : componentHsame₁ = componentHsame₂ := by
                  have hdecode := congrArg metaClosureWitnessLedgerDecodeBHist hcomponentHsame
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist componentHsame₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist componentHsame₂] at hdecode
                  exact hdecode
                have continuationEq : continuation₁ = continuation₂ := by
                  have hdecode := congrArg metaClosureWitnessLedgerDecodeBHist hcontinuation
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist continuation₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist continuation₂] at hdecode
                  exact hdecode
                have provenanceEq : provenance₁ = provenance₂ := by
                  have hdecode := congrArg metaClosureWitnessLedgerDecodeBHist hprovenance
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist provenance₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist provenance₂] at hdecode
                  exact hdecode
                have localNameEq : localName₁ = localName₂ := by
                  have hdecode := congrArg metaClosureWitnessLedgerDecodeBHist hlocalName
                  rw [metaClosureWitnessLedgerDecodeEncodeBHist localName₁,
                    metaClosureWitnessLedgerDecodeEncodeBHist localName₂] at hdecode
                  exact hdecode
                cases witnessEq
                cases classifierTransportEq
                cases directionalTransportEq
                cases dependencyAuditEq
                cases replacementEq
                cases componentHsameEq
                cases continuationEq
                cases provenanceEq
                cases localNameEq
                rfl
      · rfl

end BEDC.Derived.MetaClosureWitnessLedgerUp
