import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExternalSupplySignatureSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExternalSupplySignatureSealUp : Type where
  | mk :
      (source representation signature gap descent ledger transport replay provenance
        localName : BHist) → ExternalSupplySignatureSealUp
  deriving DecidableEq

def externalSupplySignatureSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: externalSupplySignatureSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: externalSupplySignatureSealEncodeBHist h

def externalSupplySignatureSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (externalSupplySignatureSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (externalSupplySignatureSealDecodeBHist tail)

private theorem externalSupplySignatureSealDecodeEncodeBHist :
    ∀ h : BHist,
      externalSupplySignatureSealDecodeBHist
        (externalSupplySignatureSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def externalSupplySignatureSealFields : ExternalSupplySignatureSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ExternalSupplySignatureSealUp.mk source representation signature gap descent ledger
      transport replay provenance localName =>
      [source, representation, signature, gap, descent, ledger, transport, replay,
        provenance, localName]

def externalSupplySignatureSealToEventFlow :
    ExternalSupplySignatureSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (externalSupplySignatureSealFields x).map externalSupplySignatureSealEncodeBHist

def externalSupplySignatureSealFromEventFlow :
    EventFlow → Option ExternalSupplySignatureSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [source, representation, signature, gap, descent, ledger, transport, replay, provenance,
      localName] =>
      some
        (ExternalSupplySignatureSealUp.mk
          (externalSupplySignatureSealDecodeBHist source)
          (externalSupplySignatureSealDecodeBHist representation)
          (externalSupplySignatureSealDecodeBHist signature)
          (externalSupplySignatureSealDecodeBHist gap)
          (externalSupplySignatureSealDecodeBHist descent)
          (externalSupplySignatureSealDecodeBHist ledger)
          (externalSupplySignatureSealDecodeBHist transport)
          (externalSupplySignatureSealDecodeBHist replay)
          (externalSupplySignatureSealDecodeBHist provenance)
          (externalSupplySignatureSealDecodeBHist localName))
  | _ => none

private theorem externalSupplySignatureSeal_round_trip :
    ∀ x : ExternalSupplySignatureSealUp,
      externalSupplySignatureSealFromEventFlow
        (externalSupplySignatureSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source representation signature gap descent ledger transport replay provenance localName =>
      change
        some
          (ExternalSupplySignatureSealUp.mk
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist source))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist representation))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist signature))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist gap))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist descent))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist ledger))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist transport))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist replay))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist provenance))
            (externalSupplySignatureSealDecodeBHist
              (externalSupplySignatureSealEncodeBHist localName))) =
          some
            (ExternalSupplySignatureSealUp.mk source representation signature gap descent ledger
              transport replay provenance localName)
      rw [externalSupplySignatureSealDecodeEncodeBHist source,
        externalSupplySignatureSealDecodeEncodeBHist representation,
        externalSupplySignatureSealDecodeEncodeBHist signature,
        externalSupplySignatureSealDecodeEncodeBHist gap,
        externalSupplySignatureSealDecodeEncodeBHist descent,
        externalSupplySignatureSealDecodeEncodeBHist ledger,
        externalSupplySignatureSealDecodeEncodeBHist transport,
        externalSupplySignatureSealDecodeEncodeBHist replay,
        externalSupplySignatureSealDecodeEncodeBHist provenance,
        externalSupplySignatureSealDecodeEncodeBHist localName]

private theorem externalSupplySignatureSealToEventFlow_injective
    {x y : ExternalSupplySignatureSealUp} :
    externalSupplySignatureSealToEventFlow x =
      externalSupplySignatureSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      externalSupplySignatureSealFromEventFlow (externalSupplySignatureSealToEventFlow x) =
        externalSupplySignatureSealFromEventFlow (externalSupplySignatureSealToEventFlow y) :=
    congrArg externalSupplySignatureSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (externalSupplySignatureSeal_round_trip x).symm
      (Eq.trans hread (externalSupplySignatureSeal_round_trip y)))

private theorem externalSupplySignatureSeal_fields_faithful :
    ∀ x y : ExternalSupplySignatureSealUp,
      externalSupplySignatureSealFields x = externalSupplySignatureSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ representation₁ signature₁ gap₁ descent₁ ledger₁ transport₁ replay₁
      provenance₁ localName₁ =>
      cases y with
      | mk source₂ representation₂ signature₂ gap₂ descent₂ ledger₂ transport₂ replay₂
          provenance₂ localName₂ =>
          injection hfields with hsource tail0
          injection tail0 with hrepresentation tail1
          injection tail1 with hsignature tail2
          injection tail2 with hgap tail3
          injection tail3 with hdescent tail4
          injection tail4 with hledger tail5
          injection tail5 with htransport tail6
          injection tail6 with hreplay tail7
          injection tail7 with hprovenance tail8
          injection tail8 with hlocalName _
          subst hsource
          subst hrepresentation
          subst hsignature
          subst hgap
          subst hdescent
          subst hledger
          subst htransport
          subst hreplay
          subst hprovenance
          subst hlocalName
          rfl

instance externalSupplySignatureSealBHistCarrier :
    BHistCarrier ExternalSupplySignatureSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := externalSupplySignatureSealToEventFlow
  fromEventFlow := externalSupplySignatureSealFromEventFlow

instance externalSupplySignatureSealChapterTasteGate :
    ChapterTasteGate ExternalSupplySignatureSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      externalSupplySignatureSealFromEventFlow
        (externalSupplySignatureSealToEventFlow x) = some x
    exact externalSupplySignatureSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (externalSupplySignatureSealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ExternalSupplySignatureSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  inferInstance

instance externalSupplySignatureSealFieldFaithful :
    FieldFaithful ExternalSupplySignatureSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := externalSupplySignatureSealFields
  field_faithful := externalSupplySignatureSeal_fields_faithful

instance externalSupplySignatureSealNontrivial : Nontrivial ExternalSupplySignatureSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ExternalSupplySignatureSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ExternalSupplySignatureSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hsource _ _ _ _ _ _ _ _ _
        cases hsource⟩

theorem ExternalSupplySignatureSealNameCert_obligations
    {source representation signature gap descent ledger transport replay provenance
      localName : BHist}
    (sourceRepresentationSignature : Cont source representation signature)
    (gapDescentLedger : Cont gap descent ledger)
    (signatureGapLocal : Cont signature gap localName) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row source ∧
          ∃ packet : ExternalSupplySignatureSealUp,
            packet =
              ExternalSupplySignatureSealUp.mk source representation signature gap descent
                ledger transport replay provenance localName)
      (fun row : BHist =>
        hsame row source ∧ Cont source representation signature ∧
          Cont gap descent ledger)
      (fun row : BHist =>
        Cont signature gap localName ∧ hsame row source ∧ hsame transport transport ∧
          hsame replay replay ∧ hsame provenance provenance ∧ hsame localName localName)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro source
          ⟨hsame_refl source,
            Exists.intro
              (ExternalSupplySignatureSealUp.mk source representation signature gap descent
                ledger transport replay provenance localName)
              rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, sourceRepresentationSignature, gapDescentLedger⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨signatureGapLocal, sourceRow.left, hsame_refl transport, hsame_refl replay,
          hsame_refl provenance, hsame_refl localName⟩
  }

end BEDC.Derived.ExternalSupplySignatureSealUp
