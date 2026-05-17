import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UseRuleLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UseRuleLedgerUp : Type where
  | mk :
      (useEvent rule sourceClassifier stability ledger publicAudit transport continuation provenance
        localName : BHist) →
        UseRuleLedgerUp
  deriving DecidableEq

def useRuleLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: useRuleLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: useRuleLedgerEncodeBHist h

def useRuleLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (useRuleLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (useRuleLedgerDecodeBHist tail)

private theorem UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def useRuleLedgerFields : UseRuleLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UseRuleLedgerUp.mk useEvent rule sourceClassifier stability ledger publicAudit transport
      continuation provenance localName =>
      [useEvent, rule, sourceClassifier, stability, ledger, publicAudit, transport,
        continuation, provenance, localName]

def useRuleLedgerToEventFlow : UseRuleLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (useRuleLedgerFields x).map useRuleLedgerEncodeBHist

def useRuleLedgerFromEventFlow : EventFlow → Option UseRuleLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | useEvent :: rule :: sourceClassifier :: stability :: ledger :: publicAudit :: transport ::
      continuation :: provenance :: localName :: [] =>
      some
        (UseRuleLedgerUp.mk
          (useRuleLedgerDecodeBHist useEvent)
          (useRuleLedgerDecodeBHist rule)
          (useRuleLedgerDecodeBHist sourceClassifier)
          (useRuleLedgerDecodeBHist stability)
          (useRuleLedgerDecodeBHist ledger)
          (useRuleLedgerDecodeBHist publicAudit)
          (useRuleLedgerDecodeBHist transport)
          (useRuleLedgerDecodeBHist continuation)
          (useRuleLedgerDecodeBHist provenance)
          (useRuleLedgerDecodeBHist localName))
  | _ => none

private theorem UseRuleLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UseRuleLedgerUp,
      useRuleLedgerFromEventFlow (useRuleLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk useEvent rule sourceClassifier stability ledger publicAudit transport continuation
      provenance localName =>
      change
        some
          (UseRuleLedgerUp.mk
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist useEvent))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist rule))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist sourceClassifier))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist stability))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist ledger))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist publicAudit))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist transport))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist continuation))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist provenance))
            (useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist localName))) =
          some
            (UseRuleLedgerUp.mk useEvent rule sourceClassifier stability ledger publicAudit
              transport continuation provenance localName)
      rw [UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode useEvent,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode rule,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode sourceClassifier,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode stability,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode ledger,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode publicAudit,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode transport,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode continuation,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode provenance,
        UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode localName]

private theorem UseRuleLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UseRuleLedgerUp} :
    useRuleLedgerToEventFlow x = useRuleLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      useRuleLedgerFromEventFlow (useRuleLedgerToEventFlow x) =
        useRuleLedgerFromEventFlow (useRuleLedgerToEventFlow y) :=
    congrArg useRuleLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UseRuleLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UseRuleLedgerTasteGate_single_carrier_alignment_round_trip y)))

private theorem UseRuleLedgerTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : UseRuleLedgerUp,
      useRuleLedgerFields x = useRuleLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk useEvent₁ rule₁ sourceClassifier₁ stability₁ ledger₁ publicAudit₁ transport₁
      continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk useEvent₂ rule₂ sourceClassifier₂ stability₂ ledger₂ publicAudit₂ transport₂
          continuation₂ provenance₂ localName₂ =>
          injection hfields with hUseEvent tail0
          injection tail0 with hRule tail1
          injection tail1 with hSourceClassifier tail2
          injection tail2 with hStability tail3
          injection tail3 with hLedger tail4
          injection tail4 with hPublicAudit tail5
          injection tail5 with hTransport tail6
          injection tail6 with hContinuation tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hLocalName _
          subst hUseEvent
          subst hRule
          subst hSourceClassifier
          subst hStability
          subst hLedger
          subst hPublicAudit
          subst hTransport
          subst hContinuation
          subst hProvenance
          subst hLocalName
          rfl

instance useRuleLedgerBHistCarrier : BHistCarrier UseRuleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := useRuleLedgerToEventFlow
  fromEventFlow := useRuleLedgerFromEventFlow

instance useRuleLedgerChapterTasteGate : ChapterTasteGate UseRuleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change useRuleLedgerFromEventFlow (useRuleLedgerToEventFlow x) = some x
    exact UseRuleLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UseRuleLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance useRuleLedgerFieldFaithful : FieldFaithful UseRuleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := useRuleLedgerFields
  field_faithful := UseRuleLedgerTasteGate_single_carrier_alignment_fields_faithful

instance useRuleLedgerNontrivial : Nontrivial UseRuleLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UseRuleLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UseRuleLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UseRuleLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  useRuleLedgerChapterTasteGate

theorem UseRuleLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, useRuleLedgerDecodeBHist (useRuleLedgerEncodeBHist h) = h) ∧
      useRuleLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
      (∀ x y : UseRuleLedgerUp,
        useRuleLedgerFields x = useRuleLedgerFields y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨UseRuleLedgerTasteGate_single_carrier_alignment_decode_encode, rfl,
      UseRuleLedgerTasteGate_single_carrier_alignment_fields_faithful⟩

end BEDC.Derived.UseRuleLedgerUp
