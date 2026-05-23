import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AllowedProofAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AllowedProofAuditUp : Type where
  | mk :
      (allowed refused scope witness localRefutation ledger transport continuation provenance
        localName : BHist) →
        AllowedProofAuditUp
  deriving DecidableEq

def allowedProofAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: allowedProofAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: allowedProofAuditEncodeBHist h

def allowedProofAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (allowedProofAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (allowedProofAuditDecodeBHist tail)

private theorem AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def allowedProofAuditFields : AllowedProofAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AllowedProofAuditUp.mk allowed refused scope witness localRefutation ledger transport
      continuation provenance localName =>
      [allowed, refused, scope, witness, localRefutation, ledger, transport, continuation,
        provenance, localName]

def allowedProofAuditToEventFlow : AllowedProofAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (allowedProofAuditFields x).map allowedProofAuditEncodeBHist

def allowedProofAuditFromEventFlow : EventFlow → Option AllowedProofAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | allowed :: rest0 =>
      match rest0 with
      | [] => none
      | refused :: rest1 =>
          match rest1 with
          | [] => none
          | scope :: rest2 =>
              match rest2 with
              | [] => none
              | witness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | localRefutation :: rest4 =>
                      match rest4 with
                      | [] => none
                      | ledger :: rest5 =>
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
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (AllowedProofAuditUp.mk
                                                  (allowedProofAuditDecodeBHist allowed)
                                                  (allowedProofAuditDecodeBHist refused)
                                                  (allowedProofAuditDecodeBHist scope)
                                                  (allowedProofAuditDecodeBHist witness)
                                                  (allowedProofAuditDecodeBHist localRefutation)
                                                  (allowedProofAuditDecodeBHist ledger)
                                                  (allowedProofAuditDecodeBHist transport)
                                                  (allowedProofAuditDecodeBHist continuation)
                                                  (allowedProofAuditDecodeBHist provenance)
                                                  (allowedProofAuditDecodeBHist localName))
                                          | _ :: _ => none

private theorem AllowedProofAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AllowedProofAuditUp,
      allowedProofAuditFromEventFlow (allowedProofAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk allowed refused scope witness localRefutation ledger transport continuation provenance
      localName =>
      change
        some
          (AllowedProofAuditUp.mk
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist allowed))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist refused))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist scope))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist witness))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist localRefutation))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist ledger))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist transport))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist continuation))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist provenance))
            (allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist localName))) =
          some
            (AllowedProofAuditUp.mk allowed refused scope witness localRefutation ledger transport
              continuation provenance localName)
      rw [AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode allowed,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode refused,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode scope,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode witness,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode localRefutation,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode ledger,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode transport,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode continuation,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode provenance,
        AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode localName]

private theorem AllowedProofAuditTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AllowedProofAuditUp} :
    allowedProofAuditToEventFlow x = allowedProofAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      allowedProofAuditFromEventFlow (allowedProofAuditToEventFlow x) =
        allowedProofAuditFromEventFlow (allowedProofAuditToEventFlow y) :=
    congrArg allowedProofAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AllowedProofAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AllowedProofAuditTasteGate_single_carrier_alignment_round_trip y)))

private theorem AllowedProofAuditTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : AllowedProofAuditUp,
      allowedProofAuditFields x = allowedProofAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk allowed₁ refused₁ scope₁ witness₁ localRefutation₁ ledger₁ transport₁
      continuation₁ provenance₁ localName₁ =>
      cases y with
      | mk allowed₂ refused₂ scope₂ witness₂ localRefutation₂ ledger₂ transport₂
          continuation₂ provenance₂ localName₂ =>
          injection hfields with hAllowed tail0
          injection tail0 with hRefused tail1
          injection tail1 with hScope tail2
          injection tail2 with hWitness tail3
          injection tail3 with hLocalRefutation tail4
          injection tail4 with hLedger tail5
          injection tail5 with hTransport tail6
          injection tail6 with hContinuation tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hLocalName _
          subst hAllowed
          subst hRefused
          subst hScope
          subst hWitness
          subst hLocalRefutation
          subst hLedger
          subst hTransport
          subst hContinuation
          subst hProvenance
          subst hLocalName
          rfl

instance allowedProofAuditBHistCarrier : BHistCarrier AllowedProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := allowedProofAuditToEventFlow
  fromEventFlow := allowedProofAuditFromEventFlow

instance allowedProofAuditChapterTasteGate : ChapterTasteGate AllowedProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change allowedProofAuditFromEventFlow (allowedProofAuditToEventFlow x) = some x
    exact AllowedProofAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AllowedProofAuditTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance allowedProofAuditFieldFaithful : FieldFaithful AllowedProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := allowedProofAuditFields
  field_faithful := AllowedProofAuditTasteGate_single_carrier_alignment_fields_faithful

instance allowedProofAuditNontrivial : Nontrivial AllowedProofAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AllowedProofAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AllowedProofAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AllowedProofAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  allowedProofAuditChapterTasteGate

theorem AllowedProofAuditTasteGate_single_carrier_alignment :
    (∀ h : BHist, allowedProofAuditDecodeBHist (allowedProofAuditEncodeBHist h) = h) ∧
      (∀ x : AllowedProofAuditUp,
        allowedProofAuditFromEventFlow (allowedProofAuditToEventFlow x) = some x) ∧
        (∀ x y : AllowedProofAuditUp,
          allowedProofAuditToEventFlow x = allowedProofAuditToEventFlow y → x = y) ∧
          allowedProofAuditEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨AllowedProofAuditTasteGate_single_carrier_alignment_decode_encode,
      AllowedProofAuditTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        AllowedProofAuditTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

def AllowedProofAuditPacket [AskSetup] [PackageSetup]
    (allowed refused scope witness localRefutation ledger transport continuation provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory allowed ∧ UnaryHistory refused ∧ UnaryHistory scope ∧ UnaryHistory witness ∧
    UnaryHistory localRefutation ∧
      Cont allowed refused ledger ∧
        Cont scope witness transport ∧
          Cont localRefutation ledger continuation ∧
            Cont transport continuation provenance ∧
              Cont provenance localName localName ∧ PkgSig bundle provenance pkg

theorem AllowedProofAuditPacket_namecert_obligations [AskSetup] [PackageSetup]
    {allowed refused scope witness localRefutation ledger transport continuation provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AllowedProofAuditPacket allowed refused scope witness localRefutation ledger transport
      continuation provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          AllowedProofAuditPacket allowed refused scope witness localRefutation ledger
            transport continuation provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          AllowedProofAuditPacket allowed refused scope witness localRefutation ledger
            transport continuation provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          AllowedProofAuditPacket allowed refused scope witness localRefutation ledger
            transport continuation provenance localName bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro localName (And.intro packet (hsame_refl localName))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row col same
        exact hsame_symm same
      equiv_trans := by
        intro row col next sameRowCol sameColNext
        exact hsame_trans sameRowCol sameColNext
      carrier_respects_equiv := by
        intro row col same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem AllowedProofAuditNonEscape [AskSetup] [PackageSetup]
    {allowed refused scope witness localRefutation ledger transport continuation provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AllowedProofAuditPacket allowed refused scope witness localRefutation ledger transport
      continuation provenance localName bundle pkg →
      ∃ x : AllowedProofAuditUp,
        x =
            AllowedProofAuditUp.mk allowed refused scope witness localRefutation ledger transport
              continuation provenance localName ∧
          List.Mem witness (allowedProofAuditFields x) ∧
            List.Mem localRefutation (allowedProofAuditFields x) ∧
              List.Mem ledger (allowedProofAuditFields x) ∧
                Cont scope witness transport ∧
                  Cont localRefutation ledger continuation ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle PkgSig
  intro packet
  rcases packet with
    ⟨_allowedHistory, _refusedHistory, _scopeHistory, _witnessHistory,
      _localRefutationHistory, _allowedRefusedLedger, scopeWitnessTransport,
      localRefutationLedgerContinuation, _transportContinuationProvenance,
      _provenanceLocalName, provenancePkg⟩
  refine
    ⟨AllowedProofAuditUp.mk allowed refused scope witness localRefutation ledger transport
        continuation provenance localName, rfl, ?_, ?_, ?_, scopeWitnessTransport,
      localRefutationLedgerContinuation, provenancePkg⟩
  · exact
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ (List.Mem.head _)
  · exact
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ (List.Mem.head _)
  · exact
      List.Mem.tail _ <|
        List.Mem.tail _ <|
          List.Mem.tail _ <|
            List.Mem.tail _ <|
              List.Mem.tail _ (List.Mem.head _)

end BEDC.Derived.AllowedProofAuditUp
