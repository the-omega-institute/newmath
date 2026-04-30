import BEDC.FKernel.Unary.Domain

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Cont

local instance : AskSetup := MinimalAskSetup
local instance : PackageSetup := MinimalPackageSetup
local instance : NameCertSetup := MinimalNameCertSetup

theorem nat_up_name_certificate : NameCert UnaryName := by
  exact NameCert.mk () () () () ()

theorem concrete_natup_namecert : NameCert UnaryName := by
  exact nat_up_name_certificate

theorem concrete_natup_namecert_primary : NameCert UnaryName := by
  exact NameCert.mk () () () () ()

theorem nat_up_name_certificate_witnesses :
    ∃ source : SourceSpec, ∃ pattern : PatternSpec, ∃ classifier : ClassifierSpec,
      ∃ stability : StabilityCert, ∃ ledger : LedgerPolicy, True := by
  have cert : NameCert UnaryName := nat_up_name_certificate
  cases cert with
  | mk source pattern classifier stability ledger =>
      exact ⟨source, pattern, classifier, stability, ledger, True.intro⟩

theorem nat_up_name_certificate_exists : Nonempty (NameCert UnaryName) := by
  exact Nonempty.intro nat_up_name_certificate

theorem nat_up_licensed_not_primitive : NameCert UnaryName ∧ Nonempty (NameCert UnaryName) := by
  constructor
  · exact nat_up_name_certificate
  · exact nat_up_name_certificate_exists

theorem nat_up_seed_from_unary_continuation :
    NameCert UnaryName ∧
      (∀ {h k r : BHist},
        UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r) := by
  constructor
  · exact nat_up_name_certificate
  · intro h k r uh uk hr
    exact unary_cont_closed uh uk hr

theorem nat_up_interface_seed :
    UnaryHistory BHist.Empty ∧
      (∀ {h k r : BHist}, UnaryHistory h → UnaryHistory k → Cont h k r → UnaryHistory r) ∧
        Nonempty (NameCert UnaryName) := by
  constructor
  · exact unary_empty
  · constructor
    · intro h k r uh uk hr
      exact unary_repetition_closed_under_continuation_seed uh uk hr
    · exact Nonempty.intro nat_up_name_certificate

theorem nat_up_certificate_seed_not_primitive :
    NameCert UnaryName ∧ Nonempty (NameCert UnaryName) := by
  exact nat_up_licensed_not_primitive

theorem nat_up_certificate_source_witness : Nonempty SourceSpec := by
  exact nameCert_source_witness_from_cert nat_up_name_certificate

theorem nat_up_certificate_field_witnesses :
    Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec /\
      Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  exact nameCert_field_witnesses nat_up_name_certificate

theorem nat_up_name_certificate_complete :
    NameCert UnaryName ∧ Nonempty SourceSpec ∧ Nonempty PatternSpec ∧
      Nonempty ClassifierSpec ∧ Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  exact And.intro nat_up_name_certificate nat_up_certificate_field_witnesses

theorem nat_up_certificate_has_ledger : Nonempty LedgerPolicy := by
  exact derived_interfaces_have_ledger nat_up_name_certificate

theorem nat_up_certificate_source_and_ledger :
    NameCert UnaryName ∧ Nonempty SourceSpec ∧ Nonempty LedgerPolicy := by
  constructor
  · exact nat_up_name_certificate
  · exact nameCert_source_and_ledger_from_cert nat_up_name_certificate

theorem nat_up_stability_witness : Nonempty StabilityCert := by
  exact Nonempty.intro ()

theorem nat_up_certificate_stability_and_ledger :
    Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  constructor
  · exact nat_up_stability_witness
  · exact nat_up_certificate_has_ledger

theorem add_up_name_certificate_exists : Nonempty (NameCert AddName) := by
  exact Nonempty.intro (NameCert.mk () () () () ())

theorem add_up_name_certificate : NameCert AddName := by
  exact NameCert.mk () () () () ()

theorem concrete_addup_namecert : NameCert AddName := by
  exact add_up_name_certificate

theorem add_up_licensed_not_primitive : NameCert AddName ∧ Nonempty (NameCert AddName) := by
  exact And.intro add_up_name_certificate add_up_name_certificate_exists

theorem add_up_certificate_field_witnesses :
    Nonempty SourceSpec /\ Nonempty PatternSpec /\ Nonempty ClassifierSpec /\
      Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  exact nameCert_field_witnesses add_up_name_certificate

theorem add_up_name_certificate_complete :
    NameCert AddName ∧ Nonempty SourceSpec ∧ Nonempty PatternSpec ∧
      Nonempty ClassifierSpec ∧ Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  exact And.intro add_up_name_certificate add_up_certificate_field_witnesses

theorem add_up_certificate_has_ledger : Nonempty LedgerPolicy := by
  exact derived_interfaces_have_ledger add_up_name_certificate

theorem add_up_ledger_policy_nonempty : Nonempty LedgerPolicy := by
  exact add_up_certificate_has_ledger

theorem add_up_certificate_stability_and_ledger :
    Nonempty StabilityCert /\ Nonempty LedgerPolicy := by
  exact nameCert_stability_and_ledger_from_cert add_up_name_certificate

theorem additive_stability_and_ledger_policy :
    Nonempty StabilityCert ∧ Nonempty LedgerPolicy := by
  have cert : NameCert AddName := add_up_name_certificate
  cases cert with
  | mk _ _ _ stability ledger =>
      exact And.intro (Nonempty.intro stability) (Nonempty.intro ledger)

theorem unary_addition_like_unit_with_certificate :
    Nonempty (NameCert AddName) ∧
      (forall {h left right : BHist},
        UnaryHistory h → Cont h BHist.Empty left → Cont BHist.Empty h right →
          UnaryHistory left ∧ UnaryHistory right ∧ hsame left h ∧ hsame right h) := by
  constructor
  · exact add_up_name_certificate_exists
  · intro h left right uh hleft hright
    exact unary_cont_unit uh hleft hright

def AddLedgerPolicy : Prop :=
  forall {h k r : BHist}, UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r

theorem addLedgerPolicy_from_unary_cont_closed : AddLedgerPolicy := by
  intro h k r uh uk cont
  exact unary_cont_closed uh uk cont

theorem unary_addition_seed_from_policy :
    AddLedgerPolicy -> forall {h k r : BHist},
      UnaryHistory h -> UnaryHistory k -> Cont h k r -> UnaryHistory r := by
  intro policy h k r uh uk cont
  exact policy uh uk cont

theorem unary_addition_seed : True := True.intro

theorem add_activation_stability_field (cert : NameCert UnaryName) : Nonempty StabilityCert := by
  cases cert with
  | mk _ _ _ stability _ =>
      exact Nonempty.intro stability

end BEDC.FKernel.Unary
