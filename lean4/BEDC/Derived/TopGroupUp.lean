import BEDC.Derived.GroupUp
import BEDC.Derived.TopologyUp.Singleton
import BEDC.FKernel.Unary

namespace BEDC.Derived.TopGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.GroupUp
open BEDC.Derived.TopologyUp

def TopGroupRootThresholdPackage
    (group topology product inverse neighborhood ledger provenance : BHist) : Prop :=
  GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory neighborhood ∧
    hsame product (append group topology) ∧ hsame inverse BHist.Empty ∧
      hsame ledger (append product inverse) ∧ hsame provenance ledger

theorem TopGroupRootThreshold_carrier_scope
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      GroupSingletonCarrier group ∧ TopologySingletonCarrier topology ∧ UnaryHistory group ∧
        UnaryHistory topology ∧ UnaryHistory neighborhood ∧ hsame ledger (append product inverse) ∧
          hsame provenance ledger := by
  intro package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  exact And.intro package.left
    (And.intro package.right.left
      (And.intro groupUnary
        (And.intro topologyUnary
          (And.intro package.right.right.left
            (And.intro package.right.right.right.right.right.left
              package.right.right.right.right.right.right)))))

theorem TopGroupRootThresholdPackage_shared_source_rows
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      Cont group topology product ∧ Cont product inverse ledger ∧ Cont ledger BHist.Empty provenance ∧
        UnaryHistory ledger ∧ UnaryHistory provenance := by
  intro package
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm package.left)
  have topologyUnary : UnaryHistory topology :=
    unary_transport unary_empty (hsame_symm package.right.left)
  have productCont : Cont group topology product := by
    exact package.right.right.right.left
  have inverseUnary : UnaryHistory inverse :=
    unary_transport unary_empty (hsame_symm package.right.right.right.right.left)
  have ledgerCont : Cont product inverse ledger := by
    exact package.right.right.right.right.right.left
  have productUnary : UnaryHistory product :=
    unary_cont_closed groupUnary topologyUnary productCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed productUnary inverseUnary ledgerCont
  have provenanceCont : Cont ledger BHist.Empty provenance := by
    cases package.right.right.right.right.right.right
    exact cont_right_unit ledger
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed ledgerUnary unary_empty provenanceCont
  exact And.intro productCont
    (And.intro ledgerCont
      (And.intro provenanceCont (And.intro ledgerUnary provenanceUnary)))

theorem TopGroupRootThresholdPackage_export_boundary_certificate
    {group topology product inverse neighborhood ledger provenance : BHist} :
    TopGroupRootThresholdPackage group topology product inverse neighborhood ledger provenance ->
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance) hsame ∧ hsame provenance BHist.Empty := by
  intro package
  have groupEmpty : hsame group BHist.Empty := package.left
  have topologyEmpty : hsame topology BHist.Empty := package.right.left
  have productEmpty : hsame product BHist.Empty := by
    have productAppend : hsame product (append group topology) := package.right.right.right.left
    have appendEmpty : hsame (append group topology) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro groupEmpty topologyEmpty)
    exact hsame_trans productAppend appendEmpty
  have inverseEmpty : hsame inverse BHist.Empty := package.right.right.right.right.left
  have ledgerEmpty : hsame ledger BHist.Empty := by
    have ledgerAppend : hsame ledger (append product inverse) :=
      package.right.right.right.right.right.left
    have appendEmpty : hsame (append product inverse) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro productEmpty inverseEmpty)
    exact hsame_trans ledgerAppend appendEmpty
  have provenanceEmpty : hsame provenance BHist.Empty :=
    hsame_trans package.right.right.right.right.right.right ledgerEmpty
  have provenanceSelf : hsame provenance provenance :=
    hsame_refl provenance
  have cert :
      SemanticNameCert (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance provenanceSelf
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        exact hsame_trans (hsame_symm sameHK) carrierH
    }
    pattern_sound := by
      intro h carrier
      exact carrier
    ledger_sound := by
      intro h carrier
      exact carrier
  }
  exact And.intro cert provenanceEmpty

end BEDC.Derived.TopGroupUp
