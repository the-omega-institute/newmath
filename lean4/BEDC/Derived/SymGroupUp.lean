import BEDC.Derived.GroupUp
import BEDC.Derived.PermutationUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SymGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.PermutationUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SymGroupCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
        tgtBundle srcPkg tgtPkg ->
      SemanticNameCert
          (fun endpoint : BHist => hsame endpoint ledger ∧ UnaryHistory endpoint)
          (fun endpoint : BHist => hsame endpoint ledger ∧ UnaryHistory endpoint)
          (fun endpoint : BHist => hsame endpoint ledger ∧ UnaryHistory endpoint)
          hsame ∧
        (∀ {tail : BHist}, hsame ledger (BHist.e0 tail) -> False) ∧
          (∀ {tail : BHist}, hsame action (BHist.e0 tail) -> False) := by
  intro row
  have surface := PermutationBijectionSourceRow_carrier_surface row
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledger (And.intro (hsame_refl ledger) surface.right.right.right.left)
        equiv_refl := by
          intro endpoint _endpointCarrier
          exact hsame_refl endpoint
        equiv_symm := by
          intro _endpoint leftEndpoint same
          exact hsame_symm same
        equiv_trans := by
          intro _endpoint _middle rightEndpoint sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro endpoint endpoint' sameEndpoint endpointCarrier
          exact And.intro
            (hsame_trans (hsame_symm sameEndpoint) endpointCarrier.left)
            (unary_transport endpointCarrier.right sameEndpoint)
      }
      pattern_sound := by
        intro _endpoint source
        exact source
      ledger_sound := by
        intro _endpoint source
        exact source
    }
  · constructor
    · intro tail sameLedger
      have zeroUnary : UnaryHistory (BHist.e0 tail) :=
        unary_transport surface.right.right.right.left sameLedger
      exact unary_no_zero_extension zeroUnary
    · intro tail sameAction
      have zeroUnary : UnaryHistory (BHist.e0 tail) :=
        unary_transport surface.right.right.left sameAction
      exact unary_no_zero_extension zeroUnary

theorem SymGroupPermutationCarrier_group_surface [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      GroupSingletonCarrier BHist.Empty ∧ UnaryHistory graph ∧ UnaryHistory invGraph ∧
        UnaryHistory action ∧ UnaryHistory ledger ∧ Cont graph invGraph comp ∧
          Cont src graph action ∧ Cont comp action ledger ∧
            PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg := by
  intro row
  have surface := PermutationBijectionSourceRow_carrier_surface row
  exact And.intro (hsame_refl BHist.Empty)
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro surface.right.right.right.left
            (And.intro surface.right.right.right.right.right.right.left
              (And.intro surface.right.right.right.right.right.right.right.left
                (And.intro surface.right.right.right.right.right.right.right.right.left
                  surface.right.right.right.right.right.right.right.right.right)))))))

theorem SymGroupCarrier_obligation [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      hsame src BHist.Empty ->
        hsame tgt BHist.Empty ->
          GroupSingletonCarrier graph ∧ GroupSingletonCarrier invGraph ∧
            GroupSingletonCarrier comp ∧ GroupSingletonCarrier action ∧
              GroupSingletonCarrier ledger := by
  intro row srcEmpty tgtEmpty
  cases srcEmpty
  cases tgtEmpty
  have graphCarrier : GroupSingletonCarrier graph :=
    row.right.right.left
  have invGraphCarrier : GroupSingletonCarrier invGraph :=
    row.right.right.right.left
  have compCarrier : GroupSingletonCarrier comp := by
    cases graphCarrier
    cases invGraphCarrier
    exact row.right.right.right.right.left
  have actionCarrier : GroupSingletonCarrier action := by
    cases graphCarrier
    exact row.right.right.right.right.right.left
  have ledgerCarrier : GroupSingletonCarrier ledger := by
    cases compCarrier
    cases actionCarrier
    exact row.right.right.right.right.right.right.left
  exact ⟨graphCarrier, invGraphCarrier, compCarrier, actionCarrier, ledgerCarrier⟩

def SymGroupPermutationCarrier [AskSetup] [PackageSetup]
    (src tgt graph invGraph comp action ledger : BHist)
    (srcBundle tgtBundle : ProbeBundle ProbeName) (srcPkg tgtPkg : Pkg) : Prop :=
  PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle tgtBundle
      srcPkg tgtPkg ∧
    GroupSingletonCarrier comp ∧ GroupSingletonCarrier action

theorem SymGroupPermutationCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    SymGroupPermutationCarrier src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
          tgtBundle srcPkg tgtPkg ∧
        GroupSingletonCarrier comp ∧ GroupSingletonCarrier action ∧
          UnaryHistory graph ∧ UnaryHistory invGraph ∧ UnaryHistory action ∧ UnaryHistory ledger ∧
            Cont graph invGraph comp ∧ Cont src graph action ∧ Cont comp action ledger ∧
              PkgSig srcBundle src srcPkg ∧ PkgSig tgtBundle tgt tgtPkg := by
  intro carrier
  have surface := PermutationBijectionSourceRow_carrier_surface carrier.left
  exact ⟨carrier.left, carrier.right.left, carrier.right.right, surface.left, surface.right.left,
    surface.right.right.left, surface.right.right.right.left,
    surface.right.right.right.right.right.right.left,
    surface.right.right.right.right.right.right.right.left,
    surface.right.right.right.right.right.right.right.right.left,
    surface.right.right.right.right.right.right.right.right.right⟩

theorem SymGroupPermutationCarrier_classifier_obligation [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    SymGroupPermutationCarrier src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      SemanticNameCert GroupSingletonCarrier GroupSingletonCarrier GroupSingletonCarrier
          GroupSingletonClassifier ∧
        GroupSingletonClassifier graph graph ∧ GroupSingletonClassifier invGraph invGraph ∧
          GroupSingletonClassifier comp comp ∧ GroupSingletonClassifier action action ∧
            GroupSingletonClassifier ledger ledger := by
  intro carrier
  have rows := SymGroupPermutationCarrier_carrier_obligation carrier
  have laws := GroupSingletonHistory_laws
  have cert :
      SemanticNameCert GroupSingletonCarrier GroupSingletonCarrier GroupSingletonCarrier
        GroupSingletonClassifier := laws.left
  have graphCarrier : GroupSingletonCarrier graph := by
    have compEmpty : hsame (append graph invGraph) BHist.Empty :=
      rows.right.right.right.right.right.right.left.symm.trans rows.right.left
    exact (append_eq_empty_iff.mp compEmpty).left
  have invGraphCarrier : GroupSingletonCarrier invGraph := by
    have compEmpty : hsame (append graph invGraph) BHist.Empty :=
      rows.right.right.right.right.right.right.left.symm.trans rows.right.left
    exact (append_eq_empty_iff.mp compEmpty).right
  have compCarrier : GroupSingletonCarrier comp := rows.right.left
  have srcCarrier : GroupSingletonCarrier src := by
    have graphEmpty : hsame (append src tgt) BHist.Empty :=
      rows.left.right.right.left.symm.trans graphCarrier
    exact (append_eq_empty_iff.mp graphEmpty).left
  have actionCarrier : GroupSingletonCarrier action := by
    have actionEmpty : hsame (append src graph) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro srcCarrier graphCarrier)
    exact rows.right.right.right.right.right.right.right.left.trans actionEmpty
  have ledgerCarrier : GroupSingletonCarrier ledger := by
    have compActionEmpty : hsame (append comp action) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro compCarrier actionCarrier)
    exact rows.right.right.right.right.right.right.right.right.left.trans compActionEmpty
  have graphClassified : GroupSingletonClassifier graph graph :=
    cert.core.equiv_refl graphCarrier
  have invGraphClassified : GroupSingletonClassifier invGraph invGraph :=
    cert.core.equiv_refl invGraphCarrier
  have compClassified : GroupSingletonClassifier comp comp :=
    cert.core.equiv_refl compCarrier
  have actionClassified : GroupSingletonClassifier action action :=
    cert.core.equiv_refl actionCarrier
  have ledgerClassified : GroupSingletonClassifier ledger ledger :=
    cert.core.equiv_refl ledgerCarrier
  exact And.intro cert
    (And.intro graphClassified
      (And.intro invGraphClassified
        (And.intro compClassified (And.intro actionClassified ledgerClassified))))

end BEDC.Derived.SymGroupUp
