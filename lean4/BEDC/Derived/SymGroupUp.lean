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

theorem SymGroupPermutationClassifier_stability [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger src' tgt' graph' invGraph' comp' action'
      ledger' : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    SymGroupPermutationCarrier src tgt graph invGraph comp action ledger srcBundle tgtBundle
        srcPkg tgtPkg ->
      hsame src src' -> hsame tgt tgt' -> PkgSig srcBundle src' srcPkg ->
        PkgSig tgtBundle tgt' tgtPkg -> Cont src' tgt' graph' ->
          Cont tgt' src' invGraph' -> Cont graph' invGraph' comp' ->
            Cont src' graph' action' -> Cont comp' action' ledger' ->
              SymGroupPermutationCarrier src' tgt' graph' invGraph' comp' action' ledger'
                  srcBundle tgtBundle srcPkg tgtPkg ∧
                hsame graph graph' ∧ hsame invGraph invGraph' ∧ hsame comp comp' ∧
                  hsame action action' ∧ hsame ledger ledger' := by
  intro carrier sameSrc sameTgt srcPkg' tgtPkg' graphCont' invGraphCont' compCont'
    actionCont' ledgerCont'
  have transported :=
    PermutationBijectionSourceRow_endpoint_package_hsame_transport carrier.left sameSrc sameTgt
      srcPkg' tgtPkg' graphCont' invGraphCont' compCont' actionCont' ledgerCont'
  have groupCarrier' : GroupSingletonCarrier comp' :=
    hsame_trans (hsame_symm transported.right.right.right.left) carrier.right
  exact And.intro
    (And.intro transported.left groupCarrier')
    transported.right

end BEDC.Derived.SymGroupUp
