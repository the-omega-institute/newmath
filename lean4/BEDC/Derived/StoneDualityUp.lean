import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StoneDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StoneDualityBooleanSource [AskSetup] [PackageSetup]
    (zero one meet join compl distributive source pkgRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory zero ∧ UnaryHistory one ∧ UnaryHistory meet ∧ UnaryHistory join ∧
    UnaryHistory compl ∧ UnaryHistory distributive ∧ Cont meet join distributive ∧
      Cont zero one source ∧ Cont source compl pkgRow ∧ PkgSig bundle pkgRow pkg

theorem StoneDualityBooleanSource_transport [AskSetup] [PackageSetup]
    {zero one meet join compl distributive source pkgRow zero' one' meet' join' compl'
      distributive' source' pkgRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoneDualityBooleanSource zero one meet join compl distributive source pkgRow bundle pkg ->
      hsame zero zero' ->
        hsame one one' ->
          hsame meet meet' ->
            hsame join join' ->
              hsame compl compl' ->
                Cont meet' join' distributive' ->
                  Cont zero' one' source' ->
                    Cont source' compl' pkgRow' ->
                      PkgSig bundle pkgRow' pkg ->
                        StoneDualityBooleanSource zero' one' meet' join' compl' distributive'
                            source' pkgRow' bundle pkg ∧
                          hsame distributive distributive' ∧ hsame source source' ∧
                            hsame pkgRow pkgRow' := by
  intro sourceData sameZero sameOne sameMeet sameJoin sameCompl distributiveRow' sourceRow'
    pkgRowCont' pkgSig'
  have zeroUnary' : UnaryHistory zero' :=
    unary_transport sourceData.left sameZero
  have oneUnary' : UnaryHistory one' :=
    unary_transport sourceData.right.left sameOne
  have meetUnary' : UnaryHistory meet' :=
    unary_transport sourceData.right.right.left sameMeet
  have joinUnary' : UnaryHistory join' :=
    unary_transport sourceData.right.right.right.left sameJoin
  have complUnary' : UnaryHistory compl' :=
    unary_transport sourceData.right.right.right.right.left sameCompl
  have sameDistributive : hsame distributive distributive' :=
    cont_respects_hsame sameMeet sameJoin sourceData.right.right.right.right.right.right.left
      distributiveRow'
  have distributiveUnary' : UnaryHistory distributive' :=
    unary_cont_closed meetUnary' joinUnary' distributiveRow'
  have sameSource : hsame source source' :=
    cont_respects_hsame sameZero sameOne sourceData.right.right.right.right.right.right.right.left
      sourceRow'
  have sourceUnary' : UnaryHistory source' :=
    unary_cont_closed zeroUnary' oneUnary' sourceRow'
  have samePkgRow : hsame pkgRow pkgRow' :=
    cont_respects_hsame sameSource sameCompl
      sourceData.right.right.right.right.right.right.right.right.left pkgRowCont'
  have sourceData' :
      StoneDualityBooleanSource zero' one' meet' join' compl' distributive' source'
        pkgRow' bundle pkg :=
    And.intro zeroUnary'
      (And.intro oneUnary'
        (And.intro meetUnary'
          (And.intro joinUnary'
            (And.intro complUnary'
              (And.intro distributiveUnary'
                (And.intro distributiveRow'
                  (And.intro sourceRow' (And.intro pkgRowCont' pkgSig'))))))))
  exact And.intro sourceData'
    (And.intro sameDistributive (And.intro sameSource samePkgRow))

theorem StoneDualityClopenLedger_transport_closure [AskSetup] [PackageSetup]
    {booleanRow booleanRow' clopenRow clopenRow' ledger ledger' provenance endpoint
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    hsame booleanRow booleanRow' -> hsame clopenRow clopenRow' ->
      Cont booleanRow clopenRow ledger -> Cont booleanRow' clopenRow' ledger' ->
        Cont ledger provenance endpoint -> Cont ledger' provenance endpoint' ->
          PkgSig bundle endpoint pkg -> hsame endpoint endpoint' := by
  intro sameBoolean sameClopen ledgerRow ledgerRow' endpointRow endpointRow' _pkgSig
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameBoolean sameClopen ledgerRow ledgerRow'
  exact cont_respects_hsame sameLedger (hsame_refl provenance) endpointRow endpointRow'

theorem StoneDualityStoneSpaceClassifier_transport [AskSetup] [PackageSetup]
    {zero one meet join compl distributive source pkgRow clopen ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoneDualityBooleanSource zero one meet join compl distributive source pkgRow bundle pkg ->
      Cont source clopen ledger ->
        Cont ledger pkgRow endpoint ->
          PkgSig bundle endpoint pkg ->
            UnaryHistory clopen ->
              UnaryHistory ledger ∧ UnaryHistory endpoint ∧
                hsame ledger (append source clopen) ∧
                  hsame endpoint (append ledger pkgRow) ∧ PkgSig bundle endpoint pkg := by
  intro sourcePacket sourceClopenLedger ledgerPkgEndpoint endpointPkg clopenUnary
  rcases sourcePacket with
    ⟨zeroUnary, oneUnary, _, _, complUnary, _, _, zeroOneSource, sourcePkgRow, _⟩
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed zeroUnary oneUnary zeroOneSource
  have pkgRowUnary : UnaryHistory pkgRow :=
    unary_cont_closed sourceUnary complUnary sourcePkgRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed sourceUnary clopenUnary sourceClopenLedger
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary pkgRowUnary ledgerPkgEndpoint
  exact
    ⟨ledgerUnary, endpointUnary, sourceClopenLedger, ledgerPkgEndpoint, endpointPkg⟩

theorem StoneDualityContinuousMapReadback_cont_transport [AskSetup] [PackageSetup]
    {boolean booleanTarget morph clopenTarget clopenSource preimage ledger ledgerTarget
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont booleanTarget morph boolean ->
      Cont boolean clopenSource preimage ->
        Cont booleanTarget clopenTarget ledgerTarget ->
          Cont preimage ledgerTarget ledger ->
            Cont ledger morph endpoint ->
              PkgSig bundle endpoint pkg ->
                UnaryHistory booleanTarget ->
                  UnaryHistory morph ->
                    UnaryHistory clopenTarget ->
                      UnaryHistory clopenSource ->
                        UnaryHistory ledger ∧ hsame boolean (append booleanTarget morph) ∧
                          hsame preimage (append boolean clopenSource) ∧
                            hsame ledger (append preimage ledgerTarget) ∧
                              hsame endpoint (append ledger morph) ∧
                                PkgSig bundle endpoint pkg := by
  intro booleanTargetMorphism booleanClopenPreimage targetClopenLedger preimageTargetLedger
    ledgerMorphismEndpoint endpointPkg booleanTargetUnary morphUnary clopenTargetUnary
    clopenSourceUnary
  have booleanUnary : UnaryHistory boolean :=
    unary_cont_closed booleanTargetUnary morphUnary booleanTargetMorphism
  have preimageUnary : UnaryHistory preimage :=
    unary_cont_closed booleanUnary clopenSourceUnary booleanClopenPreimage
  have ledgerTargetUnary : UnaryHistory ledgerTarget :=
    unary_cont_closed booleanTargetUnary clopenTargetUnary targetClopenLedger
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed preimageUnary ledgerTargetUnary preimageTargetLedger
  exact
    ⟨ledgerUnary, booleanTargetMorphism, booleanClopenPreimage, preimageTargetLedger,
      ledgerMorphismEndpoint, endpointPkg⟩

end BEDC.Derived.StoneDualityUp
