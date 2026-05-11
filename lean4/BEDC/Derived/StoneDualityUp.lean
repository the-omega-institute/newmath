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

theorem StoneDualityContinuousMapReadback_transport [AskSetup] [PackageSetup]
    {targetBoolean targetBoolean' targetClopen targetClopen' sourceBoolean sourceBoolean'
      sourceClopen sourceClopen' morphism morphism' readback readback' ledger ledger'
      endpoint endpoint' : BHist} :
    hsame targetBoolean targetBoolean' ->
      hsame targetClopen targetClopen' ->
        hsame sourceBoolean sourceBoolean' ->
          hsame sourceClopen sourceClopen' ->
            hsame morphism morphism' ->
              Cont morphism targetBoolean sourceBoolean ->
                Cont morphism' targetBoolean' sourceBoolean' ->
                  Cont sourceBoolean sourceClopen readback ->
                    Cont sourceBoolean' sourceClopen' readback' ->
                      Cont targetClopen readback ledger ->
                        Cont targetClopen' readback' ledger' ->
                          Cont ledger morphism endpoint ->
                            Cont ledger' morphism' endpoint' ->
                              hsame endpoint endpoint' := by
  intro sameTargetBoolean sameTargetClopen sameSourceBoolean sameSourceClopen sameMorphism
    morphismRow morphismRow' readbackRow readbackRow' ledgerRow ledgerRow' endpointRow
    endpointRow'
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame sameSourceBoolean sameSourceClopen readbackRow readbackRow'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameTargetClopen sameReadback ledgerRow ledgerRow'
  exact cont_respects_hsame sameLedger sameMorphism endpointRow endpointRow'

end BEDC.Derived.StoneDualityUp
