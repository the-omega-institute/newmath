import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StoneDualityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem StoneDualityClopenPacket_boolean_source_readback [AskSetup] [PackageSetup]
    {zero one meet join compl distributive source pkgRow clopenZero clopenOps
      clopenEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoneDualityBooleanSource zero one meet join compl distributive source pkgRow bundle pkg ->
      Cont zero one clopenZero ->
        Cont meet join clopenOps ->
          Cont clopenZero clopenOps clopenEndpoint ->
            UnaryHistory clopenZero ∧ UnaryHistory clopenOps ∧
              UnaryHistory clopenEndpoint ∧ hsame clopenZero (append zero one) ∧
                hsame clopenOps (append meet join) ∧
                  hsame clopenEndpoint (append clopenZero clopenOps) ∧
                    PkgSig bundle pkgRow pkg := by
  intro sourceData clopenZeroRow clopenOpsRow clopenEndpointRow
  have zeroUnary : UnaryHistory zero := sourceData.left
  have oneUnary : UnaryHistory one := sourceData.right.left
  have meetUnary : UnaryHistory meet := sourceData.right.right.left
  have joinUnary : UnaryHistory join := sourceData.right.right.right.left
  have pkgSig : PkgSig bundle pkgRow pkg :=
    sourceData.right.right.right.right.right.right.right.right.right
  have clopenZeroUnary : UnaryHistory clopenZero :=
    unary_cont_closed zeroUnary oneUnary clopenZeroRow
  have clopenOpsUnary : UnaryHistory clopenOps :=
    unary_cont_closed meetUnary joinUnary clopenOpsRow
  have clopenEndpointUnary : UnaryHistory clopenEndpoint :=
    unary_cont_closed clopenZeroUnary clopenOpsUnary clopenEndpointRow
  exact And.intro clopenZeroUnary
    (And.intro clopenOpsUnary
      (And.intro clopenEndpointUnary
        (And.intro clopenZeroRow
          (And.intro clopenOpsRow (And.intro clopenEndpointRow pkgSig)))))

theorem StoneDualityStoneSpaceClassifier_clopen_transport [AskSetup] [PackageSetup]
    {zero one meet join compl distributive source pkgRow clopen clopen' ledger ledger' endpoint
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoneDualityBooleanSource zero one meet join compl distributive source pkgRow bundle pkg ->
      Cont source clopen ledger ->
        Cont source clopen' ledger' ->
          Cont ledger pkgRow endpoint ->
            Cont ledger' pkgRow endpoint' ->
              hsame clopen clopen' -> hsame ledger ledger' ∧ hsame endpoint endpoint' := by
  intro _sourceData sourceClopen sourceClopen' ledgerEndpoint ledgerEndpoint' sameClopen
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame (hsame_refl source) sameClopen sourceClopen sourceClopen'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameLedger (hsame_refl pkgRow) ledgerEndpoint ledgerEndpoint'
  exact And.intro sameLedger sameEndpoint

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

theorem StoneDualityUltrafilterFreeSoundness_surface [AskSetup] [PackageSetup]
    {zero one meet join compl distributive source pkgRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StoneDualityBooleanSource zero one meet join compl distributive source pkgRow bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              StoneDualityBooleanSource zero one meet join compl distributive source e bundle
                pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              StoneDualityBooleanSource zero one meet join compl distributive source e bundle
                pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              StoneDualityBooleanSource zero one meet join compl distributive source e bundle
                pkg ∧ hsame row e)
          hsame ∧
        Cont meet join distributive ∧ Cont source compl pkgRow ∧ PkgSig bundle pkgRow pkg := by
  intro sourceData
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro pkgRow (Exists.intro pkgRow (And.intro sourceData (hsame_refl pkgRow)))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' same
          exact hsame_symm same
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' same source
          cases source with
          | intro e data =>
              exact Exists.intro e
                (And.intro data.left (hsame_trans (hsame_symm same) data.right))
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row source
        exact source
    }
  · exact And.intro sourceData.right.right.right.right.right.right.left
      (And.intro sourceData.right.right.right.right.right.right.right.right.left
        sourceData.right.right.right.right.right.right.right.right.right)

theorem StoneDualityUltrafilterFreeSoundness [AskSetup] [PackageSetup]
    {booleanRow clopenRow ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont booleanRow clopenRow ledger -> Cont ledger provenance endpoint ->
      PkgSig bundle endpoint pkg ->
        SemanticNameCert
            (fun row : BHist =>
              exists e : BHist,
                Cont booleanRow clopenRow ledger ∧ Cont ledger provenance e ∧
                  PkgSig bundle e pkg ∧ hsame row e)
            (fun row : BHist =>
              exists e : BHist,
                Cont booleanRow clopenRow ledger ∧ Cont ledger provenance e ∧
                  PkgSig bundle e pkg ∧ hsame row e)
            (fun row : BHist =>
              exists e : BHist,
                Cont booleanRow clopenRow ledger ∧ Cont ledger provenance e ∧
                  PkgSig bundle e pkg ∧ hsame row e)
            hsame ∧
          Cont booleanRow clopenRow ledger ∧ Cont ledger provenance endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro ledgerRow endpointRow pkgRow
  let Carrier : BHist -> Prop :=
    fun row : BHist =>
      exists e : BHist,
        Cont booleanRow clopenRow ledger ∧ Cont ledger provenance e ∧
          PkgSig bundle e pkg ∧ hsame row e
  have endpointCarrier : Carrier endpoint :=
    Exists.intro endpoint
      (And.intro ledgerRow (And.intro endpointRow (And.intro pkgRow (hsame_refl endpoint))))
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointCarrier
      equiv_refl := by
        intro row _rowCarrier
        exact hsame_refl row
      equiv_symm := by
        intro _row _other rowOther
        exact hsame_symm rowOther
      equiv_trans := by
        intro _row _middle _other rowMiddle middleOther
        exact hsame_trans rowMiddle middleOther
      carrier_respects_equiv := by
        intro row _other rowOther rowCarrier
        cases rowCarrier with
        | intro e rowWitness =>
            exact Exists.intro e
              (And.intro rowWitness.left
                (And.intro rowWitness.right.left
                  (And.intro rowWitness.right.right.left
                    (hsame_trans (hsame_symm rowOther) rowWitness.right.right.right))))
    }
    pattern_sound := by
      intro _row rowCarrier
      exact rowCarrier
    ledger_sound := by
      intro _row rowCarrier
      exact rowCarrier
  }
  exact And.intro cert (And.intro ledgerRow (And.intro endpointRow pkgRow))

end BEDC.Derived.StoneDualityUp
