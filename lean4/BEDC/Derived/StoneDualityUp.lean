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

end BEDC.Derived.StoneDualityUp
