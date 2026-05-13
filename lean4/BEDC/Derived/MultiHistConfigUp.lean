import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MultiHistConfigUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MultiHistConfigCarrier [AskSetup] [PackageSetup]
    (h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory h0 ∧ UnaryHistory h1 ∧ UnaryHistory noSync ∧ UnaryHistory route ∧
    UnaryHistory localCert ∧ Cont h0 h1 ledger0 ∧ Cont ledger0 noSync sameRow ∧
      Cont sameRow route provenance ∧ Cont provenance localCert ledger1 ∧
        PkgSig bundle provenance pkg

def MultiHistConfigVisibleRow
    (h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert row : BHist) : Prop :=
  hsame row h0 ∨ hsame row h1 ∨ hsame row ledger0 ∨ hsame row ledger1 ∨
    hsame row noSync ∨ hsame row sameRow ∨ hsame row route ∨ hsame row provenance ∨
      hsame row localCert

theorem MultiHistConfigCarrier_habitation [AskSetup] [PackageSetup]
    {h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory h0 ->
      UnaryHistory h1 ->
        UnaryHistory noSync ->
          UnaryHistory route ->
            UnaryHistory localCert ->
              Cont h0 h1 ledger0 ->
                Cont ledger0 noSync sameRow ->
                  Cont sameRow route provenance ->
                    Cont provenance localCert ledger1 ->
                      PkgSig bundle provenance pkg ->
                        MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route
                            provenance localCert bundle pkg ∧
                          UnaryHistory ledger0 ∧ UnaryHistory sameRow ∧
                            UnaryHistory provenance ∧ UnaryHistory ledger1 := by
  intro h0Unary h1Unary noSyncUnary routeUnary localCertUnary h0H1Ledger
    ledgerNoSyncSame sameRouteProvenance provenanceLocalLedger pkgSig
  have ledger0Unary : UnaryHistory ledger0 :=
    unary_cont_closed h0Unary h1Unary h0H1Ledger
  have sameRowUnary : UnaryHistory sameRow :=
    unary_cont_closed ledger0Unary noSyncUnary ledgerNoSyncSame
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed sameRowUnary routeUnary sameRouteProvenance
  have ledger1Unary : UnaryHistory ledger1 :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalLedger
  have carrier :
      MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert
          bundle pkg :=
    ⟨h0Unary, h1Unary, noSyncUnary, routeUnary, localCertUnary, h0H1Ledger,
      ledgerNoSyncSame, sameRouteProvenance, provenanceLocalLedger, pkgSig⟩
  exact ⟨carrier, ledger0Unary, sameRowUnary, provenanceUnary, ledger1Unary⟩

theorem MultiHistConfigCarrier_componentwise_classifier_stability [AskSetup] [PackageSetup]
    {h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert h0' h1' ledger0'
      ledger1' sameRow' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert
        bundle pkg ->
      hsame h0 h0' ->
        hsame h1 h1' ->
          Cont h0' h1' ledger0' ->
            Cont ledger0' noSync sameRow' ->
              Cont sameRow' route provenance' ->
                Cont provenance' localCert ledger1' ->
                  PkgSig bundle provenance' pkg ->
                    MultiHistConfigCarrier h0' h1' ledger0' ledger1' noSync sameRow' route
                        provenance' localCert bundle pkg ∧
                      hsame ledger0 ledger0' ∧ hsame sameRow sameRow' ∧
                        hsame provenance provenance' ∧ hsame ledger1 ledger1' := by
  intro carrier sameH0 sameH1 targetH0H1 targetLedgerNoSync targetSameRoute
    targetProvenanceLocal targetPkgSig
  have sourceH0Unary : UnaryHistory h0 := carrier.left
  have sourceH1Unary : UnaryHistory h1 := carrier.right.left
  have sourceNoSyncUnary : UnaryHistory noSync := carrier.right.right.left
  have sourceRouteUnary : UnaryHistory route := carrier.right.right.right.left
  have sourceLocalCertUnary : UnaryHistory localCert := carrier.right.right.right.right.left
  have sourceH0H1 : Cont h0 h1 ledger0 := carrier.right.right.right.right.right.left
  have sourceLedgerNoSync : Cont ledger0 noSync sameRow :=
    carrier.right.right.right.right.right.right.left
  have sourceSameRoute : Cont sameRow route provenance :=
    carrier.right.right.right.right.right.right.right.left
  have sourceProvenanceLocal : Cont provenance localCert ledger1 :=
    carrier.right.right.right.right.right.right.right.right.left
  have targetH0Unary : UnaryHistory h0' :=
    unary_transport sourceH0Unary sameH0
  have targetH1Unary : UnaryHistory h1' :=
    unary_transport sourceH1Unary sameH1
  have sameLedger0 : hsame ledger0 ledger0' :=
    cont_respects_hsame sameH0 sameH1 sourceH0H1 targetH0H1
  have sameSameRow : hsame sameRow sameRow' :=
    cont_respects_hsame sameLedger0 (hsame_refl noSync) sourceLedgerNoSync
      targetLedgerNoSync
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameSameRow (hsame_refl route) sourceSameRoute targetSameRoute
  have sameLedger1 : hsame ledger1 ledger1' :=
    cont_respects_hsame sameProvenance (hsame_refl localCert) sourceProvenanceLocal
      targetProvenanceLocal
  exact
    ⟨⟨targetH0Unary, targetH1Unary, sourceNoSyncUnary, sourceRouteUnary,
        sourceLocalCertUnary, targetH0H1, targetLedgerNoSync, targetSameRoute,
        targetProvenanceLocal, targetPkgSig⟩,
      sameLedger0, sameSameRow, sameProvenance, sameLedger1⟩

theorem MultiHistConfigCarrier_no_global_sync_ledger [AskSetup] [PackageSetup]
    {h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert noSync' sameRow'
      provenance' ledger1' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert
        bundle pkg ->
      hsame noSync noSync' ->
        Cont ledger0 noSync' sameRow' ->
          Cont sameRow' route provenance' ->
            Cont provenance' localCert ledger1' ->
              PkgSig bundle provenance' pkg ->
                MultiHistConfigCarrier h0 h1 ledger0 ledger1' noSync' sameRow' route
                    provenance' localCert bundle pkg ∧
                  hsame sameRow sameRow' ∧ hsame provenance provenance' ∧
                    hsame ledger1 ledger1' := by
  intro carrier sameNoSync targetLedgerNoSync targetSameRoute targetProvenanceLocal
    targetPkgSig
  have sourceH0Unary : UnaryHistory h0 := carrier.left
  have sourceH1Unary : UnaryHistory h1 := carrier.right.left
  have sourceNoSyncUnary : UnaryHistory noSync := carrier.right.right.left
  have sourceRouteUnary : UnaryHistory route := carrier.right.right.right.left
  have sourceLocalCertUnary : UnaryHistory localCert := carrier.right.right.right.right.left
  have sourceLedger0 : Cont h0 h1 ledger0 := carrier.right.right.right.right.right.left
  have sourceLedgerNoSync : Cont ledger0 noSync sameRow :=
    carrier.right.right.right.right.right.right.left
  have sourceSameRoute : Cont sameRow route provenance :=
    carrier.right.right.right.right.right.right.right.left
  have sourceProvenanceLocal : Cont provenance localCert ledger1 :=
    carrier.right.right.right.right.right.right.right.right.left
  have targetNoSyncUnary : UnaryHistory noSync' :=
    unary_transport sourceNoSyncUnary sameNoSync
  have sameSameRow : hsame sameRow sameRow' :=
    cont_respects_hsame (hsame_refl ledger0) sameNoSync sourceLedgerNoSync
      targetLedgerNoSync
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameSameRow (hsame_refl route) sourceSameRoute targetSameRoute
  have sameLedger1 : hsame ledger1 ledger1' :=
    cont_respects_hsame sameProvenance (hsame_refl localCert) sourceProvenanceLocal
      targetProvenanceLocal
  exact
    ⟨⟨sourceH0Unary, sourceH1Unary, targetNoSyncUnary, sourceRouteUnary,
        sourceLocalCertUnary, sourceLedger0, targetLedgerNoSync, targetSameRoute,
        targetProvenanceLocal, targetPkgSig⟩,
      sameSameRow, sameProvenance, sameLedger1⟩

theorem MultiHistConfigCarrier_finite_ledger_obligations [AskSetup] [PackageSetup]
    {h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert
        bundle pkg ->
      Cont ledger0 route ledgerRead ->
        UnaryHistory ledgerRead ∧ hsame ledgerRead ledgerRead ∧
          MultiHistConfigVisibleRow h0 h1 ledger0 ledger1 noSync sameRow route provenance
            localCert ledger0 := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory ProbeBundle Pkg
  intro carrier ledgerRouteRead
  obtain ⟨h0Unary, h1Unary, _noSyncUnary, routeUnary, _localCertUnary, h0H1Ledger,
    _ledgerNoSyncSame, _sameRouteProvenance, _provenanceLocalLedger, _pkgSig⟩ := carrier
  have ledger0Unary : UnaryHistory ledger0 :=
    unary_cont_closed h0Unary h1Unary h0H1Ledger
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledger0Unary routeUnary ledgerRouteRead
  exact
    ⟨ledgerReadUnary, hsame_refl ledgerRead,
      Or.inr (Or.inr (Or.inl (hsame_refl ledger0)))⟩

theorem MultiHistConfigCarrier_component_transport_scope [AskSetup] [PackageSetup]
    {h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert h0' h1' ledger0'
      ledger1' noSync' sameRow' provenance' : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert
        bundle pkg ->
      hsame h0 h0' ->
        hsame h1 h1' ->
          hsame noSync noSync' ->
            Cont h0' h1' ledger0' ->
              Cont ledger0' noSync' sameRow' ->
                Cont sameRow' route provenance' ->
                  Cont provenance' localCert ledger1' ->
                    PkgSig bundle provenance' pkg ->
                      MultiHistConfigCarrier h0' h1' ledger0' ledger1' noSync'
                          sameRow' route provenance' localCert bundle pkg ∧
                        hsame ledger0 ledger0' ∧ hsame sameRow sameRow' ∧
                          hsame provenance provenance' ∧ hsame ledger1 ledger1' := by
  intro carrier sameH0 sameH1 sameNoSync targetH0H1 targetLedgerNoSync
    targetSameRoute targetProvenanceLocal targetPkgSig
  have sourceH0Unary : UnaryHistory h0 := carrier.left
  have sourceH1Unary : UnaryHistory h1 := carrier.right.left
  have sourceNoSyncUnary : UnaryHistory noSync := carrier.right.right.left
  have sourceRouteUnary : UnaryHistory route := carrier.right.right.right.left
  have sourceLocalCertUnary : UnaryHistory localCert := carrier.right.right.right.right.left
  have sourceH0H1 : Cont h0 h1 ledger0 := carrier.right.right.right.right.right.left
  have sourceLedgerNoSync : Cont ledger0 noSync sameRow :=
    carrier.right.right.right.right.right.right.left
  have sourceSameRoute : Cont sameRow route provenance :=
    carrier.right.right.right.right.right.right.right.left
  have sourceProvenanceLocal : Cont provenance localCert ledger1 :=
    carrier.right.right.right.right.right.right.right.right.left
  have targetH0Unary : UnaryHistory h0' :=
    unary_transport sourceH0Unary sameH0
  have targetH1Unary : UnaryHistory h1' :=
    unary_transport sourceH1Unary sameH1
  have targetNoSyncUnary : UnaryHistory noSync' :=
    unary_transport sourceNoSyncUnary sameNoSync
  have sameLedger0 : hsame ledger0 ledger0' :=
    cont_respects_hsame sameH0 sameH1 sourceH0H1 targetH0H1
  have sameSameRow : hsame sameRow sameRow' :=
    cont_respects_hsame sameLedger0 sameNoSync sourceLedgerNoSync targetLedgerNoSync
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameSameRow (hsame_refl route) sourceSameRoute targetSameRoute
  have sameLedger1 : hsame ledger1 ledger1' :=
    cont_respects_hsame sameProvenance (hsame_refl localCert) sourceProvenanceLocal
      targetProvenanceLocal
  exact
    ⟨⟨targetH0Unary, targetH1Unary, targetNoSyncUnary, sourceRouteUnary,
        sourceLocalCertUnary, targetH0H1, targetLedgerNoSync, targetSameRoute,
        targetProvenanceLocal, targetPkgSig⟩,
      sameLedger0, sameSameRow, sameProvenance, sameLedger1⟩

theorem MultiHistConfigCarrier_namecert_obligation_package [AskSetup] [PackageSetup]
    {h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance
              localCert bundle pkg ∧
            MultiHistConfigVisibleRow h0 h1 ledger0 ledger1 noSync sameRow route provenance
              localCert row)
        (fun row : BHist =>
          MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance
              localCert bundle pkg ∧
            MultiHistConfigVisibleRow h0 h1 ledger0 ledger1 noSync sameRow route provenance
              localCert row)
        (fun row : BHist =>
          MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance
              localCert bundle pkg ∧
            MultiHistConfigVisibleRow h0 h1 ledger0 ledger1 noSync sameRow route provenance
              localCert row)
        hsame := by
  intro carrier
  constructor
  · constructor
    · exact Exists.intro h0 (And.intro carrier (Or.inl (hsame_refl h0)))
    · intro row _source
      exact hsame_refl row
    · intro row row' sameRowRow'
      exact hsame_symm sameRowRow'
    · intro row row' row'' sameRowRow' sameRow'Row''
      exact hsame_trans sameRowRow' sameRow'Row''
    · intro row row' sameRowRow' source
      cases sameRowRow'
      exact source
  · intro _row source
    exact source
  · intro _row source
    exact source

theorem MultiHistConfigCarrier_consumer_projection_boundary [AskSetup] [PackageSetup]
    {h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert projection : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MultiHistConfigCarrier h0 h1 ledger0 ledger1 noSync sameRow route provenance localCert
        bundle pkg ->
      Cont ledger1 route projection ->
        UnaryHistory h0 ∧ UnaryHistory h1 ∧ UnaryHistory ledger0 ∧ UnaryHistory sameRow ∧
          UnaryHistory provenance ∧ UnaryHistory ledger1 ∧ UnaryHistory projection ∧
            Cont h0 h1 ledger0 ∧ Cont provenance localCert ledger1 ∧
              Cont ledger1 route projection ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier ledgerProjection
  obtain ⟨h0Unary, h1Unary, noSyncUnary, routeUnary, localCertUnary, h0H1Ledger,
    ledgerNoSyncSame, sameRouteProvenance, provenanceLocalLedger, provenancePkg⟩ := carrier
  have ledger0Unary : UnaryHistory ledger0 :=
    unary_cont_closed h0Unary h1Unary h0H1Ledger
  have sameRowUnary : UnaryHistory sameRow :=
    unary_cont_closed ledger0Unary noSyncUnary ledgerNoSyncSame
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed sameRowUnary routeUnary sameRouteProvenance
  have ledger1Unary : UnaryHistory ledger1 :=
    unary_cont_closed provenanceUnary localCertUnary provenanceLocalLedger
  have projectionUnary : UnaryHistory projection :=
    unary_cont_closed ledger1Unary routeUnary ledgerProjection
  exact
    ⟨h0Unary, h1Unary, ledger0Unary, sameRowUnary, provenanceUnary, ledger1Unary,
      projectionUnary, h0H1Ledger, provenanceLocalLedger, ledgerProjection, provenancePkg⟩

theorem MultiHistConfig_carrier_habitation (h0 h1 : BHist) :
    (Cont h0 BHist.Empty h0 ∧ Cont h1 BHist.Empty h1) ∧
      BEDC.FKernel.NameCert.NameCert
        (fun h : BHist => hsame h h0 ∨ hsame h h1) hsame := by
  constructor
  · constructor
    · exact cont_right_unit h0
    · exact cont_right_unit h1
  · exact {
      carrier_inhabited := Exists.intro h0 (Or.inl (hsame_refl h0))
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro h k sameHK
        exact hsame_symm sameHK
      equiv_trans := by
        intro a b c sameAB sameBC
        exact hsame_trans sameAB sameBC
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        cases sameHK
        exact carrierH
    }

end BEDC.Derived.MultiHistConfigUp
