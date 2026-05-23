import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyFamilyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyFamilyCarrier_modulus_window_exactness [AskSetup] [PackageSetup]
    {memberLedger memberRow modulus streamWindow dyadicLedger diagonalRoute provenance
      localCert selectedMember selectedWindow observation completionRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory memberLedger ->
      UnaryHistory memberRow ->
        UnaryHistory modulus ->
          UnaryHistory streamWindow ->
            UnaryHistory dyadicLedger ->
              UnaryHistory diagonalRoute ->
                Cont modulus memberRow selectedMember ->
                  Cont selectedMember streamWindow selectedWindow ->
                    Cont selectedWindow dyadicLedger observation ->
                      Cont observation diagonalRoute completionRoute ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle localCert pkg ->
                            PkgSig bundle completionRoute pkg ->
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row completionRoute ∧ UnaryHistory row ∧
                                    PkgSig bundle row pkg)
                                (fun row : BHist =>
                                  Cont observation diagonalRoute row ∧ PkgSig bundle row pkg)
                                (fun _row : BHist =>
                                  UnaryHistory memberLedger ∧ UnaryHistory modulus ∧
                                    UnaryHistory streamWindow ∧ UnaryHistory dyadicLedger ∧
                                      UnaryHistory diagonalRoute ∧
                                        Cont modulus memberRow selectedMember ∧
                                          Cont selectedMember streamWindow selectedWindow ∧
                                            Cont selectedWindow dyadicLedger observation ∧
                                              PkgSig bundle provenance pkg ∧
                                                PkgSig bundle localCert pkg)
                                hsame := by
  intro memberLedgerUnary memberRowUnary modulusUnary streamWindowUnary dyadicLedgerUnary
  intro diagonalRouteUnary modulusMemberSelected selectedMemberWindow selectedWindowLedger
  intro observationDiagonalCompletion provenancePkg localCertPkg completionRoutePkg
  have selectedMemberUnary : UnaryHistory selectedMember :=
    unary_cont_closed modulusUnary memberRowUnary modulusMemberSelected
  have selectedWindowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed selectedMemberUnary streamWindowUnary selectedMemberWindow
  have observationUnary : UnaryHistory observation :=
    unary_cont_closed selectedWindowUnary dyadicLedgerUnary selectedWindowLedger
  have completionRouteUnary : UnaryHistory completionRoute :=
    unary_cont_closed observationUnary diagonalRouteUnary observationDiagonalCompletion
  have sourceCompletion :
      hsame completionRoute completionRoute ∧ UnaryHistory completionRoute ∧
        PkgSig bundle completionRoute pkg :=
    ⟨hsame_refl completionRoute, completionRouteUnary, completionRoutePkg⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro completionRoute sourceCompletion
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro row row' classified sourceRow
        exact
          ⟨hsame_trans (hsame_symm classified) sourceRow.left,
            unary_transport sourceRow.right.left classified,
            by
              cases classified
              exact sourceRow.right.right⟩
    }
    pattern_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨observationDiagonalCompletion, sourceRow.right.right⟩
    ledger_sound := by
      intro _row _sourceRow
      exact
        ⟨memberLedgerUnary, modulusUnary, streamWindowUnary, dyadicLedgerUnary,
          diagonalRouteUnary, modulusMemberSelected, selectedMemberWindow,
          selectedWindowLedger, provenancePkg, localCertPkg⟩
  }

def RegularCauchyFamilyCarrier [AskSetup] [PackageSetup]
    (memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory memberLedger ∧ UnaryHistory memberRows ∧ UnaryHistory modulus ∧
    UnaryHistory windows ∧ UnaryHistory dyadicLedger ∧ UnaryHistory diagonalRoute ∧
      UnaryHistory transports ∧ UnaryHistory contRoutes ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont memberLedger memberRows modulus ∧
          Cont modulus windows dyadicLedger ∧ Cont dyadicLedger diagonalRoute contRoutes ∧
            Cont transports contRoutes provenance ∧ PkgSig bundle provenance pkg

theorem RegularCauchyFamilyCarrier_carrier_transport_stability [AskSetup] [PackageSetup]
    {memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert memberLedger' memberRows' modulus' windows' dyadicLedger'
      diagonalRoute' transports' contRoutes' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg ->
      hsame memberLedger memberLedger' ->
        hsame memberRows memberRows' ->
          hsame windows windows' ->
            hsame transports transports' ->
              hsame localCert localCert' ->
                hsame diagonalRoute diagonalRoute' ->
                  Cont memberLedger' memberRows' modulus' ->
                    Cont modulus' windows' dyadicLedger' ->
                      Cont dyadicLedger' diagonalRoute' contRoutes' ->
                        Cont transports' contRoutes' provenance' ->
                          PkgSig bundle provenance' pkg ->
                            RegularCauchyFamilyCarrier memberLedger' memberRows' modulus' windows'
                                dyadicLedger' diagonalRoute' transports' contRoutes' provenance'
                                localCert' bundle pkg ∧
                              hsame modulus modulus' ∧ hsame dyadicLedger dyadicLedger' ∧
                                hsame diagonalRoute diagonalRoute' ∧
                                  hsame contRoutes contRoutes' ∧
                                    hsame provenance provenance' := by
  intro carrier sameMemberLedger sameMemberRows sameWindows sameTransports sameLocalCert
    sameDiagonal memberRoute' windowRoute' diagonalRouteRow' provenanceRoute' provenancePkg'
  obtain ⟨memberLedgerUnary, memberRowsUnary, modulusUnary, windowsUnary, dyadicLedgerUnary,
    diagonalRouteUnary, transportsUnary, contRoutesUnary, provenanceUnary, localCertUnary,
    memberRoute, windowRoute, diagonalRouteRow, provenanceRoute, _provenancePkg⟩ := carrier
  have sameModulus : hsame modulus modulus' :=
    cont_respects_hsame sameMemberLedger sameMemberRows memberRoute memberRoute'
  have sameDyadicLedger : hsame dyadicLedger dyadicLedger' :=
    cont_respects_hsame sameModulus sameWindows windowRoute windowRoute'
  have sameContRoutes : hsame contRoutes contRoutes' :=
    cont_respects_hsame sameDyadicLedger sameDiagonal diagonalRouteRow diagonalRouteRow'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransports sameContRoutes provenanceRoute provenanceRoute'
  have transported :
      RegularCauchyFamilyCarrier memberLedger' memberRows' modulus' windows'
        dyadicLedger' diagonalRoute' transports' contRoutes' provenance' localCert' bundle pkg :=
    ⟨unary_transport memberLedgerUnary sameMemberLedger,
      unary_transport memberRowsUnary sameMemberRows,
      unary_transport modulusUnary sameModulus,
      unary_transport windowsUnary sameWindows,
      unary_transport dyadicLedgerUnary sameDyadicLedger,
      unary_transport diagonalRouteUnary sameDiagonal,
      unary_transport transportsUnary sameTransports,
      unary_transport contRoutesUnary sameContRoutes,
      unary_transport provenanceUnary sameProvenance,
      unary_transport localCertUnary sameLocalCert,
      memberRoute',
      windowRoute',
      diagonalRouteRow',
      provenanceRoute',
      provenancePkg'⟩
  exact
    ⟨transported, sameModulus, sameDyadicLedger, sameDiagonal, sameContRoutes, sameProvenance⟩

theorem RegularCauchyFamilyCarrier_transport_stability [AskSetup] [PackageSetup]
    {memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert memberLedger' memberRows' modulus' windows' dyadicLedger'
      diagonalRoute' transports' contRoutes' provenance' localCert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg ->
      hsame memberLedger memberLedger' ->
        hsame memberRows memberRows' ->
          hsame modulus modulus' ->
            hsame windows windows' ->
              hsame dyadicLedger dyadicLedger' ->
                hsame diagonalRoute diagonalRoute' ->
                  hsame transports transports' ->
                    hsame contRoutes contRoutes' ->
                      hsame provenance provenance' ->
                        hsame localCert localCert' ->
                          Cont memberLedger' memberRows' modulus' ->
                            Cont modulus' windows' dyadicLedger' ->
                              Cont dyadicLedger' diagonalRoute' contRoutes' ->
                                Cont transports' contRoutes' provenance' ->
                                  PkgSig bundle provenance' pkg ->
                                    RegularCauchyFamilyCarrier memberLedger' memberRows'
                                      modulus' windows' dyadicLedger' diagonalRoute'
                                      transports' contRoutes' provenance' localCert'
                                      bundle pkg := by
  intro carrier sameMemberLedger sameMemberRows sameModulus sameWindows sameDyadicLedger
    sameDiagonalRoute sameTransports sameContRoutes sameProvenance sameLocalCert
    memberRoute' windowRoute' diagonalRouteRow' provenanceRoute' provenancePkg'
  obtain ⟨memberLedgerUnary, memberRowsUnary, modulusUnary, windowsUnary,
    dyadicLedgerUnary, diagonalRouteUnary, transportsUnary, contRoutesUnary,
    provenanceUnary, localCertUnary, _memberRoute, _windowRoute, _diagonalRouteRow,
    _provenanceRoute, _provenancePkg⟩ := carrier
  exact
    ⟨unary_transport memberLedgerUnary sameMemberLedger,
      unary_transport memberRowsUnary sameMemberRows,
      unary_transport modulusUnary sameModulus,
      unary_transport windowsUnary sameWindows,
      unary_transport dyadicLedgerUnary sameDyadicLedger,
      unary_transport diagonalRouteUnary sameDiagonalRoute,
      unary_transport transportsUnary sameTransports,
      unary_transport contRoutesUnary sameContRoutes,
      unary_transport provenanceUnary sameProvenance,
      unary_transport localCertUnary sameLocalCert,
      memberRoute', windowRoute', diagonalRouteRow', provenanceRoute', provenancePkg'⟩

theorem RegularCauchyFamilyCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row provenance ∧
            RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
              diagonalRoute transports contRoutes provenance localCert bundle pkg)
        (fun _row : BHist =>
          UnaryHistory memberLedger ∧ UnaryHistory memberRows ∧ UnaryHistory modulus ∧
            Cont memberLedger memberRows modulus ∧ Cont modulus windows dyadicLedger ∧
              Cont dyadicLedger diagonalRoute contRoutes)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
        hsame := by
  intro carrier
  have carrierData :
      RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg :=
    carrier
  obtain ⟨memberLedgerUnary, memberRowsUnary, modulusUnary, _windowsUnary,
    _dyadicLedgerUnary, _diagonalRouteUnary, _transportsUnary, _contRoutesUnary,
    provenanceUnary, _localCertUnary, memberRoute, windowRoute, diagonalRouteRow,
    _provenanceRoute, provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro provenance ⟨hsame_refl provenance, carrierData⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row _sourceRow
      exact
        ⟨memberLedgerUnary, memberRowsUnary, modulusUnary, memberRoute, windowRoute,
          diagonalRouteRow⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨provenancePkg, unary_transport provenanceUnary (hsame_symm sourceRow.left)⟩
  }

theorem RegularCauchyFamilyCarrier_diagonal_handoff [AskSetup] [PackageSetup]
    {memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert selectedMember diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg ->
      Cont modulus windows selectedMember ->
        Cont selectedMember diagonalRoute diagonalRead ->
          PkgSig bundle diagonalRead pkg ->
            UnaryHistory memberLedger ∧ UnaryHistory memberRows ∧ UnaryHistory modulus ∧
              UnaryHistory windows ∧ UnaryHistory selectedMember ∧
                UnaryHistory diagonalRead ∧ Cont memberLedger memberRows modulus ∧
                  Cont modulus windows dyadicLedger ∧ Cont modulus windows selectedMember ∧
                    Cont selectedMember diagonalRoute diagonalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle diagonalRead pkg := by
  intro carrier selectedMemberRoute diagonalReadRoute diagonalReadPkg
  obtain ⟨memberLedgerUnary, memberRowsUnary, modulusUnary, windowsUnary,
    _dyadicLedgerUnary, diagonalRouteUnary, _transportsUnary, _contRoutesUnary,
    _provenanceUnary, _localCertUnary, memberRowsRoute, dyadicLedgerRoute,
    _contRoutesRoute, _provenanceRoute, provenancePkg⟩ := carrier
  have selectedMemberUnary : UnaryHistory selectedMember :=
    unary_cont_closed modulusUnary windowsUnary selectedMemberRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed selectedMemberUnary diagonalRouteUnary diagonalReadRoute
  exact
    ⟨memberLedgerUnary, memberRowsUnary, modulusUnary, windowsUnary, selectedMemberUnary,
      diagonalReadUnary, memberRowsRoute, dyadicLedgerRoute, selectedMemberRoute,
      diagonalReadRoute, provenancePkg, diagonalReadPkg⟩

theorem RegularCauchyFamilyCarrier_member_selection_determinacy [AskSetup] [PackageSetup]
    {memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert selectedMember selectedMember' diagonalRead diagonalRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg ->
      Cont modulus windows selectedMember ->
        Cont modulus windows selectedMember' ->
          Cont selectedMember diagonalRoute diagonalRead ->
            Cont selectedMember' diagonalRoute diagonalRead' ->
              PkgSig bundle diagonalRead pkg ->
                PkgSig bundle diagonalRead' pkg ->
                  hsame selectedMember selectedMember' ∧ hsame diagonalRead diagonalRead' ∧
                    UnaryHistory selectedMember ∧ UnaryHistory selectedMember' ∧
                      UnaryHistory diagonalRead ∧ UnaryHistory diagonalRead' ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle diagonalRead pkg ∧
                          PkgSig bundle diagonalRead' pkg := by
  intro carrier selectedRoute selectedRoute' diagonalRouteRead diagonalRouteRead'
    diagonalReadPkg diagonalReadPkg'
  obtain ⟨_memberLedgerUnary, _memberRowsUnary, modulusUnary, windowsUnary,
    _dyadicLedgerUnary, diagonalRouteUnary, _transportsUnary, _contRoutesUnary,
    _provenanceUnary, _localCertUnary, _memberRoute, _windowRoute, _contRoutesRoute,
    _provenanceRoute, provenancePkg⟩ := carrier
  have sameSelected : hsame selectedMember selectedMember' :=
    cont_deterministic selectedRoute selectedRoute'
  have sameDiagonal : hsame diagonalRead diagonalRead' :=
    cont_respects_hsame sameSelected (hsame_refl diagonalRoute) diagonalRouteRead
      diagonalRouteRead'
  have selectedUnary : UnaryHistory selectedMember :=
    unary_cont_closed modulusUnary windowsUnary selectedRoute
  have selectedUnary' : UnaryHistory selectedMember' :=
    unary_cont_closed modulusUnary windowsUnary selectedRoute'
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed selectedUnary diagonalRouteUnary diagonalRouteRead
  have diagonalUnary' : UnaryHistory diagonalRead' :=
    unary_cont_closed selectedUnary' diagonalRouteUnary diagonalRouteRead'
  exact
    ⟨sameSelected, sameDiagonal, selectedUnary, selectedUnary', diagonalUnary,
      diagonalUnary', provenancePkg, diagonalReadPkg, diagonalReadPkg'⟩

theorem RegularCauchyFamily_standard_bridge_boundary [AskSetup] [PackageSetup]
    {memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert selectedMember diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg ->
      Cont modulus windows selectedMember ->
        Cont selectedMember diagonalRoute diagonalRead ->
          PkgSig bundle diagonalRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  hsame row provenance ∧
                    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows
                      dyadicLedger diagonalRoute transports contRoutes provenance localCert
                      bundle pkg)
                (fun _row : BHist =>
                  UnaryHistory memberLedger ∧ UnaryHistory memberRows ∧ UnaryHistory modulus ∧
                    Cont memberLedger memberRows modulus ∧ Cont modulus windows dyadicLedger ∧
                      Cont dyadicLedger diagonalRoute contRoutes)
                (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row) hsame ∧
              UnaryHistory selectedMember ∧ UnaryHistory diagonalRead ∧
                Cont modulus windows selectedMember ∧
                  Cont selectedMember diagonalRoute diagonalRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle diagonalRead pkg := by
  intro carrier selectedMemberRoute diagonalReadRoute diagonalReadPkg
  have certificate :=
    RegularCauchyFamilyCarrier_namecert_obligation_surface carrier
  have handoff :=
    RegularCauchyFamilyCarrier_diagonal_handoff carrier selectedMemberRoute diagonalReadRoute
      diagonalReadPkg
  obtain ⟨_memberLedgerUnary, _memberRowsUnary, _modulusUnary, _windowsUnary,
    selectedMemberUnary, diagonalReadUnary, _memberRowsRoute, _dyadicLedgerRoute,
    selectedMemberRoute', diagonalReadRoute', provenancePkg, diagonalReadPkg'⟩ := handoff
  exact
    ⟨certificate, selectedMemberUnary, diagonalReadUnary, selectedMemberRoute',
      diagonalReadRoute', provenancePkg, diagonalReadPkg'⟩

theorem RegularCauchyFamily_completion_consumer_factorization [AskSetup] [PackageSetup]
    {memberLedger memberRows modulus windows dyadicLedger diagonalRoute transports contRoutes
      provenance localCert selectedMember diagonalRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyFamilyCarrier memberLedger memberRows modulus windows dyadicLedger
        diagonalRoute transports contRoutes provenance localCert bundle pkg ->
      Cont modulus windows selectedMember ->
        Cont selectedMember diagonalRoute diagonalRead ->
          Cont diagonalRead provenance terminalRead ->
            PkgSig bundle terminalRead pkg ->
              UnaryHistory selectedMember ∧ UnaryHistory diagonalRead ∧
                UnaryHistory terminalRead ∧ Cont modulus windows selectedMember ∧
                  Cont selectedMember diagonalRoute diagonalRead ∧
                    Cont diagonalRead provenance terminalRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier selectedMemberRoute diagonalReadRoute terminalReadRoute terminalPkg
  obtain ⟨_memberLedgerUnary, _memberRowsUnary, modulusUnary, windowsUnary,
    _dyadicLedgerUnary, diagonalRouteUnary, _transportsUnary, _contRoutesUnary,
    provenanceUnary, _localCertUnary, _memberRowsRoute, _dyadicLedgerRoute,
    _contRoutesRoute, _provenanceRoute, provenancePkg⟩ := carrier
  have selectedMemberUnary : UnaryHistory selectedMember :=
    unary_cont_closed modulusUnary windowsUnary selectedMemberRoute
  have diagonalReadUnary : UnaryHistory diagonalRead :=
    unary_cont_closed selectedMemberUnary diagonalRouteUnary diagonalReadRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed diagonalReadUnary provenanceUnary terminalReadRoute
  exact
    ⟨selectedMemberUnary, diagonalReadUnary, terminalReadUnary, selectedMemberRoute,
      diagonalReadRoute, terminalReadRoute, provenancePkg, terminalPkg⟩

end BEDC.Derived.RegularCauchyFamilyUp
