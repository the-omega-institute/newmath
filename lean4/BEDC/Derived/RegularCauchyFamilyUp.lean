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

end BEDC.Derived.RegularCauchyFamilyUp
