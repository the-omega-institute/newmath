import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

/-!
# RegularLimitUniquenessUp finite carrier surface.
-/

namespace BEDC.Derived.RegularLimitUniquenessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularLimitUniquenessCarrier [AskSetup] [PackageSetup]
    (family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory family ∧ UnaryHistory diagonalLeft ∧ UnaryHistory diagonalRight ∧
    UnaryHistory threshold ∧ UnaryHistory readbackLeft ∧ UnaryHistory readbackRight ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont family threshold diagonalLeft ∧
          Cont family threshold diagonalRight ∧ Cont diagonalLeft threshold readbackLeft ∧
            Cont diagonalRight threshold readbackRight ∧ Cont readbackLeft threshold sealLeft ∧
              Cont readbackRight threshold sealRight ∧ Cont sealLeft sealRight separated ∧
                Cont separated transport endpoint ∧ Cont route provenance endpoint ∧
                  PkgSig bundle endpoint pkg

theorem RegularLimitUniquenessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
        readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row endpoint ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
        (fun row : BHist => Cont separated transport row ∧ UnaryHistory sealLeft ∧
          UnaryHistory sealRight)
        (fun row : BHist => PkgSig bundle row pkg ∧ Cont route provenance endpoint)
        hsame := by
  intro carrier
  obtain ⟨familyUnary, _diagonalLeftUnary, _diagonalRightUnary, thresholdUnary,
    readbackLeftUnary, readbackRightUnary, transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    _diagonalLeftThresholdReadback, _diagonalRightThresholdReadback,
    readbackLeftThresholdSeal, readbackRightThresholdSeal, sealComparison,
    separatedTransportEndpoint, routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have sealLeftUnary : UnaryHistory sealLeft :=
    unary_cont_closed readbackLeftUnary thresholdUnary readbackLeftThresholdSeal
  have sealRightUnary : UnaryHistory sealRight :=
    unary_cont_closed readbackRightUnary thresholdUnary readbackRightThresholdSeal
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed sealLeftUnary sealRightUnary sealComparison
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separatedUnary transportUnary separatedTransportEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary, endpointPkg⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨separatedTransportEndpoint, sealLeftUnary, sealRightUnary⟩
    ledger_sound := by
      intro _row sourceRow
      cases sourceRow.left
      exact ⟨sourceRow.right.right, routeProvenanceEndpoint⟩
  }

theorem RegularLimitUniquenessCarrier_classifier_determinacy [AskSetup] [PackageSetup]
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint family' diagonalLeft' diagonalRight'
      threshold' readbackLeft' readbackRight' sealLeft' sealRight' separated' transport' route'
      provenance' localCert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
        readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
        bundle pkg ->
      RegularLimitUniquenessCarrier family' diagonalLeft' diagonalRight' threshold' readbackLeft'
          readbackRight' sealLeft' sealRight' separated' transport' route' provenance' localCert'
          endpoint' bundle pkg ->
        hsame separated separated' ->
          hsame transport transport' ->
            hsame endpoint endpoint' ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle endpoint' pkg := by
  intro carrier carrier' sameSeparated sameTransport
  obtain ⟨_familyUnary, _diagonalLeftUnary, _diagonalRightUnary, _thresholdUnary,
    _readbackLeftUnary, _readbackRightUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    _diagonalLeftThresholdReadback, _diagonalRightThresholdReadback,
    _readbackLeftThresholdSeal, _readbackRightThresholdSeal, _sealComparison,
    separatedTransportEndpoint, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_familyUnary', _diagonalLeftUnary', _diagonalRightUnary', _thresholdUnary',
    _readbackLeftUnary', _readbackRightUnary', _transportUnary', _routeUnary',
    _provenanceUnary', _localCertUnary', _familyThresholdDiagonalLeft',
    _familyThresholdDiagonalRight', _diagonalLeftThresholdReadback',
    _diagonalRightThresholdReadback', _readbackLeftThresholdSeal',
    _readbackRightThresholdSeal', _sealComparison', separatedTransportEndpoint',
    _routeProvenanceEndpoint', endpointPkg'⟩ := carrier'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSeparated sameTransport separatedTransportEndpoint
      separatedTransportEndpoint'
  exact ⟨sameEndpoint, endpointPkg, endpointPkg'⟩

theorem RegularLimitUniquenessCarrier_readback_seal_exactness [AskSetup] [PackageSetup]
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
        readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
        bundle pkg ->
      Cont diagonalLeft threshold readbackLeft ∧ Cont diagonalRight threshold readbackRight ∧
        UnaryHistory sealLeft ∧ UnaryHistory sealRight ∧ Cont sealLeft sealRight separated ∧
          Cont separated transport endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨_familyUnary, _diagonalLeftUnary, _diagonalRightUnary, thresholdUnary,
    readbackLeftUnary, readbackRightUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    diagonalLeftThresholdReadback, diagonalRightThresholdReadback,
    readbackLeftThresholdSeal, readbackRightThresholdSeal, sealComparison,
    separatedTransportEndpoint, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have sealLeftUnary : UnaryHistory sealLeft :=
    unary_cont_closed readbackLeftUnary thresholdUnary readbackLeftThresholdSeal
  have sealRightUnary : UnaryHistory sealRight :=
    unary_cont_closed readbackRightUnary thresholdUnary readbackRightThresholdSeal
  exact
    ⟨diagonalLeftThresholdReadback, diagonalRightThresholdReadback, sealLeftUnary,
      sealRightUnary, sealComparison, separatedTransportEndpoint, endpointPkg⟩

theorem RegularLimitUniquenessCarrier_separated_limit_certificate [AskSetup] [PackageSetup]
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
        readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
        bundle pkg ->
      UnaryHistory readbackLeft ∧ UnaryHistory readbackRight ∧ UnaryHistory sealLeft ∧
        UnaryHistory sealRight ∧ UnaryHistory separated ∧
          Cont diagonalLeft threshold readbackLeft ∧
            Cont diagonalRight threshold readbackRight ∧
              Cont readbackLeft threshold sealLeft ∧
                Cont readbackRight threshold sealRight ∧
                  Cont sealLeft sealRight separated ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨_familyUnary, _diagonalLeftUnary, _diagonalRightUnary, thresholdUnary,
    readbackLeftUnary, readbackRightUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    diagonalLeftThresholdReadback, diagonalRightThresholdReadback,
    readbackLeftThresholdSeal, readbackRightThresholdSeal, sealComparison,
    _separatedTransportEndpoint, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  have sealLeftUnary : UnaryHistory sealLeft :=
    unary_cont_closed readbackLeftUnary thresholdUnary readbackLeftThresholdSeal
  have sealRightUnary : UnaryHistory sealRight :=
    unary_cont_closed readbackRightUnary thresholdUnary readbackRightThresholdSeal
  have separatedUnary : UnaryHistory separated :=
    unary_cont_closed sealLeftUnary sealRightUnary sealComparison
  exact ⟨readbackLeftUnary, readbackRightUnary, sealLeftUnary, sealRightUnary, separatedUnary,
    diagonalLeftThresholdReadback, diagonalRightThresholdReadback, readbackLeftThresholdSeal,
    readbackRightThresholdSeal, sealComparison, endpointPkg⟩

theorem RegularLimitUniquenessCarrier_separated_transport [AskSetup] [PackageSetup]
    {family diagonalLeft diagonalRight threshold readbackLeft readbackRight sealLeft sealRight
      separated transport route provenance localCert endpoint family' diagonalLeft' diagonalRight'
      threshold' readbackLeft' readbackRight' sealLeft' sealRight' separated' transport' route'
      provenance' localCert' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularLimitUniquenessCarrier family diagonalLeft diagonalRight threshold readbackLeft
        readbackRight sealLeft sealRight separated transport route provenance localCert endpoint
        bundle pkg ->
      RegularLimitUniquenessCarrier family' diagonalLeft' diagonalRight' threshold' readbackLeft'
          readbackRight' sealLeft' sealRight' separated' transport' route' provenance' localCert'
          endpoint' bundle pkg ->
        hsame sealLeft sealLeft' ->
          hsame sealRight sealRight' ->
            hsame separated separated' ∧ PkgSig bundle endpoint pkg ∧
              PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier carrier' sameSealLeft sameSealRight
  obtain ⟨_familyUnary, _diagonalLeftUnary, _diagonalRightUnary, _thresholdUnary,
    _readbackLeftUnary, _readbackRightUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localCertUnary, _familyThresholdDiagonalLeft, _familyThresholdDiagonalRight,
    _diagonalLeftThresholdReadback, _diagonalRightThresholdReadback,
    _readbackLeftThresholdSeal, _readbackRightThresholdSeal, sealComparison,
    _separatedTransportEndpoint, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_familyUnary', _diagonalLeftUnary', _diagonalRightUnary', _thresholdUnary',
    _readbackLeftUnary', _readbackRightUnary', _transportUnary', _routeUnary',
    _provenanceUnary', _localCertUnary', _familyThresholdDiagonalLeft',
    _familyThresholdDiagonalRight', _diagonalLeftThresholdReadback',
    _diagonalRightThresholdReadback', _readbackLeftThresholdSeal',
    _readbackRightThresholdSeal', sealComparison', _separatedTransportEndpoint',
    _routeProvenanceEndpoint', endpointPkg'⟩ := carrier'
  have sameSeparated : hsame separated separated' :=
    cont_respects_hsame sameSealLeft sameSealRight sealComparison sealComparison'
  exact ⟨sameSeparated, endpointPkg, endpointPkg'⟩

end BEDC.Derived.RegularLimitUniquenessUp
