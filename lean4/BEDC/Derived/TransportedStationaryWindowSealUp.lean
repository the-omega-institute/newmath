import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TransportedStationaryWindowSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TransportedStationaryWindowSealPacket [AskSetup] [PackageSetup]
    (ratRow streamWindow sealRow envelope realRow diagonalRow routes provenance nameCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory ratRow ∧ UnaryHistory streamWindow ∧ UnaryHistory sealRow ∧
    UnaryHistory envelope ∧ UnaryHistory diagonalRow ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont ratRow streamWindow sealRow ∧
        Cont sealRow envelope realRow ∧ Cont realRow diagonalRow routes ∧
          Cont routes provenance nameCert ∧ Cont envelope sealRow endpoint ∧
            PkgSig bundle endpoint pkg

theorem TransportedStationaryWindowSealPacket_namecert_obligations
    [AskSetup] [PackageSetup]
    {ratRow streamWindow sealRow envelope realRow diagonalRow routes provenance nameCert
      endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransportedStationaryWindowSealPacket ratRow streamWindow sealRow envelope realRow
        diagonalRow routes provenance nameCert endpoint bundle pkg ->
      Cont envelope sealRow endpoint' ->
        PkgSig bundle endpoint' pkg ->
          TransportedStationaryWindowSealPacket ratRow streamWindow sealRow envelope realRow
              diagonalRow routes provenance nameCert endpoint' bundle pkg ∧
            hsame endpoint endpoint' := by
  intro packet endpointCont' endpointPkg'
  have endpointCont : Cont envelope sealRow endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.right.right.left
  have envelopeUnary : UnaryHistory envelope :=
    packet.right.right.right.left
  have sealUnary : UnaryHistory sealRow :=
    packet.right.right.left
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame rfl rfl endpointCont endpointCont'
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed envelopeUnary sealUnary endpointCont'
  have transported :
      TransportedStationaryWindowSealPacket ratRow streamWindow sealRow envelope realRow
        diagonalRow routes provenance nameCert endpoint' bundle pkg :=
    ⟨packet.left,
      packet.right.left,
      sealUnary,
      envelopeUnary,
      packet.right.right.right.right.left,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.right.right.right.left,
      endpointCont',
      endpointPkg'⟩
  exact And.intro transported endpointSame

theorem TransportedStationaryWindowSealPacket_readback_determinacy
    [AskSetup] [PackageSetup]
    {ratRow ratRow' streamWindow streamWindow' sealRow sealRow' envelope realRow diagonalRow
      routes provenance nameCert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransportedStationaryWindowSealPacket ratRow streamWindow sealRow envelope realRow
        diagonalRow routes provenance nameCert endpoint bundle pkg ->
      hsame ratRow ratRow' ->
        hsame streamWindow streamWindow' ->
          Cont ratRow' streamWindow' sealRow' ->
            hsame sealRow sealRow' ∧ Cont ratRow streamWindow sealRow ∧
              Cont ratRow' streamWindow' sealRow' := by
  intro packet ratSame windowSame transportedRoute
  have originalRoute : Cont ratRow streamWindow sealRow :=
    packet.right.right.right.right.right.right.right.right.left
  have sealSame : hsame sealRow sealRow' :=
    cont_respects_hsame ratSame windowSame originalRoute transportedRoute
  exact ⟨sealSame, originalRoute, transportedRoute⟩

theorem TransportedStationaryWindowSealPacket_real_factorization
    [AskSetup] [PackageSetup]
    {ratRow streamWindow sealRow envelope realRow diagonalRow routes provenance nameCert endpoint
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransportedStationaryWindowSealPacket ratRow streamWindow sealRow envelope realRow diagonalRow
        routes provenance nameCert endpoint bundle pkg ->
      Cont realRow routes realRead ->
        UnaryHistory realRow /\ UnaryHistory routes /\ UnaryHistory realRead /\
          Cont sealRow envelope realRow /\ Cont realRow diagonalRow routes /\
            Cont realRow routes realRead /\ PkgSig bundle endpoint pkg := by
  intro packet realReadRoute
  obtain ⟨_ratUnary, _streamUnary, sealUnary, envelopeUnary, _diagonalUnary, routesUnary,
    _provenanceUnary, _nameCertUnary, _ratStreamSeal, sealEnvelopeReal, realDiagonalRoutes,
    _routesProvenanceNameCert, _endpointCont, endpointPkg⟩ := packet
  have realUnary : UnaryHistory realRow :=
    unary_cont_closed sealUnary envelopeUnary sealEnvelopeReal
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed realUnary routesUnary realReadRoute
  exact
    ⟨realUnary, routesUnary, realReadUnary, sealEnvelopeReal, realDiagonalRoutes,
      realReadRoute, endpointPkg⟩

theorem TransportedStationaryWindowSealLedgerNonescape [AskSetup] [PackageSetup]
    {ratRow streamWindow sealRow envelope realRow diagonalRow routes provenance nameCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransportedStationaryWindowSealPacket ratRow streamWindow sealRow envelope realRow
        diagonalRow routes provenance nameCert endpoint bundle pkg ->
      UnaryHistory ratRow ∧ UnaryHistory streamWindow ∧ UnaryHistory sealRow ∧
        UnaryHistory envelope ∧ UnaryHistory realRow ∧ UnaryHistory routes ∧
          UnaryHistory provenance ∧ UnaryHistory nameCert ∧
            Cont ratRow streamWindow sealRow ∧ Cont sealRow envelope realRow ∧
              Cont realRow diagonalRow routes ∧ Cont routes provenance nameCert ∧
                Cont envelope sealRow endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  obtain ⟨ratUnary, streamUnary, sealUnary, envelopeUnary, _diagonalUnary, routesUnary,
    provenanceUnary, nameCertUnary, ratStreamSeal, sealEnvelopeReal, realDiagonalRoutes,
    routesProvenanceNameCert, endpointCont, endpointPkg⟩ := packet
  have realUnary : UnaryHistory realRow :=
    unary_cont_closed sealUnary envelopeUnary sealEnvelopeReal
  exact
    ⟨ratUnary, streamUnary, sealUnary, envelopeUnary, realUnary, routesUnary,
      provenanceUnary, nameCertUnary, ratStreamSeal, sealEnvelopeReal, realDiagonalRoutes,
      routesProvenanceNameCert, endpointCont, endpointPkg⟩

end BEDC.Derived.TransportedStationaryWindowSealUp
