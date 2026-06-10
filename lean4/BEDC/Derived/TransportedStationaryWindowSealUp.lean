import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TransportedStationaryWindowSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def TransportedStationaryWindowSealCarrier [AskSetup] [PackageSetup]
    (sourceRow windowRow regularRow sealRow transportRow replayRow provenanceRow nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceRow ∧ UnaryHistory windowRow ∧ UnaryHistory regularRow ∧
    UnaryHistory sealRow ∧ UnaryHistory transportRow ∧ UnaryHistory replayRow ∧
      UnaryHistory provenanceRow ∧ UnaryHistory nameRow ∧
        Cont sourceRow windowRow regularRow ∧ Cont regularRow sealRow replayRow ∧
          PkgSig bundle provenanceRow pkg ∧ PkgSig bundle nameRow pkg

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

theorem TransportedStationaryWindowSealTailCofinalityHandoff [AskSetup] [PackageSetup]
    {S W R E H C P N tailRead windowRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TransportedStationaryWindowSealCarrier S W R E H C P N bundle pkg →
      Cont S W tailRead →
        Cont tailRead R windowRead →
          Cont windowRead E sealRead →
            Cont sealRead N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                        hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row tailRead ∨ hsame row windowRead ∨
                            hsame row sealRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S W tailRead ∧ Cont tailRead R windowRead ∧
                        Cont windowRead E sealRead ∧ Cont sealRead N namedRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory tailRead ∧ UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier tailRoute windowRoute sealRoute namedRoute namedPkg
  obtain ⟨sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _sourceRoute, _replayRoute, provenancePkg, _namePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sUnary wUnary tailRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tailUnary rUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary eUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row tailRead ∨
                hsame row windowRead ∨ hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W tailRead ∧ Cont tailRead R windowRead ∧
              Cont windowRead E sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, windowRoute, sealRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, tailUnary, windowUnary, sealUnary, namedUnary⟩

end BEDC.Derived.TransportedStationaryWindowSealUp
