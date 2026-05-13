import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FoldDefectStokesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FoldDefectStokesPacket [AskSetup] [PackageSetup]
    (input output boundary ledger transport routes provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory input ∧ UnaryHistory output ∧ UnaryHistory boundary ∧
    UnaryHistory ledger ∧ UnaryHistory nameRow ∧ Cont input output routes ∧
      Cont boundary ledger transport ∧ Cont routes transport provenance ∧
        PkgSig bundle provenance pkg

theorem FoldDefectStokesPacket_boundary_ledger [AskSetup] [PackageSetup]
    {input output boundary ledger transport routes provenance nameRow publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FoldDefectStokesPacket input output boundary ledger transport routes provenance nameRow
        bundle pkg ->
      Cont output boundary publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory input ∧ UnaryHistory output ∧ UnaryHistory boundary ∧
            UnaryHistory ledger ∧ UnaryHistory publicRead ∧ Cont input output routes ∧
              Cont output boundary publicRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle publicRead pkg := by
  intro packet boundaryRoute publicPkg
  obtain ⟨inputUnary, outputUnary, boundaryUnary, ledgerUnary, _nameRowUnary, routesRoute,
    _transportRoute, _provenanceRoute, provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary boundaryUnary boundaryRoute
  exact
    ⟨inputUnary, outputUnary, boundaryUnary, ledgerUnary, publicUnary, routesRoute,
      boundaryRoute, provenancePkg, publicPkg⟩

theorem FoldDefectStokesPacket_non_escape_boundary [AskSetup] [PackageSetup]
    {input output boundary ledger transportRow routes provenance nameRow publicBoundary
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FoldDefectStokesPacket input output boundary ledger transportRow routes provenance nameRow
        bundle pkg ->
      Cont output boundary publicBoundary ->
        Cont boundary ledger ledgerRead ->
          PkgSig bundle publicBoundary pkg ->
            UnaryHistory input ∧ UnaryHistory output ∧ UnaryHistory boundary ∧
              UnaryHistory ledger ∧ UnaryHistory publicBoundary ∧ UnaryHistory ledgerRead ∧
                Cont input output routes ∧ Cont output boundary publicBoundary ∧
                  Cont boundary ledger ledgerRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle publicBoundary pkg := by
  intro packet boundaryRoute ledgerRoute publicPkg
  obtain ⟨inputUnary, outputUnary, boundaryUnary, ledgerUnary, _nameRowUnary, routesRoute,
    _transportRoute, _provenanceRoute, provenancePkg⟩ := packet
  have publicBoundaryUnary : UnaryHistory publicBoundary :=
    unary_cont_closed outputUnary boundaryUnary boundaryRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundaryUnary ledgerUnary ledgerRoute
  exact
    ⟨inputUnary, outputUnary, boundaryUnary, ledgerUnary, publicBoundaryUnary, ledgerReadUnary,
      routesRoute, boundaryRoute, ledgerRoute, provenancePkg, publicPkg⟩

theorem FoldDefectStokesPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {input output boundary ledger transport routes provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FoldDefectStokesPacket input output boundary ledger transport routes provenance nameRow
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          FoldDefectStokesPacket input output boundary ledger transport routes provenance
            nameRow bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FoldDefectStokesPacket input output boundary ledger transport routes provenance
            nameRow bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          FoldDefectStokesPacket input output boundary ledger transport routes provenance
            nameRow bundle pkg ∧ hsame row provenance)
        hsame ∧
        UnaryHistory input ∧ UnaryHistory output ∧ UnaryHistory boundary ∧
          UnaryHistory ledger ∧ UnaryHistory nameRow ∧ Cont input output routes ∧
            Cont boundary ledger transport ∧ Cont routes transport provenance ∧
              PkgSig bundle provenance pkg := by
  intro packet
  let packetWitness :
      FoldDefectStokesPacket input output boundary ledger transport routes provenance
        nameRow bundle pkg :=
    packet
  obtain ⟨inputUnary, outputUnary, boundaryUnary, ledgerUnary, nameUnary, routesCont,
    transportCont, provenanceCont, pkgSig⟩ := packet
  let Carrier : BHist → Prop :=
    fun row =>
      FoldDefectStokesPacket input output boundary ledger transport routes provenance
        nameRow bundle pkg ∧ hsame row provenance
  have core : NameCert Carrier hsame := {
    carrier_inhabited := by
      exact Exists.intro provenance (And.intro packetWitness (hsame_refl provenance))
    equiv_refl := by
      intro row _rowCarrier
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' same
      exact hsame_symm same
    equiv_trans := by
      intro _row _row' _row'' same same'
      exact hsame_trans same same'
    carrier_respects_equiv := by
      intro _row _row' same rowCarrier
      exact And.intro rowCarrier.left (hsame_trans (hsame_symm same) rowCarrier.right)
  }
  have cert : SemanticNameCert Carrier Carrier Carrier hsame := {
    core := core
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact
    ⟨cert, inputUnary, outputUnary, boundaryUnary, ledgerUnary, nameUnary, routesCont,
      transportCont, provenanceCont, pkgSig⟩

theorem FoldDefectStokesPacket_projection_stability [AskSetup] [PackageSetup]
    {input output boundary ledger transport routes provenance nameRow input' output' boundary' ledger'
      transport' routes' provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FoldDefectStokesPacket input output boundary ledger transport routes provenance nameRow bundle pkg ->
      hsame input input' -> hsame output output' -> hsame boundary boundary' -> hsame ledger ledger' ->
        hsame transport transport' -> hsame routes routes' -> hsame provenance provenance' ->
          Cont input' output' routes' -> Cont boundary' ledger' transport' ->
            Cont routes' transport' provenance' -> PkgSig bundle provenance' pkg ->
              FoldDefectStokesPacket input' output' boundary' ledger' transport' routes'
                  provenance' nameRow bundle pkg ∧
                hsame output output' ∧ hsame boundary boundary' ∧ hsame ledger ledger' := by
  intro packet sameInput sameOutput sameBoundary sameLedger _sameTransport _sameRoutes
    _sameProvenance inputOutputRoutes boundaryLedgerTransport routesTransportProvenance
    provenancePkg
  obtain ⟨inputUnary, outputUnary, boundaryUnary, ledgerUnary, nameUnary, _inputOutputRoutes,
    _boundaryLedgerTransport, _routesTransportProvenance, _provenancePkg⟩ := packet
  exact
    ⟨⟨unary_transport inputUnary sameInput,
        unary_transport outputUnary sameOutput,
        unary_transport boundaryUnary sameBoundary,
        unary_transport ledgerUnary sameLedger,
        nameUnary,
        inputOutputRoutes,
        boundaryLedgerTransport,
        routesTransportProvenance,
        provenancePkg⟩,
      sameOutput, sameBoundary, sameLedger⟩

end BEDC.Derived.FoldDefectStokesUp
