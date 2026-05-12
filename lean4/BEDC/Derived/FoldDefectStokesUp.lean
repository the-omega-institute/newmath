import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FoldDefectStokesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.FoldDefectStokesUp
