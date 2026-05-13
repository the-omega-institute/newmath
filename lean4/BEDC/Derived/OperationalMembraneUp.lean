import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OperationalMembraneUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OperationalMembranePacket [AskSetup] [PackageSetup]
    (sourceScan ancestry importBoundary drift transport routes provenance ledger name :
      BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceScan ∧ UnaryHistory ancestry ∧ UnaryHistory importBoundary ∧
    UnaryHistory drift ∧ UnaryHistory transport ∧ UnaryHistory routes ∧
      UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory name ∧
        Cont sourceScan ancestry transport ∧ Cont importBoundary drift routes ∧
          Cont transport routes provenance ∧ Cont provenance ledger name ∧
            PkgSig bundle name pkg

theorem OperationalMembranePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {sourceScan ancestry importBoundary drift transport routes provenance ledger name
      sourceRead driftRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OperationalMembranePacket sourceScan ancestry importBoundary drift transport routes
        provenance ledger name bundle pkg ->
      Cont sourceScan ancestry sourceRead ->
        Cont importBoundary drift driftRead ->
          Cont ledger name ledgerRead ->
            PkgSig bundle sourceRead pkg ->
              PkgSig bundle driftRead pkg ->
                PkgSig bundle ledgerRead pkg ->
                  UnaryHistory sourceScan ∧ UnaryHistory ancestry ∧
                    UnaryHistory importBoundary ∧ UnaryHistory drift ∧
                      UnaryHistory sourceRead ∧ UnaryHistory driftRead ∧
                        UnaryHistory ledgerRead ∧ Cont sourceScan ancestry sourceRead ∧
                          Cont importBoundary drift driftRead ∧ Cont ledger name ledgerRead ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle sourceRead pkg ∧
                              PkgSig bundle driftRead pkg ∧
                                PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet sourceScanAncestrySourceRead importBoundaryDriftRead ledgerNameRead
    sourceReadPkg driftReadPkg ledgerReadPkg
  obtain ⟨sourceScanUnary, ancestryUnary, importBoundaryUnary, driftUnary, _transportUnary,
    _routesUnary, _provenanceUnary, ledgerUnary, nameUnary, _sourceScanAncestryTransport,
    _importBoundaryDriftRoutes, _transportRoutesProvenance, _provenanceLedgerName,
    namePkg⟩ := packet
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceScanUnary ancestryUnary sourceScanAncestrySourceRead
  have driftReadUnary : UnaryHistory driftRead :=
    unary_cont_closed importBoundaryUnary driftUnary importBoundaryDriftRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary nameUnary ledgerNameRead
  exact
    ⟨sourceScanUnary, ancestryUnary, importBoundaryUnary, driftUnary, sourceReadUnary,
      driftReadUnary, ledgerReadUnary, sourceScanAncestrySourceRead, importBoundaryDriftRead,
      ledgerNameRead, namePkg, sourceReadPkg, driftReadPkg, ledgerReadPkg⟩

end BEDC.Derived.OperationalMembraneUp
