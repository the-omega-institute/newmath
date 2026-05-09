import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatorRootInputPacket [AskSetup] [PackageSetup]
    (dirichlet numfield unit inverse rank basis determinant provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory dirichlet ∧ UnaryHistory numfield ∧ UnaryHistory unit ∧
    UnaryHistory inverse ∧ UnaryHistory rank ∧ UnaryHistory basis ∧
      UnaryHistory determinant ∧ UnaryHistory provenance ∧
        Cont provenance determinant endpoint ∧ PkgSig bundle endpoint pkg

theorem RegulatorRootInputPacket_ledger_exactness [AskSetup] [PackageSetup]
    {dirichlet numfield unit inverse rank basis determinant provenance endpoint
      determinantLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatorRootInputPacket dirichlet numfield unit inverse rank basis determinant provenance
        endpoint bundle pkg ->
      Cont basis determinant determinantLedger ->
        UnaryHistory determinantLedger ∧ hsame determinantLedger (append basis determinant) ∧
          hsame endpoint (append provenance determinant) ∧ PkgSig bundle endpoint pkg := by
  intro packet determinantLedgerCont
  cases packet with
  | intro _ rest =>
      cases rest with
      | intro _ rest =>
          cases rest with
          | intro _ rest =>
              cases rest with
              | intro _ rest =>
                  cases rest with
                  | intro _ rest =>
                      cases rest with
                      | intro basisUnary rest =>
                          cases rest with
                          | intro determinantUnary rest =>
                              cases rest with
                              | intro provenanceUnary rest =>
                                  cases rest with
                                  | intro endpointCont endpointPkg =>
                                      have determinantLedgerUnary :
                                          UnaryHistory determinantLedger :=
                                        unary_cont_closed basisUnary determinantUnary
                                          determinantLedgerCont
                                      exact And.intro determinantLedgerUnary
                                        (And.intro determinantLedgerCont
                                          (And.intro endpointCont endpointPkg))

end BEDC.Derived.RegulatorUp
