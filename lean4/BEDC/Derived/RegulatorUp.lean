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

theorem RegulatorRootInputPacket_root_namecert_threshold [AskSetup] [PackageSetup]
    {dirichlet numfield unit inverse rank basis determinant provenance endpoint threshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatorRootInputPacket dirichlet numfield unit inverse rank basis determinant provenance
        endpoint bundle pkg ->
      Cont endpoint provenance threshold ->
        PkgSig bundle threshold pkg ->
          UnaryHistory threshold ∧ hsame threshold (append endpoint provenance) ∧
            RegulatorRootInputPacket dirichlet numfield unit inverse rank basis determinant
              provenance endpoint bundle pkg := by
  intro packet thresholdCont _
  cases packet with
  | intro dirichletUnary rest =>
      cases rest with
      | intro numfieldUnary rest =>
          cases rest with
          | intro unitUnary rest =>
              cases rest with
              | intro inverseUnary rest =>
                  cases rest with
                  | intro rankUnary rest =>
                      cases rest with
                      | intro basisUnary rest =>
                          cases rest with
                          | intro determinantUnary rest =>
                              cases rest with
                              | intro provenanceUnary rest =>
                                  cases rest with
                                  | intro endpointCont endpointPkg =>
                                      have endpointUnary : UnaryHistory endpoint :=
                                        unary_cont_closed provenanceUnary determinantUnary endpointCont
                                      have thresholdUnary : UnaryHistory threshold :=
                                        unary_cont_closed endpointUnary provenanceUnary thresholdCont
                                      exact And.intro thresholdUnary
                                        (And.intro thresholdCont
                                          (And.intro dirichletUnary
                                            (And.intro numfieldUnary
                                              (And.intro unitUnary
                                                (And.intro inverseUnary
                                                  (And.intro rankUnary
                                                    (And.intro basisUnary
                                                      (And.intro determinantUnary
                                                        (And.intro provenanceUnary
                                                          (And.intro endpointCont
                                                            endpointPkg))))))))))

end BEDC.Derived.RegulatorUp
