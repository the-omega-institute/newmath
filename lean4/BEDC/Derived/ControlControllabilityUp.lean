import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ControlControllabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ControlControllabilityReachabilityPacket [AskSetup] [PackageSetup]
    (state input transition control horizon columns matrix ledger provenance endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧ UnaryHistory control ∧
    UnaryHistory horizon ∧ UnaryHistory columns ∧ Cont control horizon columns ∧
      Cont transition columns matrix ∧ Cont matrix ledger provenance ∧
        Cont provenance state endpoint ∧ PkgSig probe endpoint pkg

theorem ControlControllabilityReachabilityPacket_endpoint_obligation [AskSetup] [PackageSetup]
    {state input transition control horizon columns matrix ledger provenance endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlControllabilityReachabilityPacket state input transition control horizon columns
        matrix ledger provenance endpoint probe pkg ->
      UnaryHistory columns ∧ UnaryHistory matrix ∧ Cont matrix ledger provenance ∧
        Cont provenance state endpoint ∧ hsame columns (append control horizon) ∧
          hsame matrix (append transition columns) ∧ hsame provenance (append matrix ledger) ∧
            hsame endpoint (append provenance state) ∧ PkgSig probe endpoint pkg := by
  intro packet
  cases packet with
  | intro stateUnary rest =>
      cases rest with
      | intro _inputUnary rest =>
          cases rest with
          | intro transitionUnary rest =>
              cases rest with
              | intro controlUnary rest =>
                  cases rest with
                  | intro horizonUnary rest =>
                      cases rest with
                      | intro columnsUnary rest =>
                          cases rest with
                          | intro columnsCont rest =>
                              cases rest with
                              | intro matrixCont rest =>
                                  cases rest with
                                  | intro provenanceCont rest =>
                                      cases rest with
                                      | intro endpointCont endpointPkg =>
                                          have matrixUnary : UnaryHistory matrix :=
                                            unary_cont_closed transitionUnary columnsUnary matrixCont
                                          exact And.intro columnsUnary
                                            (And.intro matrixUnary
                                              (And.intro provenanceCont
                                                (And.intro endpointCont
                                                  (And.intro columnsCont
                                                    (And.intro matrixCont
                                                      (And.intro provenanceCont
                                                        (And.intro endpointCont endpointPkg)))))))

end BEDC.Derived.ControlControllabilityUp
