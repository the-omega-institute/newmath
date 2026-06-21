import BEDC.Derived.ReductionFuelBoundaryUp.FuelTimeoutExactness
import BEDC.Derived.ReductionFuelBoundaryUp.TotalHostNonescape

namespace BEDC.Derived.ReductionFuelBoundaryUp.ObligationClosurePackage

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ReductionFuelBoundary_obligation_closure_package [AskSetup] [PackageSetup]
    {H F T E U A X C P N endpointRead timeoutRead auditRead replayRead
      hostExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H →
      UnaryHistory F →
        UnaryHistory T →
          UnaryHistory E →
            UnaryHistory U →
              UnaryHistory A →
                UnaryHistory X →
                  UnaryHistory C →
                    Cont H F T →
                      Cont T E endpointRead →
                        Cont T U timeoutRead →
                          Cont endpointRead A auditRead →
                            Cont timeoutRead A replayRead →
                              Cont auditRead C hostExport →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row H ∨ hsame row F ∨ hsame row T ∨
                                            hsame row E ∨ hsame row U ∨ hsame row A ∨
                                              hsame row X ∨ hsame row C)
                                        (fun row : BHist =>
                                          hsame row H ∨ hsame row F ∨ hsame row T ∨
                                            hsame row E ∨ hsame row U ∨ hsame row A ∨
                                              hsame row X ∨ hsame row C ∨ hsame row P ∨
                                                hsame row N)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont H F T ∧
                                            Cont T E endpointRead ∧ Cont T U timeoutRead ∧
                                              Cont endpointRead A auditRead ∧
                                                Cont timeoutRead A replayRead ∧
                                                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                        hsame ∧
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row hostExport ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row H ∨ hsame row F ∨ hsame row T ∨
                                              hsame row E ∨ hsame row U ∨ hsame row A ∨
                                                hsame row C ∨ hsame row hostExport)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont H F T ∧
                                              Cont T E endpointRead ∧ Cont T U timeoutRead ∧
                                                Cont endpointRead A auditRead ∧
                                                  Cont timeoutRead A replayRead ∧
                                                    Cont auditRead C hostExport ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle N pkg)
                                          hsame ∧
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row timeoutRead ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row F ∨ hsame row T ∨ hsame row U ∨
                                                hsame row timeoutRead)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧ Cont H F T ∧
                                                Cont T U timeoutRead ∧
                                                  Cont timeoutRead A replayRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg)
                                            hsame ∧
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                (hsame row endpointRead ∨
                                                    hsame row timeoutRead) ∧
                                                  UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row H ∨ hsame row F ∨ hsame row T ∨
                                                  hsame row E ∨ hsame row U ∨
                                                    hsame row A ∨ hsame row endpointRead ∨
                                                      hsame row timeoutRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont H F T ∧
                                                  Cont T E endpointRead ∧
                                                    Cont T U timeoutRead ∧
                                                      Cont endpointRead A auditRead ∧
                                                        Cont timeoutRead A replayRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory endpointRead ∧
                                              UnaryHistory timeoutRead ∧
                                                UnaryHistory auditRead ∧
                                                  UnaryHistory replayRead ∧
                                                    UnaryHistory hostExport := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert
  intro hUnary fUnary tUnary eUnary uUnary aUnary xUnary cUnary hostFuelRoute
    endpointRoute timeoutRoute auditRoute replayRoute hostExportRoute provenancePkg namePkg
  have obligationsCert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row T ∨ hsame row E ∨
              hsame row U ∨ hsame row A ∨ hsame row X ∨ hsame row C)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row T ∨ hsame row E ∨
              hsame row U ∨ hsame row A ∨ hsame row X ∨ hsame row C ∨
                hsame row P ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F T ∧ Cont T E endpointRead ∧
              Cont T U timeoutRead ∧ Cont endpointRead A auditRead ∧
                Cont timeoutRead A replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame :=
    ReductionFuelBoundary_namecert_obligations hUnary fUnary tUnary eUnary uUnary
      aUnary xUnary cUnary hostFuelRoute endpointRoute timeoutRoute auditRoute replayRoute
      provenancePkg namePkg
  obtain ⟨hostCert, endpointUnaryFromHost, timeoutUnaryFromHost, auditUnaryFromHost,
    replayUnaryFromHost, hostExportUnary⟩ :=
    BEDC.Derived.ReductionFuelBoundaryUp.TotalHostNonescape.ReductionFuelBoundaryTotalHostNonescape
      hUnary fUnary tUnary eUnary uUnary
        aUnary xUnary cUnary hostFuelRoute endpointRoute timeoutRoute auditRoute replayRoute
          hostExportRoute provenancePkg namePkg
  obtain ⟨timeoutCert, _timeoutUnaryFromFuel, _auditUnaryFromFuel⟩ :=
    BEDC.Derived.ReductionFuelBoundaryUp.FuelTimeoutExactness.ReductionFuelBoundary_fuel_timeout_exactness
      hUnary fUnary tUnary uUnary aUnary
        xUnary cUnary hostFuelRoute timeoutRoute replayRoute provenancePkg namePkg
  obtain ⟨endpointTimeoutCert, _endpointUnaryFromSplit, _timeoutUnaryFromSplit,
    _auditUnaryFromSplit, replayUnaryFromSplit⟩ :=
    BEDC.Derived.ReductionFuelBoundaryUp.EndpointTimeoutDisjointness.ReductionFuelBoundary_endpoint_timeout_disjointness
      hUnary fUnary tUnary eUnary
        uUnary aUnary xUnary cUnary hostFuelRoute endpointRoute timeoutRoute auditRoute
          replayRoute provenancePkg namePkg
  exact
    ⟨obligationsCert, hostCert, timeoutCert, endpointTimeoutCert, endpointUnaryFromHost,
      timeoutUnaryFromHost, auditUnaryFromHost, replayUnaryFromSplit, hostExportUnary⟩

end BEDC.Derived.ReductionFuelBoundaryUp.ObligationClosurePackage
