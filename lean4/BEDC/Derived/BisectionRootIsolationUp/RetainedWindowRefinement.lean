import BEDC.Derived.BisectionRootIsolationUp.RegSeqRatWindowHandoff

namespace BEDC.Derived.BisectionRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BisectionRootIsolationRetainedWindowRefinement [AskSetup] [PackageSetup]
    {interval bisection functionRow endpoint window readback sealRow transport replay provenance name
      retained requested exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BisectionRootIsolationCarrier interval bisection functionRow endpoint window readback sealRow
        transport replay provenance name bundle pkg →
      Cont bisection endpoint retained →
        Cont retained window requested →
          Cont requested readback exported →
            PkgSig bundle exported pkg →
              UnaryHistory retained ∧ UnaryHistory requested ∧ UnaryHistory exported ∧
                Cont bisection endpoint retained ∧ Cont retained window requested ∧
                  Cont requested readback exported ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle exported pkg ∧
                      List.Mem (bisectionRootIsolationEncodeBHist window)
                        (bisectionRootIsolationToEventFlow
                          (BisectionRootIsolationUp.mk interval bisection functionRow endpoint
                            window readback sealRow transport replay provenance name)) := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier retainedRoute requestedRoute exportedRoute exportedPkg
  obtain ⟨_intervalUnary, bisectionUnary, _functionUnary, endpointUnary, windowUnary,
    readbackUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _sealRoute, _endpointRoute, provenancePkg⟩ := carrier
  have retainedUnary : UnaryHistory retained :=
    unary_cont_closed bisectionUnary endpointUnary retainedRoute
  have requestedUnary : UnaryHistory requested :=
    unary_cont_closed retainedUnary windowUnary requestedRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed requestedUnary readbackUnary exportedRoute
  have windowListed :
      List.Mem (bisectionRootIsolationEncodeBHist window)
        (bisectionRootIsolationToEventFlow
          (BisectionRootIsolationUp.mk interval bisection functionRow endpoint window readback
            sealRow transport replay provenance name)) := by
    change
      List.Mem (bisectionRootIsolationEncodeBHist window)
        [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
          bisectionRootIsolationEncodeBHist interval,
          bisectionRootIsolationEncodeBHist bisection,
          bisectionRootIsolationEncodeBHist functionRow,
          bisectionRootIsolationEncodeBHist endpoint,
          bisectionRootIsolationEncodeBHist window,
          bisectionRootIsolationEncodeBHist readback,
          bisectionRootIsolationEncodeBHist sealRow,
          bisectionRootIsolationEncodeBHist transport,
          bisectionRootIsolationEncodeBHist replay,
          bisectionRootIsolationEncodeBHist provenance,
          bisectionRootIsolationEncodeBHist name]
    exact
      List.mem_cons_of_mem _
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ List.mem_cons_self))))
  exact
    ⟨retainedUnary, requestedUnary, exportedUnary, retainedRoute, requestedRoute, exportedRoute,
      provenancePkg, exportedPkg, windowListed⟩

end BEDC.Derived.BisectionRootIsolationUp
