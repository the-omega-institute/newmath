import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ZnormalPacket_terminal_normality_refusal_stability [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name typed' fuel'
      terminal' normal' continuation' transports' routes' provenance' name' terminalRead
      terminalRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      hsame typed typed' →
        hsame fuel fuel' →
          hsame terminal terminal' →
            hsame normal normal' →
              hsame continuation continuation' →
                hsame transports transports' →
                  hsame routes routes' →
                    hsame provenance provenance' →
                      hsame name name' →
                        Cont typed' fuel' terminal' →
                          Cont terminal' normal' continuation' →
                            Cont continuation' transports' routes' →
                              PkgSig bundle name' pkg →
                                PkgSig bundle provenance' pkg →
                                  Cont terminal normal terminalRead →
                                    Cont terminal' normal' terminalRead' →
                                      hsame terminalRead terminalRead' ∧
                                        ZnormalPacket typed' fuel' terminal' normal'
                                          continuation' transports' routes' provenance' name'
                                          bundle pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sameTyped sameFuel sameTerminal sameNormal sameContinuation sameTransports
    sameRoutes sameProvenance sameName typedFuelTerminal' terminalNormalContinuation'
    continuationTransportsRoutes' namePkg' provenancePkg' terminalReadRoute
    terminalReadRoute'
  have refusalStable : hsame terminalRead terminalRead' :=
    cont_respects_hsame sameTerminal sameNormal terminalReadRoute terminalReadRoute'
  have transportedPacket :
      ZnormalPacket typed' fuel' terminal' normal' continuation' transports' routes'
        provenance' name' bundle pkg :=
    ZnormalPacket_componentwise_namecert_transport
      (typed := typed) (fuel := fuel) (terminal := terminal) (normal := normal)
      (continuation := continuation) (transports := transports) (routes := routes)
      (provenance := provenance) (name := name) (typed' := typed') (fuel' := fuel')
      (terminal' := terminal') (normal' := normal') (continuation' := continuation')
      (transports' := transports') (routes' := routes') (provenance' := provenance')
      (name' := name') (bundle := bundle) (pkg := pkg) packet sameTyped sameFuel
      sameTerminal sameNormal sameContinuation sameTransports sameRoutes sameProvenance
      sameName typedFuelTerminal' terminalNormalContinuation' continuationTransportsRoutes'
      namePkg' provenancePkg'
  exact ⟨refusalStable, transportedPacket⟩

end BEDC.Derived.ZnormalUp
