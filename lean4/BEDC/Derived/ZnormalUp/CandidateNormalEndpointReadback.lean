import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacketCandidateNormalEndpointReadback [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      candidate endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead routes candidate →
          Cont candidate transports endpoint →
            PkgSig bundle endpoint pkg →
              UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
                UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory normalRead ∧
                  UnaryHistory candidate ∧ UnaryHistory transports ∧
                    UnaryHistory endpoint ∧ Cont normal continuation normalRead ∧
                      Cont normalRead routes candidate ∧ Cont candidate transports endpoint ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet normalContinuationRead readRoutesCandidate candidateTransportsEndpoint endpointPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationRead
  have candidateUnary : UnaryHistory candidate :=
    unary_cont_closed normalReadUnary routesUnary readRoutesCandidate
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed candidateUnary transportsUnary candidateTransportsEndpoint
  exact
    ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary, normalReadUnary,
      candidateUnary, transportsUnary, endpointUnary, normalContinuationRead,
      readRoutesCandidate, candidateTransportsEndpoint, provenancePkg, endpointPkg⟩

end BEDC.Derived.ZnormalUp
