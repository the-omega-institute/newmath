import BEDC.Derived.ZnormalUp.FiniteNormalwordClassifierCompatibility

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_frontier_carry_readback_totality [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name normalRead
      carryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation normalRead →
        Cont normalRead routes carryRead →
          PkgSig bundle carryRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row carryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont normal continuation normalRead ∧ Cont normalRead routes row ∧
                    PkgSig bundle carryRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle carryRead pkg)
                hsame ∧
              UnaryHistory normalRead ∧ UnaryHistory carryRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet normalContinuationRead normalReadRoutesCarry carryPkg
  obtain ⟨cert, normalReadUnary, carryReadUnary⟩ :=
    ZnormalPacketFiniteNormalwordClassifierCompatibility packet normalContinuationRead
      normalReadRoutesCarry carryPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  exact ⟨cert, normalReadUnary, carryReadUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
