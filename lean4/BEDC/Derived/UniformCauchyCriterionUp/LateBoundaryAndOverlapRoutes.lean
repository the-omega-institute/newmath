import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_tail_readback_route [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name tailRead
      sealRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail tailRead →
        Cont tail sealRow sealRead →
          Cont sealRead routes terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory tailRead ∧ UnaryHistory sealRead ∧
                UnaryHistory terminalRead ∧ Cont index tail tailRead ∧
                  Cont tail sealRow sealRead ∧ Cont sealRead routes terminalRead ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRead tailSealRead sealRoutesTerminal terminalPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed indexUnary tailUnary indexTailRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed sealReadUnary routesUnary sealRoutesTerminal
  exact
    ⟨tailReadUnary, sealReadUnary, terminalReadUnary, indexTailRead, tailSealRead,
      sealRoutesTerminal, namePkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
