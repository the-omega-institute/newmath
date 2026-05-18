import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_real_envelope_witness_extraction [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name witnessRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont windows tail witnessRead →
        Cont witnessRead sealRow terminalRead →
          PkgSig bundle terminalRead pkg →
            UnaryHistory windows ∧ UnaryHistory tail ∧ UnaryHistory witnessRead ∧
              UnaryHistory sealRow ∧ UnaryHistory terminalRead ∧
                Cont windows tail witnessRead ∧ Cont witnessRead sealRow terminalRead ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowsTailWitness witnessSealTerminal terminalPkg
  rcases packet with
    ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
      _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
      _modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowsUnary tailUnary windowsTailWitness
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed witnessUnary sealRowUnary witnessSealTerminal
  exact
    ⟨windowsUnary, tailUnary, witnessUnary, sealRowUnary, terminalUnary,
      windowsTailWitness, witnessSealTerminal, namePkg, terminalPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
