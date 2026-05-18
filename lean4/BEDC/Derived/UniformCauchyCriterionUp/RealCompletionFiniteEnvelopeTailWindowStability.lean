import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionRealCompletionFiniteEnvelope_tail_window_stability
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name
      windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont windows tail windowRead →
        PkgSig bundle windowRead pkg →
          UnaryHistory windows ∧ UnaryHistory tail ∧ UnaryHistory windowRead ∧
            Cont windows tail windowRead ∧ PkgSig bundle name pkg ∧
              PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet windowTailRead windowReadPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary tailUnary windowTailRead
  exact
    ⟨windowsUnary, tailUnary, windowReadUnary, windowTailRead, namePkg, windowReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
