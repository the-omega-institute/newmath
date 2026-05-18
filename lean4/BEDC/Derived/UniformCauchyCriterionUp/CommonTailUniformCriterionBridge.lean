import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_common_tail_uniform_criterion_bridge
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name commonTail
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont windows tail commonTail →
        Cont commonTail sealRow realSeal →
          PkgSig bundle realSeal pkg →
            UnaryHistory windows ∧ UnaryHistory tail ∧ UnaryHistory commonTail ∧
              UnaryHistory sealRow ∧ UnaryHistory realSeal ∧ Cont windows tail commonTail ∧
                Cont commonTail sealRow realSeal ∧ Cont index windows modulus ∧
                  Cont modulus tolerance tail ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro packet windowsTailCommon commonSealReal realPkg
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    indexWindowsModulus, modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have commonTailUnary : UnaryHistory commonTail :=
    unary_cont_closed windowsUnary tailUnary windowsTailCommon
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed commonTailUnary sealRowUnary commonSealReal
  exact
    ⟨windowsUnary, tailUnary, commonTailUnary, sealRowUnary, realSealUnary,
      windowsTailCommon, commonSealReal, indexWindowsModulus, modulusToleranceTail, namePkg,
      realPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
