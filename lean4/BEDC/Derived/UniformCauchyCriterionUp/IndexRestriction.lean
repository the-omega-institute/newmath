import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_index_restriction [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name subIndex subTail
      subSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows subIndex ->
        Cont subIndex tail subTail ->
          Cont subTail sealRow subSeal ->
            PkgSig bundle subSeal pkg ->
              UnaryHistory subIndex ∧ UnaryHistory subTail ∧ UnaryHistory subSeal ∧
                Cont index windows subIndex ∧ Cont subIndex tail subTail ∧
                  Cont subTail sealRow subSeal ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle subSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet indexWindowSubIndex subIndexTailSubTail subTailSealSubSeal subSealPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have subIndexUnary : UnaryHistory subIndex :=
    unary_cont_closed indexUnary windowsUnary indexWindowSubIndex
  have subTailUnary : UnaryHistory subTail :=
    unary_cont_closed subIndexUnary tailUnary subIndexTailSubTail
  have subSealUnary : UnaryHistory subSeal :=
    unary_cont_closed subTailUnary sealRowUnary subTailSealSubSeal
  exact
    ⟨subIndexUnary, subTailUnary, subSealUnary, indexWindowSubIndex,
      subIndexTailSubTail, subTailSealSubSeal, namePkg, subSealPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
