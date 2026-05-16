import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_regseqrat_real_seal_pullback_exactness
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont tail sealRow realRead ->
          Cont regseqRead realRead pullback ->
            PkgSig bundle pullback pkg ->
              UnaryHistory regseqRead ∧ UnaryHistory realRead ∧ UnaryHistory pullback ∧
                Cont index windows modulus ∧ Cont modulus tolerance tail ∧
                  Cont index tail regseqRead ∧ Cont tail sealRow realRead ∧
                    Cont regseqRead realRead pullback ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealPullback pullbackPkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealTransports, _transportsRoutesProvenance, namePkg⟩ :=
      packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed regseqUnary realUnary regseqRealPullback
  exact
    ⟨regseqUnary, realUnary, pullbackUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRegseq, tailSealReal, regseqRealPullback, namePkg, pullbackPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
