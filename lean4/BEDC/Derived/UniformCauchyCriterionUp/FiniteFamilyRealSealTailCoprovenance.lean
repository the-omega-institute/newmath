import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_real_seal_tail_coprovenance
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead coprovenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail regseqRead →
        Cont tail sealRow realRead →
          Cont regseqRead realRead coprovenance →
            PkgSig bundle regseqRead pkg →
              PkgSig bundle realRead pkg →
                PkgSig bundle coprovenance pkg →
                  UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                    UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                      UnaryHistory regseqRead ∧ UnaryHistory realRead ∧
                        UnaryHistory coprovenance ∧ Cont index windows modulus ∧
                          Cont modulus tolerance tail ∧ Cont index tail regseqRead ∧
                            Cont tail sealRow realRead ∧
                              Cont regseqRead realRead coprovenance ∧
                                PkgSig bundle name pkg ∧ PkgSig bundle regseqRead pkg ∧
                                  PkgSig bundle realRead pkg ∧
                                    PkgSig bundle coprovenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealCoprovenance regseqPkg realPkg
    coprovenancePkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have coprovenanceUnary : UnaryHistory coprovenance :=
    unary_cont_closed regseqUnary realUnary regseqRealCoprovenance
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      regseqUnary, realUnary, coprovenanceUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailRegseq, tailSealReal, regseqRealCoprovenance, namePkg, regseqPkg, realPkg,
      coprovenancePkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
