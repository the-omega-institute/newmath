import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_tail_seal_coprovenance_lock
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      realRead coprovenance lockRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail regseqRead →
        Cont tail sealRow realRead →
          Cont regseqRead realRead coprovenance →
            Cont coprovenance name lockRead →
              PkgSig bundle regseqRead pkg →
                PkgSig bundle realRead pkg →
                  PkgSig bundle coprovenance pkg →
                    PkgSig bundle lockRead pkg →
                      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                        UnaryHistory tolerance ∧ UnaryHistory tail ∧
                          UnaryHistory sealRow ∧ UnaryHistory regseqRead ∧
                            UnaryHistory realRead ∧ UnaryHistory coprovenance ∧
                              UnaryHistory lockRead ∧ Cont index tail regseqRead ∧
                                Cont tail sealRow realRead ∧
                                  Cont regseqRead realRead coprovenance ∧
                                    Cont coprovenance name lockRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle lockRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRegseq tailSealReal regseqRealCoprovenance coprovenanceNameLock
    _regseqPkg _realPkg _coprovenancePkg lockPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have coprovenanceUnary : UnaryHistory coprovenance :=
    unary_cont_closed regseqUnary realUnary regseqRealCoprovenance
  have lockUnary : UnaryHistory lockRead :=
    unary_cont_closed coprovenanceUnary nameUnary coprovenanceNameLock
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      regseqUnary, realUnary, coprovenanceUnary, lockUnary, indexTailRegseq, tailSealReal,
      regseqRealCoprovenance, coprovenanceNameLock, namePkg, lockPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
