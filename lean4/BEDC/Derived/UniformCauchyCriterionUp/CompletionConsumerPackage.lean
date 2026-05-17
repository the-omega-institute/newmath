import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_completion_consumer_package [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name streamRead
      regseqRead realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index windows streamRead ->
        Cont index tail regseqRead ->
          Cont tail sealRow realRead ->
            Cont regseqRead realRead completionRead ->
              PkgSig bundle streamRead pkg ->
                PkgSig bundle regseqRead pkg ->
                  PkgSig bundle realRead pkg ->
                    PkgSig bundle completionRead pkg ->
                      UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                        UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                          UnaryHistory streamRead ∧ UnaryHistory regseqRead ∧
                            UnaryHistory realRead ∧ UnaryHistory completionRead ∧
                              Cont index windows streamRead ∧
                                Cont index tail regseqRead ∧
                                  Cont tail sealRow realRead ∧
                                    Cont regseqRead realRead completionRead ∧
                                      PkgSig bundle name pkg ∧
                                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro packet indexWindowsStreamRead indexTailRegseqRead tailSealRowRealRead
    regseqReadRealReadCompletionRead _streamReadPkg _regseqReadPkg _realReadPkg
    completionReadPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed indexUnary windowsUnary indexWindowsStreamRead
  have regseqReadUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseqRead
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRowRealRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed regseqReadUnary realReadUnary regseqReadRealReadCompletionRead
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      streamReadUnary, regseqReadUnary, realReadUnary, completionReadUnary,
      indexWindowsStreamRead, indexTailRegseqRead, tailSealRowRealRead,
      regseqReadRealReadCompletionRead, namePkg, completionReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
