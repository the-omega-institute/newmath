import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitScopedDependencyPackage [AskSetup] [PackageSetup]
    {sequence limit window dyadic classifier transport replay provenance name windowRead
      limitRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequence limit window dyadic classifier transport replay
        provenance name bundle pkg ->
      Cont sequence window windowRead ->
        Cont limit dyadic limitRead ->
          Cont windowRead limitRead sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory sequence ∧ UnaryHistory limit ∧ UnaryHistory window ∧
                UnaryHistory dyadic ∧ UnaryHistory classifier ∧ UnaryHistory transport ∧
                  UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
                    UnaryHistory windowRead ∧ UnaryHistory limitRead ∧
                      UnaryHistory sealRead ∧ Cont sequence window replay ∧
                        Cont limit dyadic classifier ∧ Cont sequence window windowRead ∧
                          Cont limit dyadic limitRead ∧ Cont windowRead limitRead sealRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                              PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig
  intro carrier sequenceWindowRead limitDyadicRead readSeal sealPkg
  rcases carrier with
    ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, classifierUnary, transportUnary,
      replayUnary, provenanceUnary, nameUnary, sequenceWindowReplay, limitDyadicClassifier,
      _transportSame, _replaySame, provenancePkg, namePkg⟩
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sequenceUnary windowUnary sequenceWindowRead
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed limitUnary dyadicUnary limitDyadicRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary limitReadUnary readSeal
  exact
    ⟨sequenceUnary, limitUnary, windowUnary, dyadicUnary, classifierUnary, transportUnary,
      replayUnary, provenanceUnary, nameUnary, windowReadUnary, limitReadUnary, sealReadUnary,
      sequenceWindowReplay, limitDyadicClassifier, sequenceWindowRead, limitDyadicRead,
      readSeal, provenancePkg, namePkg, sealPkg⟩

end BEDC.Derived.RealSequenceLimitUp
