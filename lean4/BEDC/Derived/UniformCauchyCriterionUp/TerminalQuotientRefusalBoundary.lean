import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_terminal_quotient_refusal_boundary
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name regseqRead
      regseqRead' realRead realRead' correspondence windowRead tailRead sealRead
      classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail regseqRead ->
        Cont index tail regseqRead' ->
          Cont tail sealRow realRead ->
            Cont tail sealRow realRead' ->
              Cont regseqRead realRead correspondence ->
                PkgSig bundle correspondence pkg ->
                  Cont index windows windowRead ->
                    Cont windowRead tail tailRead ->
                      Cont tail sealRow sealRead ->
                        Cont tailRead sealRead classifierRead ->
                          PkgSig bundle classifierRead pkg ->
                            hsame regseqRead regseqRead' ∧ hsame realRead realRead' ∧
                              UnaryHistory correspondence ∧ UnaryHistory classifierRead ∧
                                Cont regseqRead realRead correspondence ∧
                                  Cont tailRead sealRead classifierRead ∧
                                    PkgSig bundle name pkg ∧
                                      PkgSig bundle correspondence pkg ∧
                                        PkgSig bundle classifierRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet indexTailRegseq indexTailRegseq' tailSealReal tailSealReal'
    regseqRealCorrespondence correspondencePkg windowRoute tailRoute sealRoute classifierRoute
    classifierPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealTransports,
    _transportsRoutesProvenance, namePkg⟩ := packet
  have regseqSame : hsame regseqRead regseqRead' :=
    cont_respects_hsame (hsame_refl index) (hsame_refl tail) indexTailRegseq
      indexTailRegseq'
  have realSame : hsame realRead realRead' :=
    cont_respects_hsame (hsame_refl tail) (hsame_refl sealRow) tailSealReal tailSealReal'
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed indexUnary tailUnary indexTailRegseq
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealReal
  have correspondenceUnary : UnaryHistory correspondence :=
    unary_cont_closed regseqUnary realUnary regseqRealCorrespondence
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowsUnary windowRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed windowUnary tailUnary tailRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary sealRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed tailReadUnary sealReadUnary classifierRoute
  exact
    ⟨regseqSame, realSame, correspondenceUnary, classifierUnary, regseqRealCorrespondence,
      classifierRoute, namePkg, correspondencePkg, classifierPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
