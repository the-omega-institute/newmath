import BEDC.Derived.CauchyUp

namespace BEDC.Derived.CauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyBaseForwardL10Route [AskSetup] [PackageSetup]
    {stream dyadic regseq sumTail realSeal transport replay provenance localName requestRead
      toleranceRead tailRead sealRead structuralRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory stream ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory sumTail ->
            UnaryHistory realSeal ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  UnaryHistory provenance ->
                    UnaryHistory localName ->
                      Cont stream dyadic requestRead ->
                        Cont requestRead regseq toleranceRead ->
                          Cont toleranceRead sumTail tailRead ->
                            Cont tailRead realSeal sealRead ->
                              Cont transport replay structuralRead ->
                                Cont provenance localName namedRead ->
                                  PkgSig bundle provenance pkg ->
                                    PkgSig bundle localName pkg ->
                                      UnaryHistory requestRead ∧
                                        UnaryHistory toleranceRead ∧
                                          UnaryHistory tailRead ∧
                                            UnaryHistory sealRead ∧
                                              UnaryHistory structuralRead ∧
                                                UnaryHistory namedRead ∧
                                                  Cont requestRead regseq toleranceRead ∧
                                                    Cont toleranceRead sumTail tailRead ∧
                                                      Cont tailRead realSeal sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro streamUnary dyadicUnary regseqUnary sumTailUnary realSealUnary transportUnary
    replayUnary provenanceUnary localNameUnary streamDyadicRoute requestRegseqRoute
    toleranceSumTailRoute tailRealSealRoute transportReplayRoute provenanceNameRoute
    _provenancePkg _localNamePkg
  have requestReadUnary : UnaryHistory requestRead :=
    unary_cont_closed streamUnary dyadicUnary streamDyadicRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed requestReadUnary regseqUnary requestRegseqRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed toleranceReadUnary sumTailUnary toleranceSumTailRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailReadUnary realSealUnary tailRealSealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary transportReplayRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceNameRoute
  exact
    ⟨requestReadUnary, toleranceReadUnary, tailReadUnary, sealReadUnary,
      structuralReadUnary, namedReadUnary, requestRegseqRoute, toleranceSumTailRoute,
      tailRealSealRoute⟩

end BEDC.Derived.CauchyUp
