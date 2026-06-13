import BEDC.Derived.BishopLocatedCompletionBoundaryUp.WindowExhaustion

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopLocatedCompletionBoundaryInductiveRoute [AskSetup] [PackageSetup]
    {stream regseq dyadic regular locatedLimit locatedReal realSeal transport replay provenance
      localName windowRead dyadicRead regularRead limitRead locatedRead sealRead transportRead
      replayRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopLocatedCompletionBoundaryCarrier stream regseq dyadic regular locatedLimit locatedReal
        realSeal transport replay provenance localName bundle pkg ->
      Cont stream regseq windowRead ->
        Cont windowRead dyadic dyadicRead ->
          Cont dyadicRead regular regularRead ->
            Cont regular locatedLimit limitRead ->
              Cont limitRead locatedReal locatedRead ->
                Cont locatedRead realSeal sealRead ->
                  Cont sealRead transport transportRead ->
                    Cont transportRead replay replayRead ->
                      Cont replayRead localName terminalRead ->
                        PkgSig bundle terminalRead pkg ->
                          UnaryHistory terminalRead ∧ Cont replayRead localName terminalRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle terminalRead pkg ∧
                              hsame terminalRead terminalRead := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier windowRoute dyadicRoute regularRoute limitRoute locatedRoute sealRoute
    transportRoute replayRoute terminalRoute terminalPkg
  obtain ⟨streamUnary, regseqUnary, dyadicUnary, regularUnary, locatedLimitUnary,
    locatedRealUnary, realSealUnary, transportUnary, replayUnary, _provenanceUnary,
    localNameUnary, _streamRegseqDyadic, _dyadicRegularLocatedLimit,
    _locatedLimitLocatedRealRealSeal, provenancePkg, _localNamePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary regseqUnary windowRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dyadicUnary dyadicRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicReadUnary regularUnary regularRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed regularUnary locatedLimitUnary limitRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed limitReadUnary locatedRealUnary locatedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed locatedReadUnary realSealUnary sealRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed sealReadUnary transportUnary transportRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportReadUnary replayUnary replayRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed replayReadUnary localNameUnary terminalRoute
  exact
    ⟨terminalReadUnary, terminalRoute, provenancePkg, terminalPkg,
      hsame_refl terminalRead⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp
