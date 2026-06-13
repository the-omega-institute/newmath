import BEDC.Derived.BishopLocatedCompletionBoundaryUp.RegularCauchyExtraction

namespace BEDC.Derived.BishopLocatedCompletionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopLocatedCompletionBoundaryScopedRoute [AskSetup] [PackageSetup]
    {stream regseq dyadic regular locatedLimit locatedReal realSeal transport replay provenance
      localName windowRead boundaryRead locatedRead sealRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BishopLocatedCompletionBoundaryCarrier stream regseq dyadic regular locatedLimit locatedReal
        realSeal transport replay provenance localName bundle pkg →
      Cont stream regseq windowRead →
        Cont windowRead dyadic boundaryRead →
          Cont boundaryRead locatedLimit locatedRead →
            Cont locatedRead realSeal sealRead →
              Cont sealRead localName scopedRead →
                PkgSig bundle scopedRead pkg →
                  UnaryHistory stream ∧ UnaryHistory regseq ∧ UnaryHistory dyadic ∧
                    UnaryHistory locatedLimit ∧ UnaryHistory realSeal ∧
                      UnaryHistory localName ∧ UnaryHistory windowRead ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory locatedRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory scopedRead ∧
                            Cont stream regseq windowRead ∧
                              Cont windowRead dyadic boundaryRead ∧
                                Cont boundaryRead locatedLimit locatedRead ∧
                                  Cont locatedRead realSeal sealRead ∧
                                    Cont sealRead localName scopedRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle scopedRead pkg := by
  -- BEDC touchpoint anchor: BishopLocatedCompletionBoundaryCarrier BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier streamRegseqWindow windowDyadicBoundary boundaryLocated locatedSeal
    sealLocalName scopedPkg
  obtain ⟨streamUnary, regseqUnary, dyadicUnary, _regularUnary, locatedLimitUnary,
    _locatedRealUnary, realSealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _streamRegseqDyadic, _dyadicRegularLocatedLimit,
    _locatedLimitLocatedRealRealSeal, provenancePkg, _localNamePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary regseqUnary streamRegseqWindow
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicBoundary
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed boundaryUnary locatedLimitUnary boundaryLocated
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed locatedUnary realSealUnary locatedSeal
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed sealUnary localNameUnary sealLocalName
  exact
    ⟨streamUnary, regseqUnary, dyadicUnary, locatedLimitUnary, realSealUnary,
      localNameUnary, windowUnary, boundaryUnary, locatedUnary, sealUnary, scopedUnary,
      streamRegseqWindow, windowDyadicBoundary, boundaryLocated, locatedSeal, sealLocalName,
      provenancePkg, scopedPkg⟩

end BEDC.Derived.BishopLocatedCompletionBoundaryUp
