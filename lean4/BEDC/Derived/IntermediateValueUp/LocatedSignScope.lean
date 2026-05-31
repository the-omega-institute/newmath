import BEDC.Derived.IntermediateValueUp.TasteGate

namespace BEDC.Derived.IntermediateValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem IntermediateValueCarrier_located_sign_scope [AskSetup] [PackageSetup]
    {locatedInterval endpointNegative endpointPositive continuousMap modulusBudget
      bisectionLedger nestedWindow realSeal transports routes provenance localNameCert
      convergenceRead streamRead regSeqRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    IntermediateValueCarrier locatedInterval endpointNegative endpointPositive continuousMap
        modulusBudget bisectionLedger nestedWindow realSeal transports routes provenance
        localNameCert bundle pkg ->
      Cont bisectionLedger nestedWindow convergenceRead ->
        Cont convergenceRead realSeal streamRead ->
          Cont streamRead realSeal regSeqRead ->
            Cont regSeqRead localNameCert rootRead ->
              PkgSig bundle rootRead pkg ->
                UnaryHistory convergenceRead ∧ UnaryHistory streamRead ∧
                  UnaryHistory regSeqRead ∧ UnaryHistory rootRead ∧
                    Cont bisectionLedger nestedWindow convergenceRead ∧
                      Cont convergenceRead realSeal streamRead ∧
                        Cont streamRead realSeal regSeqRead ∧
                          Cont regSeqRead localNameCert rootRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  intro carrier bisectionNestedConvergence convergenceSealStream streamSealRegSeq
    regSeqNameCertRoot rootPkg
  obtain ⟨_locatedUnary, _endpointNegativeUnary, _endpointPositiveUnary, _continuousUnary,
    modulusUnary, bisectionUnary, _transportsUnary, _routesUnary, _provenanceUnary,
    localNameCertUnary, modulusBisectionNested, bisectionNestedSeal, provenancePkg,
    _localNameCertPkg⟩ := carrier
  have nestedUnary : UnaryHistory nestedWindow :=
    unary_cont_closed modulusUnary bisectionUnary modulusBisectionNested
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedSeal
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed bisectionUnary nestedUnary bisectionNestedConvergence
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed convergenceUnary realSealUnary convergenceSealStream
  have regSeqUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamUnary realSealUnary streamSealRegSeq
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed regSeqUnary localNameCertUnary regSeqNameCertRoot
  exact
    ⟨convergenceUnary, streamUnary, regSeqUnary, rootUnary, bisectionNestedConvergence,
      convergenceSealStream, streamSealRegSeq, regSeqNameCertRoot, provenancePkg, rootPkg⟩

end BEDC.Derived.IntermediateValueUp
