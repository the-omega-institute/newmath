import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactFiniteSubsequenceObligation [AskSetup] [PackageSetup]
    {compact baire stream window regular realSeal transport replay provenance localName
      sourceRead subsequenceRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier compact baire stream window regular realSeal transport replay
        provenance localName bundle pkg →
      Cont compact stream sourceRead →
        Cont sourceRead window subsequenceRead →
          Cont subsequenceRead localName namedRead →
            PkgSig bundle namedRead pkg →
              UnaryHistory compact ∧ UnaryHistory stream ∧ UnaryHistory window ∧
                UnaryHistory sourceRead ∧ UnaryHistory subsequenceRead ∧
                  UnaryHistory namedRead ∧ Cont compact stream sourceRead ∧
                    Cont sourceRead window subsequenceRead ∧
                      Cont subsequenceRead localName namedRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sourceRoute subsequenceRoute namedRoute namedPkg
  obtain ⟨compactUnary, _baireUnary, streamUnary, windowUnary, _regularUnary,
    _realSealUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed compactUnary streamUnary sourceRoute
  have subsequenceUnary : UnaryHistory subsequenceRead :=
    unary_cont_closed sourceUnary windowUnary subsequenceRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed subsequenceUnary localNameUnary namedRoute
  exact
    ⟨compactUnary, streamUnary, windowUnary, sourceUnary, subsequenceUnary, namedUnary,
      sourceRoute, subsequenceRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.SequentialCompactUp
