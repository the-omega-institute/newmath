import BEDC.Derived.HaltingDistinctionUp

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionInscriptionEventHandoff [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert eventRead supportRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg →
      Cont diagonal route eventRead →
        Cont eventRead provenance supportRead →
          PkgSig bundle supportRead pkg →
            UnaryHistory diagonal ∧ UnaryHistory eventRead ∧ UnaryHistory supportRead ∧
              Cont diagonal route eventRead ∧ Cont eventRead provenance supportRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle supportRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier diagonalRouteEvent eventProvenanceSupport supportPkg
  obtain ⟨_questionUnary, _traceUnary, diagonalUnary, _haltUnary, _classifierUnary,
    routeUnary, provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have eventUnary : UnaryHistory eventRead :=
    unary_cont_closed diagonalUnary routeUnary diagonalRouteEvent
  have supportUnary : UnaryHistory supportRead :=
    unary_cont_closed eventUnary provenanceUnary eventProvenanceSupport
  exact
    ⟨diagonalUnary, eventUnary, supportUnary, diagonalRouteEvent, eventProvenanceSupport,
      provenancePkg, supportPkg⟩

end BEDC.Derived.HaltingDistinctionUp
