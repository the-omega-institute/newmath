import BEDC.Derived.HaltingDistinctionUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.HaltingDistinctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HaltingDistinctionRootSiblingConsumerLock [AskSetup] [PackageSetup]
    {question trace diagonal halt classifier route provenance cert traceRead inscriptionRead
      normalRead siblingRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HaltingDistinctionCarrier question trace diagonal halt classifier route provenance cert
        bundle pkg ->
      Cont trace route traceRead ->
        Cont diagonal halt inscriptionRead ->
          Cont traceRead inscriptionRead normalRead ->
            Cont normalRead classifier siblingRead ->
              PkgSig bundle siblingRead pkg ->
                UnaryHistory trace ∧ UnaryHistory diagonal ∧ UnaryHistory traceRead ∧
                  UnaryHistory inscriptionRead ∧ UnaryHistory normalRead ∧
                    UnaryHistory siblingRead ∧ Cont trace route traceRead ∧
                      Cont diagonal halt inscriptionRead ∧
                        Cont traceRead inscriptionRead normalRead ∧
                          Cont normalRead classifier siblingRead ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle siblingRead pkg ∧
                                (Cont siblingRead (BHist.e0 hostTail) normalRead ->
                                  False) := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro carrier traceRouteRead diagonalHaltInscription traceInscriptionNormal
    normalClassifierSibling siblingPkg
  obtain ⟨_questionUnary, traceUnary, diagonalUnary, haltUnary, classifierUnary,
    routeUnary, _provenanceUnary, _certUnary, _questionTraceDiagonal,
    _diagonalHaltClassifier, _classifierRouteCert, provenancePkg⟩ := carrier
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed traceUnary routeUnary traceRouteRead
  have inscriptionReadUnary : UnaryHistory inscriptionRead :=
    unary_cont_closed diagonalUnary haltUnary diagonalHaltInscription
  have normalReadUnary : UnaryHistory normalRead :=
    unary_cont_closed traceReadUnary inscriptionReadUnary traceInscriptionNormal
  have siblingReadUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalReadUnary classifierUnary normalClassifierSibling
  exact
    ⟨traceUnary, diagonalUnary, traceReadUnary, inscriptionReadUnary, normalReadUnary,
      siblingReadUnary, traceRouteRead, diagonalHaltInscription, traceInscriptionNormal,
      normalClassifierSibling, provenancePkg, siblingPkg,
      fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left normalClassifierSibling hostReturn⟩

end BEDC.Derived.HaltingDistinctionUp
