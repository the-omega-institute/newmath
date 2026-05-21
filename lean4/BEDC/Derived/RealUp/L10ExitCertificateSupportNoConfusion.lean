import BEDC.Derived.RealUp.L10DependencyLattice

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10ExitCertificateSupportNoConfusion [AskSetup] [PackageSetup]
    {dyadicFace streamFace regSeqFace localReal support route endpoint endpoint' nameCert :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadicFace →
      UnaryHistory streamFace →
        UnaryHistory regSeqFace →
          UnaryHistory localReal →
            UnaryHistory support →
              Cont dyadicFace streamFace regSeqFace →
                Cont regSeqFace localReal route →
                  Cont route support endpoint →
                    Cont route support endpoint' →
                      hsame nameCert endpoint →
                        PkgSig bundle endpoint pkg →
                          PkgSig bundle endpoint' pkg →
                            hsame endpoint endpoint' ∧ UnaryHistory route ∧
                              UnaryHistory endpoint ∧ UnaryHistory endpoint' ∧
                                Cont dyadicFace streamFace regSeqFace ∧
                                  Cont regSeqFace localReal route ∧
                                    Cont route support endpoint ∧
                                      Cont route support endpoint' ∧
                                        hsame nameCert endpoint ∧
                                          PkgSig bundle endpoint pkg ∧
                                            PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro _dyadicUnary _streamUnary regSeqUnary localRealUnary supportUnary
    dyadicStreamRoute regSeqRealRoute endpointRoute endpointRoute' nameCertSame
    endpointPkg endpointPkg'
  have routeUnary : UnaryHistory route :=
    unary_cont_closed regSeqUnary localRealUnary regSeqRealRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary supportUnary endpointRoute
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed routeUnary supportUnary endpointRoute'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_deterministic endpointRoute endpointRoute'
  exact
    ⟨sameEndpoint, routeUnary, endpointUnary, endpointUnary', dyadicStreamRoute,
      regSeqRealRoute, endpointRoute, endpointRoute', nameCertSame, endpointPkg,
      endpointPkg'⟩

end BEDC.Derived.RealUp
