import BEDC.Derived.RealUp.L10CurrentPhaseExitLocalThreshold

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10ObjectwiseExitThresholdEquivalence [AskSetup] [PackageSetup]
    {dyadicFace streamFace regSeqFace localReal support route endpoint nameCert statusRead
      targetRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadicFace ->
      UnaryHistory streamFace ->
        UnaryHistory regSeqFace ->
          UnaryHistory localReal ->
            UnaryHistory support ->
              Cont dyadicFace streamFace regSeqFace ->
                Cont regSeqFace localReal route ->
                  Cont route support endpoint ->
                    hsame nameCert endpoint ->
                      PkgSig bundle endpoint pkg ->
                        PkgSig bundle statusRead pkg ->
                          PkgSig bundle targetRead pkg ->
                            PkgSig bundle bridgeRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                                  (fun row : BHist => hsame row endpoint)
                                  (fun row : BHist =>
                                    hsame row endpoint ∧ Cont route support endpoint)
                                  hsame ∧
                                UnaryHistory route ∧ UnaryHistory endpoint ∧
                                  Cont dyadicFace streamFace regSeqFace ∧
                                    Cont regSeqFace localReal route ∧
                                      Cont route support endpoint ∧ hsame nameCert endpoint ∧
                                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert
  intro dyadicUnary streamUnary regSeqUnary localRealUnary supportUnary dyadicStreamRoute
    realRoute endpointRoute sameName endpointPkg _statusPkg _targetPkg _bridgePkg
  exact
    RealL10CurrentPhaseExitLocalThreshold
      dyadicUnary
      streamUnary
      regSeqUnary
      localRealUnary
      supportUnary
      dyadicStreamRoute
      realRoute
      endpointRoute
      sameName
      endpointPkg

end BEDC.Derived.RealUp
