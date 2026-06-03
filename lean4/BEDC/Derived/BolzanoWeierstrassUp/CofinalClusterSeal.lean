import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassCarrier_cofinal_cluster_seal [AskSetup] [PackageSetup]
    {source intervalNet cofinal readback sealRow transport replay provenance name streamRead
      dyadicRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier source intervalNet cofinal readback sealRow transport replay
        provenance name bundle pkg →
      Cont cofinal readback streamRead →
        Cont streamRead provenance dyadicRead →
          Cont dyadicRead sealRow realRead →
            PkgSig bundle realRead pkg →
              UnaryHistory cofinal ∧ UnaryHistory readback ∧ UnaryHistory streamRead ∧
                UnaryHistory dyadicRead ∧ UnaryHistory realRead ∧
                  Cont cofinal readback streamRead ∧
                    Cont streamRead provenance dyadicRead ∧
                      Cont dyadicRead sealRow realRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier streamRoute dyadicRoute realRoute realPkg
  obtain ⟨_sourceUnary, _intervalNetUnary, cofinalUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _sourceIntervalRoute,
    _cofinalReadbackSeal, _transportReplayProvenance, provenancePkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed cofinalUnary readbackUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed streamUnary provenanceUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary sealUnary realRoute
  exact
    ⟨cofinalUnary, readbackUnary, streamUnary, dyadicUnary, realUnary, streamRoute,
      dyadicRoute, realRoute, provenancePkg, realPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
