import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ProjectiveVarZeroLocusPackage [AskSetup] [PackageSetup]
    (chart homogeneous projective zeroEval endpoint : BHist)
    (chartBundle homogeneousBundle projectiveBundle zeroBundle : ProbeBundle ProbeName)
    (chartPkg homogeneousPkg projectivePkg zeroPkg : Pkg) : Prop :=
  UnaryHistory chart ∧ UnaryHistory homogeneous ∧ UnaryHistory projective ∧
    Cont chart homogeneous projective ∧ Cont projective zeroEval endpoint ∧
      PkgSig chartBundle chart chartPkg ∧ PkgSig homogeneousBundle homogeneous homogeneousPkg ∧
        PkgSig projectiveBundle projective projectivePkg ∧
          PkgSig zeroBundle zeroEval zeroPkg

theorem ProjectiveVarZeroLocusPackage_hsame_transport [AskSetup] [PackageSetup]
    {chart homogeneous projective zeroEval endpoint chart' homogeneous' projective' zeroEval'
      endpoint' : BHist}
    {chartBundle homogeneousBundle projectiveBundle zeroBundle : ProbeBundle ProbeName}
    {chartPkg homogeneousPkg projectivePkg zeroPkg : Pkg} :
    ProjectiveVarZeroLocusPackage chart homogeneous projective zeroEval endpoint chartBundle
        homogeneousBundle projectiveBundle zeroBundle chartPkg homogeneousPkg projectivePkg
        zeroPkg ->
      hsame chart chart' -> hsame homogeneous homogeneous' -> hsame zeroEval zeroEval' ->
        PkgSig chartBundle chart' chartPkg ->
          PkgSig homogeneousBundle homogeneous' homogeneousPkg ->
            PkgSig projectiveBundle projective' projectivePkg ->
              PkgSig zeroBundle zeroEval' zeroPkg ->
                Cont chart' homogeneous' projective' ->
                  Cont projective' zeroEval' endpoint' ->
                    ProjectiveVarZeroLocusPackage chart' homogeneous' projective' zeroEval'
                        endpoint' chartBundle homogeneousBundle projectiveBundle zeroBundle
                        chartPkg homogeneousPkg projectivePkg zeroPkg ∧
                      hsame endpoint endpoint' := by
  intro pkg sameChart sameHomogeneous sameZeroEval chartPkg' homogeneousPkg' projectivePkg'
    zeroPkg' projectiveCont' endpointCont'
  have chartUnary' : UnaryHistory chart' :=
    unary_transport pkg.left sameChart
  have homogeneousUnary' : UnaryHistory homogeneous' :=
    unary_transport pkg.right.left sameHomogeneous
  have sameProjective : hsame projective projective' :=
    cont_respects_hsame sameChart sameHomogeneous pkg.right.right.right.left projectiveCont'
  have projectiveUnary' : UnaryHistory projective' :=
    unary_transport pkg.right.right.left sameProjective
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameProjective sameZeroEval pkg.right.right.right.right.left endpointCont'
  exact And.intro
    (And.intro chartUnary'
      (And.intro homogeneousUnary'
        (And.intro projectiveUnary'
          (And.intro projectiveCont'
            (And.intro endpointCont'
              (And.intro chartPkg'
                (And.intro homogeneousPkg' (And.intro projectivePkg' zeroPkg'))))))))
    sameEndpoint

end BEDC.Derived.ProjectiveVarUp
