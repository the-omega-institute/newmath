import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations

namespace BEDC.Derived.BolzanoweierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassClusterSourceFormalTarget [AskSetup] [PackageSetup]
    {boundedSource intervalNet regularSubsequence rationalReadback clusterSeal provenance :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory boundedSource →
      UnaryHistory clusterSeal →
        Cont boundedSource intervalNet regularSubsequence →
          Cont regularSubsequence rationalReadback clusterSeal →
            PkgSig bundle provenance pkg →
              ∃ clusterRoute : BHist,
                UnaryHistory clusterRoute ∧ hsame clusterRoute (append boundedSource clusterSeal) ∧
                  Cont boundedSource intervalNet regularSubsequence ∧
                    Cont regularSubsequence rationalReadback clusterSeal ∧
                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame
  intro boundedUnary clusterUnary sourceInterval regularReadbackCluster provenancePkg
  refine Exists.intro (append boundedSource clusterSeal) ?_
  exact
    ⟨unary_append_closed boundedUnary clusterUnary,
      hsame_refl (append boundedSource clusterSeal), sourceInterval, regularReadbackCluster,
      provenancePkg⟩

end BEDC.Derived.BolzanoweierstrassUp
