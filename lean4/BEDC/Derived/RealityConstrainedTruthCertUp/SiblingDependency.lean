import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RealityConstrainedTruthCertSiblingDependency [AskSetup] [PackageSetup]
    {S Sigma K T U D I L F N openFitRead invariantRead explanationRead inductionRead
      compressionRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont S Sigma openFitRead ->
      Cont I K invariantRead ->
        Cont openFitRead D explanationRead ->
          Cont T U inductionRead ->
            Cont compressionRead L exportRead ->
              PkgSig bundle exportRead pkg ->
                TasteGate.realityConstrainedTruthCertFields
                    (TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N) =
                  [S, Sigma, K, T, U, D, I, L, F, N] /\
                Cont S Sigma openFitRead /\
                  Cont I K invariantRead /\
                    Cont openFitRead D explanationRead /\
                      Cont T U inductionRead /\
                        Cont compressionRead L exportRead /\
                          PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig
  intro openFitRoute invariantRoute explanationRoute inductionRoute compressionRoute exportPkg
  exact
    ⟨rfl, openFitRoute, invariantRoute, explanationRoute, inductionRoute,
      compressionRoute, exportPkg⟩

end BEDC.Derived.RealityConstrainedTruthCertUp
