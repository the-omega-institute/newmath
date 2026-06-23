import BEDC.Derived.HeineBorelIntervalUp.PublicFiniteNetExport
import BEDC.Derived.HeineBorelIntervalUp.RealSealDescent

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HeineBorelIntervalRealCompletionFacingRoute [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N net mesh coverageRead stableRead inductionRead sealRead
      publicRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net mesh coverageRead bundle pkg →
      UnaryHistory T →
        UnaryHistory E →
          UnaryHistory N →
            UnaryHistory R →
              Cont coverageRead T stableRead →
                HeineBorelIntervalFiniteNetInductionRoute
                    (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                    stableRead inductionRead bundle pkg →
                  Cont inductionRead E sealRead →
                    Cont sealRead N publicRead →
                      Cont publicRead R completionRead →
                        PkgSig bundle stableRead pkg →
                          PkgSig bundle sealRead pkg →
                            PkgSig bundle publicRead pkg →
                              PkgSig bundle completionRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row completionRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row coverageRead ∨ hsame row stableRead ∨
                                        hsame row inductionRead ∨ hsame row sealRead ∨
                                          hsame row publicRead ∨ hsame row completionRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont coverageRead T stableRead ∧
                                        Cont inductionRead E sealRead ∧
                                          Cont sealRead N publicRead ∧
                                            Cont publicRead R completionRead ∧
                                              PkgSig bundle completionRead pkg)
                                    hsame ∧
                                  UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro coverageRouteSource tailUnary eUnary nUnary rUnary coverageTailStable inductionRoute
    inductionSeal sealPublic publicCompletion stablePkg sealPkg publicPkg completionPkg
  have coverageRoute :
      HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net mesh coverageRead bundle pkg :=
    coverageRouteSource
  have _coverageResult :
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row net ∨ hsame row mesh ∨ hsame row coverageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont net mesh coverageRead ∧
              PkgSig bundle coverageRead pkg)
          hsame ∧
        UnaryHistory coverageRead :=
    HeineBorelIntervalNetCoverage
      (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
      coverageRoute
  obtain ⟨kUnary, mUnary, zUnary, fUnary, qUnary, cUnary, pUnary, nUnary,
    netRoute, coverageThroughMesh, finiteCoverageRoute, replayRoute, meshSameM,
    coveragePkg⟩ := coverageRouteSource
  have coverageThroughM : Cont net M coverageRead := by
    cases meshSameM
    exact coverageThroughMesh
  have coverageRouteForTail :
      HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net M coverageRead bundle pkg :=
    ⟨kUnary, mUnary, zUnary, fUnary, qUnary, cUnary, pUnary, nUnary, netRoute,
      coverageThroughM, finiteCoverageRoute, replayRoute, hsame_refl M, coveragePkg⟩
  have _tailResult :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row coverageRead ∨ hsame row T ∨ hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              PkgSig bundle stableRead pkg)
          hsame ∧
        UnaryHistory stableRead :=
    HeineBorelIntervalTailStability coverageRouteForTail tailUnary coverageTailStable stablePkg
  have publicResult :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row stableRead ∨ hsame row inductionRead ∨
              hsame row sealRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              Cont inductionRead E sealRead ∧ Cont sealRead N publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame ∧
        UnaryHistory stableRead ∧ UnaryHistory inductionRead ∧ UnaryHistory sealRead ∧
          UnaryHistory publicRead :=
    HeineBorelIntervalNameCertObligationSurface
      coverageRoute tailUnary eUnary nUnary coverageTailStable inductionRoute
      inductionSeal sealPublic stablePkg sealPkg publicPkg
  have publicUnary : UnaryHistory publicRead := publicResult.right.right.right.right
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed publicUnary rUnary publicCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row stableRead ∨ hsame row inductionRead ∨
              hsame row sealRead ∨ hsame row publicRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              Cont inductionRead E sealRead ∧ Cont sealRead N publicRead ∧
                Cont publicRead R completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverageTailStable, inductionSeal, sealPublic, publicCompletion,
          completionPkg⟩
  }
  exact ⟨cert, completionUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
