import BEDC.Derived.HeineBorelIntervalUp.NetInduction
import BEDC.Derived.HeineBorelIntervalUp.TailStability

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HeineBorelIntervalMeshRefinementFunctoriality [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N net mesh coverageRead stableRead inductionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net mesh coverageRead bundle pkg →
      UnaryHistory T →
        Cont coverageRead T stableRead →
          PkgSig bundle stableRead pkg →
            HeineBorelIntervalFiniteNetInductionRoute
                (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                stableRead inductionRead bundle pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row)
                    (fun row : BHist => hsame row stableRead ∨ hsame row inductionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont coverageRead T stableRead ∧
                        HeineBorelIntervalFiniteNetInductionRoute
                          (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                          stableRead inductionRead bundle pkg)
                    hsame ∧
                UnaryHistory inductionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro coverageRoute tailUnary coverageTailStable stablePkg inductionRoute
  obtain ⟨kUnary, mUnary, zUnary, fUnary, qUnary, cUnary, pUnary, nUnary,
    netRoute, coverageThroughMesh, finiteCoverageRoute, replayRoute, meshSameM, coveragePkg⟩ :=
    coverageRoute
  have coverageThroughM : Cont net M coverageRead := by
    cases meshSameM
    exact coverageThroughMesh
  have coverageRouteForTail :
      HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        net M coverageRead bundle pkg :=
    ⟨kUnary, mUnary, zUnary, fUnary, qUnary, cUnary, pUnary, nUnary, netRoute,
      coverageThroughM, finiteCoverageRoute, replayRoute, hsame_refl M, coveragePkg⟩
  have stableResult :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row coverageRead ∨ hsame row T ∨ hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              PkgSig bundle stableRead pkg)
          hsame ∧
        UnaryHistory stableRead :=
    HeineBorelIntervalTailStability coverageRouteForTail tailUnary coverageTailStable stablePkg
  have stableUnary : UnaryHistory stableRead := stableResult.right
  obtain ⟨inductionZUnary, inductionFUnary, inductionCUnary, inductionPUnary,
    inductionNUnary, stableInduction, finiteReplay, packageReplay, inductionPkg⟩ :=
    inductionRoute
  have inductionUnary : UnaryHistory inductionRead :=
    unary_cont_closed stableUnary inductionZUnary stableInduction
  have inductionRouteHere :
      HeineBorelIntervalFiniteNetInductionRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        stableRead inductionRead bundle pkg :=
    ⟨inductionZUnary, inductionFUnary, inductionCUnary, inductionPUnary, inductionNUnary,
      stableInduction, finiteReplay, packageReplay, inductionPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row inductionRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row stableRead ∨ hsame row inductionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              HeineBorelIntervalFiniteNetInductionRoute
                (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
                stableRead inductionRead bundle pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro inductionRead
        ⟨hsame_refl inductionRead, inductionUnary⟩
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
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverageTailStable, inductionRouteHere⟩
  }
  exact ⟨cert, inductionUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
