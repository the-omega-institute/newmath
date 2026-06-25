import BEDC.Derived.HeineBorelIntervalUp.TasteGate

namespace BEDC.Derived.HeineBorelIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem HeineBorelIntervalTailStability [AskSetup] [PackageSetup]
    {A B K M Z F T S R E Q C P N mesh coverageRead stableRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HeineBorelIntervalCoverageRoute
        (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
        mesh M coverageRead bundle pkg →
      UnaryHistory T →
        Cont coverageRead T stableRead →
          PkgSig bundle stableRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row coverageRead ∨ hsame row T ∨ hsame row stableRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont coverageRead T stableRead ∧
                    PkgSig bundle stableRead pkg)
                hsame ∧
              UnaryHistory stableRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro coverageRoute tailUnary coverageTailStable stablePkg
  have coverageResult :
      SemanticNameCert
          (fun row : BHist => hsame row coverageRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row mesh ∨ hsame row M ∨ hsame row coverageRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont mesh M coverageRead ∧ PkgSig bundle coverageRead pkg)
          hsame ∧
        UnaryHistory coverageRead :=
    HeineBorelIntervalNetCoverage
      (HeineBorelIntervalUp.mk A B K M Z F T S R E Q C P N)
      coverageRoute
  have coverageUnary : UnaryHistory coverageRead := coverageResult.right
  have stableUnary : UnaryHistory stableRead :=
    unary_cont_closed coverageUnary tailUnary coverageTailStable
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stableRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row coverageRead ∨ hsame row T ∨ hsame row stableRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont coverageRead T stableRead ∧
              PkgSig bundle stableRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stableRead ⟨hsame_refl stableRead, stableUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverageTailStable, stablePkg⟩
  }
  exact ⟨cert, stableUnary⟩

end BEDC.Derived.HeineBorelIntervalUp
