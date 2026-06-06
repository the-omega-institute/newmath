import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootCarrier_rows_exposed [AskSetup] [PackageSetup]
    {X F E W R O H C P N rootRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory F →
          Cont X F rootRead →
            PkgSig bundle P pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist => hsame row X ∨ hsame row F ∨ hsame row rootRead)
                  (fun row : BHist => PkgSig bundle P pkg ∧ hsame row rootRead)
                  hsame ∧
                UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields xUnary fUnary rootRoute provenancePkg
  have _acceptedFields :
      lowerSemicontinuousRootFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, E, W, R, O, H, C, P, N] := fields
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed xUnary fUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row X ∨ hsame row F ∨ hsame row rootRead)
          (fun row : BHist => PkgSig bundle P pkg ∧ hsame row rootRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
      exact ⟨provenancePkg, source.left⟩
  }
  exact ⟨cert, rootUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
