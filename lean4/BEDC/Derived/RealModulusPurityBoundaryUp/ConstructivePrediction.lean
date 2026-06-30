import BEDC.Derived.RealModulusPurityBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealModulusPurityBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealModulusPurityBoundary_constructive_prediction [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB predicted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] ->
      Cont D S R0 ->
        Cont R0 L routeRL ->
          Cont routeRL B routeLB ->
            Cont routeLB H predicted ->
              UnaryHistory D ->
                UnaryHistory S ->
                  UnaryHistory L ->
                    UnaryHistory B ->
                      UnaryHistory H ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle predicted pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row predicted ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row D ∨ hsame row S ∨ hsame row R0 ∨
                                    hsame row L ∨ hsame row B ∨ hsame row H ∨
                                      hsame row predicted)
                                (fun row : BHist =>
                                  hsame row predicted ∧ Cont D S R0 ∧
                                    Cont R0 L routeRL ∧ Cont routeRL B routeLB ∧
                                      Cont routeLB H predicted ∧
                                        PkgSig bundle predicted pkg)
                                hsame ∧
                              UnaryHistory predicted := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _fields routeR0 routeRLCont routeLBCont predictedCont unaryD unaryS unaryL
    unaryB unaryH _provenancePkg predictedPkg
  have unaryR0 : UnaryHistory R0 :=
    unary_cont_closed unaryD unaryS routeR0
  have unaryRouteRL : UnaryHistory routeRL :=
    unary_cont_closed unaryR0 unaryL routeRLCont
  have unaryRouteLB : UnaryHistory routeLB :=
    unary_cont_closed unaryRouteRL unaryB routeLBCont
  have predictedUnary : UnaryHistory predicted :=
    unary_cont_closed unaryRouteLB unaryH predictedCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row predicted ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row predicted)
          (fun row : BHist =>
            hsame row predicted ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                PkgSig bundle predicted pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro predicted ⟨hsame_refl predicted, predictedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeR0, routeRLCont, routeLBCont, predictedCont, predictedPkg⟩
  }
  exact ⟨cert, predictedUnary⟩

end BEDC.Derived.RealModulusPurityBoundaryUp
