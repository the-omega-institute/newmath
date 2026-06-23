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

theorem RealModulusPurityBoundary_scope_package [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB consumer refusalRead predicted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] ->
      Cont D S R0 ->
        Cont R0 L routeRL ->
          Cont routeRL B routeLB ->
            Cont routeLB N consumer ->
              Cont B N refusalRead ->
                Cont routeLB H predicted ->
                  UnaryHistory D ->
                    UnaryHistory S ->
                      UnaryHistory L ->
                        UnaryHistory B ->
                          UnaryHistory H ->
                            UnaryHistory N ->
                              PkgSig bundle N pkg ->
                                PkgSig bundle refusalRead pkg ->
                                  PkgSig bundle predicted pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row consumer ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row D ∨ hsame row S ∨ hsame row R0 ∨
                                            hsame row L ∨ hsame row B ∨ hsame row H ∨
                                              hsame row consumer)
                                        (fun row : BHist =>
                                          hsame row consumer ∧ Cont D S R0 ∧
                                            Cont R0 L routeRL ∧ Cont routeRL B routeLB ∧
                                              Cont routeLB N consumer ∧
                                                PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory consumer ∧ UnaryHistory refusalRead ∧
                                        UnaryHistory predicted := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _fields routeR0 routeRLCont routeLBCont consumerCont refusalCont predictedCont
    unaryD unaryS unaryL unaryB unaryH unaryN namePkg _refusalPkg _predictedPkg
  have unaryR0 : UnaryHistory R0 :=
    unary_cont_closed unaryD unaryS routeR0
  have unaryRouteRL : UnaryHistory routeRL :=
    unary_cont_closed unaryR0 unaryL routeRLCont
  have unaryRouteLB : UnaryHistory routeLB :=
    unary_cont_closed unaryRouteRL unaryB routeLBCont
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unaryRouteLB unaryN consumerCont
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryB unaryN refusalCont
  have unaryPredicted : UnaryHistory predicted :=
    unary_cont_closed unaryRouteLB unaryH predictedCont
  have sourceConsumer :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, unaryConsumer⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row consumer)
          (fun row : BHist =>
            hsame row consumer ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB N consumer ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer sourceConsumer
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, routeR0, routeRLCont, routeLBCont, consumerCont, namePkg⟩
  }
  exact ⟨cert, unaryConsumer, unaryRefusal, unaryPredicted⟩

end BEDC.Derived.RealModulusPurityBoundaryUp
