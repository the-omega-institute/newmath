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

theorem RealModulusPurityBoundary_namecert_obligations [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] ->
      Cont D S R0 ->
        Cont R0 L routeRL ->
          Cont routeRL B routeLB ->
            Cont routeLB N consumer ->
              UnaryHistory D ->
                UnaryHistory S ->
                  UnaryHistory L ->
                    UnaryHistory B ->
                      UnaryHistory N ->
                        PkgSig bundle N pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row consumer ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
                                  Cont routeRL B routeLB ∧ Cont routeLB N consumer)
                              (fun row : BHist => hsame row consumer ∧ PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory R0 ∧ UnaryHistory routeRL ∧
                              UnaryHistory routeLB ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro _fields routeR0 routeRLCont routeLBCont consumerCont unaryD unaryS unaryL unaryB
    unaryN namePkg
  have unaryR0 : UnaryHistory R0 :=
    unary_cont_closed unaryD unaryS routeR0
  have unaryRouteRL : UnaryHistory routeRL :=
    unary_cont_closed unaryR0 unaryL routeRLCont
  have unaryRouteLB : UnaryHistory routeLB :=
    unary_cont_closed unaryRouteRL unaryB routeLBCont
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unaryRouteLB unaryN consumerCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row consumer ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
            Cont routeRL B routeLB ∧ Cont routeLB N consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, unaryConsumer⟩
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
      exact ⟨source.left, routeR0, routeRLCont, routeLBCont, consumerCont⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact ⟨cert, unaryR0, unaryRouteRL, unaryRouteLB, unaryConsumer⟩

theorem RealModulusPurityBoundary_nonescape [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB consumer leaked : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] ->
      Cont D S R0 ->
        Cont R0 L routeRL ->
          Cont routeRL B routeLB ->
            Cont routeLB N consumer ->
              UnaryHistory D ->
                UnaryHistory S ->
                  UnaryHistory L ->
                    UnaryHistory B ->
                      UnaryHistory N ->
                        PkgSig bundle N pkg ->
                          hsame leaked consumer ->
                            UnaryHistory leaked ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro _fields routeR0 routeRLCont routeLBCont consumerCont unaryD unaryS unaryL unaryB
    unaryN namePkg leakedSame
  have unaryR0 : UnaryHistory R0 :=
    unary_cont_closed unaryD unaryS routeR0
  have unaryRouteRL : UnaryHistory routeRL :=
    unary_cont_closed unaryR0 unaryL routeRLCont
  have unaryRouteLB : UnaryHistory routeLB :=
    unary_cont_closed unaryRouteRL unaryB routeLBCont
  have unaryConsumer : UnaryHistory consumer :=
    unary_cont_closed unaryRouteLB unaryN consumerCont
  exact ⟨unary_transport unaryConsumer (hsame_symm leakedSame), namePkg⟩

end BEDC.Derived.RealModulusPurityBoundaryUp
