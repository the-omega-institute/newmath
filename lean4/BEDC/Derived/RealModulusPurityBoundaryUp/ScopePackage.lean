import BEDC.Derived.RealModulusPurityBoundaryUp.ConstructivePrediction
import BEDC.Derived.RealModulusPurityBoundaryUp.NameCertObligations
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

theorem RealModulusPurityBoundaryScopePackage [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB predicted consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] →
      Cont D S R0 →
        Cont R0 L routeRL →
          Cont routeRL B routeLB →
            Cont routeLB H predicted →
              Cont routeLB N consumer →
                UnaryHistory D →
                  UnaryHistory S →
                    UnaryHistory L →
                      UnaryHistory B →
                        UnaryHistory H →
                          UnaryHistory N →
                            PkgSig bundle P pkg →
                              PkgSig bundle N pkg →
                                PkgSig bundle predicted pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row predicted ∨ hsame row consumer) ∧
                                          UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row D ∨ hsame row S ∨ hsame row R0 ∨
                                          hsame row L ∨ hsame row B ∨ hsame row H ∨
                                            hsame row N ∨ hsame row predicted ∨
                                              hsame row consumer)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont D S R0 ∧
                                          Cont R0 L routeRL ∧ Cont routeRL B routeLB ∧
                                            Cont routeLB H predicted ∧
                                              Cont routeLB N consumer ∧
                                                PkgSig bundle P pkg)
                                      hsame ∧
                                    UnaryHistory routeRL ∧ UnaryHistory routeLB ∧
                                      UnaryHistory predicted ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fields routeR0 routeRLCont routeLBCont predictedCont consumerCont unaryD unaryS
    unaryL unaryB unaryH unaryN provenancePkg namePkg predictedPkg
  have predictionResult :
      SemanticNameCert
          (fun row : BHist => hsame row predicted ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row predicted)
          (fun row : BHist =>
            hsame row predicted ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                PkgSig bundle predicted pkg)
          hsame ∧
        UnaryHistory predicted :=
    RealModulusPurityBoundary_constructive_prediction
      fields routeR0 routeRLCont routeLBCont predictedCont unaryD unaryS unaryL
      unaryB unaryH provenancePkg predictedPkg
  have obligationResult :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row consumer ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB N consumer)
          (fun row : BHist => hsame row consumer ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory R0 ∧ UnaryHistory routeRL ∧ UnaryHistory routeLB ∧
          UnaryHistory consumer :=
    RealModulusPurityBoundary_namecert_obligations
      fields routeR0 routeRLCont routeLBCont consumerCont unaryD unaryS unaryL unaryB
      unaryN namePkg
  obtain ⟨_predictionCert, predictedUnary⟩ := predictionResult
  obtain ⟨_obligationCert, _unaryR0, routeRLUnary, routeLBUnary, consumerUnary⟩ :=
    obligationResult
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row predicted ∨ hsame row consumer) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row N ∨ hsame row predicted ∨ hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                Cont routeLB N consumer ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro predicted
        ⟨Or.inl (hsame_refl predicted), predictedUnary⟩
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
        constructor
        · cases source.left with
          | inl predictedSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) predictedSame)
          | inr consumerSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) consumerSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl predictedSame =>
          exact
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inl predictedSame)))))))
      | inr consumerSame =>
          exact
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr consumerSame)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeR0, routeRLCont, routeLBCont, predictedCont, consumerCont,
          provenancePkg⟩
  }
  exact ⟨cert, routeRLUnary, routeLBUnary, predictedUnary, consumerUnary⟩

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
