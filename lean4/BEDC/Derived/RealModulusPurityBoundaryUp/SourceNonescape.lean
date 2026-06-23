import BEDC.Derived.RealModulusPurityBoundaryUp.TailBudgetExhaustion

namespace BEDC.Derived.RealModulusPurityBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealModulusPurityBoundarySourceNonescape [AskSetup] [PackageSetup]
    {x : RealModulusPurityBoundaryUp}
    {D S R0 L B H C P N routeRL routeLB predicted consumer tailRead sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realModulusPurityBoundaryFields x = [D, S, R0, L, B, H, C, P, N] →
      Cont D S R0 →
        Cont R0 L routeRL →
          Cont routeRL B routeLB →
            Cont routeLB H predicted →
              Cont routeLB N consumer →
                Cont consumer B tailRead →
                  Cont tailRead N sourceRead →
                    UnaryHistory D →
                      UnaryHistory S →
                        UnaryHistory L →
                          UnaryHistory B →
                            UnaryHistory H →
                              UnaryHistory N →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    PkgSig bundle predicted pkg →
                                      PkgSig bundle tailRead pkg →
                                        PkgSig bundle sourceRead pkg →
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row sourceRead ∧ UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row D ∨ hsame row S ∨
                                                  hsame row R0 ∨ hsame row L ∨
                                                    hsame row B ∨ hsame row H ∨
                                                      hsame row N ∨ hsame row predicted ∨
                                                        hsame row consumer ∨
                                                          hsame row tailRead ∨
                                                            hsame row sourceRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont D S R0 ∧
                                                  Cont R0 L routeRL ∧
                                                    Cont routeRL B routeLB ∧
                                                      Cont routeLB H predicted ∧
                                                        Cont routeLB N consumer ∧
                                                          Cont consumer B tailRead ∧
                                                            Cont tailRead N sourceRead ∧
                                                              PkgSig bundle sourceRead pkg)
                                              hsame ∧
                                            UnaryHistory tailRead ∧ UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fields routeR0 routeRLCont routeLBCont predictedCont consumerCont consumerTail
    tailSource unaryD unaryS unaryL unaryB unaryH unaryN provenancePkg namePkg predictedPkg
    tailPkg sourcePkg
  have tailResult :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row predicted ∨ hsame row consumer ∨ hsame row tailRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row N ∨ hsame row predicted ∨ hsame row consumer ∨
                hsame row tailRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                Cont routeLB N consumer ∧ Cont consumer B tailRead ∧ PkgSig bundle P pkg)
          hsame ∧
        UnaryHistory tailRead :=
    RealModulusPurityBoundaryTailBudgetExhaustion
      fields routeR0 routeRLCont routeLBCont predictedCont consumerCont consumerTail
      unaryD unaryS unaryL unaryB unaryH unaryN provenancePkg namePkg predictedPkg tailPkg
  have tailUnary : UnaryHistory tailRead := tailResult.right
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed tailUnary unaryN tailSource
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row S ∨ hsame row R0 ∨ hsame row L ∨ hsame row B ∨
              hsame row H ∨ hsame row N ∨ hsame row predicted ∨ hsame row consumer ∨
                hsame row tailRead ∨ hsame row sourceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D S R0 ∧ Cont R0 L routeRL ∧
              Cont routeRL B routeLB ∧ Cont routeLB H predicted ∧
                Cont routeLB N consumer ∧ Cont consumer B tailRead ∧
                  Cont tailRead N sourceRead ∧ PkgSig bundle sourceRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead
        ⟨hsame_refl sourceRead, sourceUnary⟩
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeR0, routeRLCont, routeLBCont, predictedCont, consumerCont,
          consumerTail, tailSource, sourcePkg⟩
  }
  exact ⟨cert, tailUnary, sourceUnary⟩

end BEDC.Derived.RealModulusPurityBoundaryUp
