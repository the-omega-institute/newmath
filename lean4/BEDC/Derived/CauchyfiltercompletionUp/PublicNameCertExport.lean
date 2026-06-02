import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyFilterCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPublicNameCert_export [AskSetup] [PackageSetup]
    {C W T R L H K P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory W →
        UnaryHistory T →
          UnaryHistory R →
            UnaryHistory L →
              UnaryHistory H →
                UnaryHistory K →
                  Cont C W T →
                    Cont T R L →
                      Cont L H publicRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row C ∨ hsame row W ∨ hsame row T ∨ hsame row R ∨
                                    hsame row L ∨ hsame row H ∨ hsame row K ∨
                                      hsame row publicRead)
                                (fun row : BHist =>
                                  hsame row publicRead ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro cUnary wUnary _tUnary rUnary _lUnary hUnary _kUnary cWRoute tRRoute publicRoute
    provenancePkg namePkg
  have routeTUnary : UnaryHistory T :=
    unary_cont_closed cUnary wUnary cWRoute
  have routeLUnary : UnaryHistory L :=
    unary_cont_closed routeTUnary rUnary tRRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeLUnary hUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row W ∨ hsame row T ∨ hsame row R ∨ hsame row L ∨
              hsame row H ∨ hsame row K ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.CauchyFilterCompletionUp
