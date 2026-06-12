import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

set_option linter.unusedVariables false

theorem FanFunctionalUniformmodulusConsumerScope [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead depthRead witnessRead modulusRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory C ∧ UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory W ∧ UnaryHistory M ∧
      UnaryHistory H ∧ UnaryHistory K ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg) →
      Cont C B prefixRead →
        Cont prefixRead D depthRead →
          Cont depthRead W witnessRead →
            Cont witnessRead M modulusRead →
              Cont H K localRead →
                PkgSig bundle localRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row C ∨ hsame row B ∨ hsame row D ∨ hsame row W ∨
                          hsame row M ∨ hsame row H ∨ hsame row K ∨ hsame row P ∨
                            hsame row N ∨ hsame row modulusRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont C B prefixRead ∧
                          Cont prefixRead D depthRead ∧ Cont depthRead W witnessRead ∧
                            Cont depthRead W witnessRead ∧ Cont witnessRead M modulusRead ∧
                              PkgSig bundle localRead pkg)
                      hsame ∧
                    UnaryHistory prefixRead ∧ UnaryHistory depthRead ∧
                      UnaryHistory witnessRead ∧ UnaryHistory modulusRead ∧
                        UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface prefixRoute depthRoute witnessRoute modulusRoute localRoute localPkg
  have cUnary : UnaryHistory C := surface.left
  have bUnary : UnaryHistory B := surface.right.left
  have dUnary : UnaryHistory D := surface.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.left
  have mUnary : UnaryHistory M := surface.right.right.right.right.left
  have hUnary : UnaryHistory H := surface.right.right.right.right.right.left
  have kUnary : UnaryHistory K := surface.right.right.right.right.right.right.left
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary bUnary prefixRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed prefixUnary dUnary depthRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed depthUnary wUnary witnessRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary mUnary modulusRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary kUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row B ∨ hsame row D ∨ hsame row W ∨ hsame row M ∨
              hsame row H ∨ hsame row K ∨ hsame row P ∨ hsame row N ∨
                hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C B prefixRead ∧ Cont prefixRead D depthRead ∧
              Cont depthRead W witnessRead ∧ Cont depthRead W witnessRead ∧
                Cont witnessRead M modulusRead ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead ⟨hsame_refl modulusRead, modulusUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, prefixRoute, depthRoute, witnessRoute, witnessRoute, modulusRoute,
          localPkg⟩
  }
  exact ⟨cert, prefixUnary, depthUnary, witnessUnary, modulusUnary, localUnary⟩

end BEDC.Derived.FanfunctionalUp
