import BEDC.Derived.BishopRegularCauchyCompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BishopRegularCauchyCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopRegularCauchyCompletionMatureRoute [AskSetup] [PackageSetup]
    {E S R D W H C P N obligationRead scopedRead publicRead bridgeRead matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory E ->
      UnaryHistory S ->
        UnaryHistory R ->
          UnaryHistory D ->
            UnaryHistory W ->
              UnaryHistory C ->
                UnaryHistory N ->
                  Cont E S obligationRead ->
                    Cont obligationRead R scopedRead ->
                      Cont scopedRead W publicRead ->
                        Cont publicRead C bridgeRead ->
                          Cont bridgeRead N matureRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                SemanticNameCert
                                      (fun row : BHist => hsame row matureRead ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row E ∨ hsame row S ∨ hsame row R ∨
                                          hsame row D ∨ hsame row W ∨
                                            hsame row bridgeRead ∨ hsame row matureRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont publicRead C bridgeRead ∧
                                          Cont bridgeRead N matureRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory obligationRead ∧ UnaryHistory scopedRead ∧
                                      UnaryHistory publicRead ∧ UnaryHistory bridgeRead ∧
                                        UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro unaryE unaryS unaryR _unaryD unaryW unaryC unaryN obligationRoute scopedRoute
    publicRoute bridgeRoute matureRoute provenancePkg localNamePkg
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed unaryE unaryS obligationRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed obligationUnary unaryR scopedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed scopedUnary unaryW publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary unaryC bridgeRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed bridgeUnary unaryN matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
              hsame row W ∨ hsame row bridgeRead ∨ hsame row matureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont publicRead C bridgeRead ∧
              Cont bridgeRead N matureRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgeRoute, matureRoute, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, obligationUnary, scopedUnary, publicUnary, bridgeUnary, matureUnary⟩

end BEDC.Derived.BishopRegularCauchyCompletionUp
