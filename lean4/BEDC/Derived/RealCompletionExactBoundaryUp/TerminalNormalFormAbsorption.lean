import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryTerminalNormalFormAbsorption [AskSetup] [PackageSetup]
    {L K J S W R D E H C P N streamRead classifierRead boundaryRead secondRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W ->
      UnaryHistory D ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory H ->
              Cont W D streamRead ->
                Cont streamRead R classifierRead ->
                  Cont classifierRead E boundaryRead ->
                    Cont boundaryRead H secondRead ->
                      PkgSig bundle secondRead pkg ->
                        realCompletionExactBoundaryFields
                            (RealCompletionExactBoundaryUp.mk L K J S W R D E H C P N) =
                          [L, K, J, S, W, R, D, E, H, C, P, N] ∧
                          UnaryHistory streamRead ∧ UnaryHistory classifierRead ∧
                            UnaryHistory boundaryRead ∧ UnaryHistory secondRead ∧
                              Cont W D streamRead ∧ Cont streamRead R classifierRead ∧
                                Cont classifierRead E boundaryRead ∧
                                  Cont boundaryRead H secondRead ∧
                                    PkgSig bundle secondRead pkg ∧
                                      SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row secondRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row boundaryRead ∨ hsame row secondRead)
                                        (fun row : BHist =>
                                          hsame row secondRead ∧
                                            PkgSig bundle secondRead pkg)
                                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro unaryW unaryD unaryR unaryE unaryH streamRoute classifierRoute boundaryRoute
    secondRoute secondPkg
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed unaryW unaryD streamRoute
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed streamUnary unaryR classifierRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed classifierUnary unaryE boundaryRoute
  have secondUnary : UnaryHistory secondRead :=
    unary_cont_closed boundaryUnary unaryH secondRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row secondRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row boundaryRead ∨ hsame row secondRead)
        (fun row : BHist => hsame row secondRead ∧ PkgSig bundle secondRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro secondRead ⟨hsame_refl secondRead, secondUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, secondPkg⟩
  }
  exact
    ⟨rfl, streamUnary, classifierUnary, boundaryUnary, secondUnary, streamRoute,
      classifierRoute, boundaryRoute, secondRoute, secondPkg, cert⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
