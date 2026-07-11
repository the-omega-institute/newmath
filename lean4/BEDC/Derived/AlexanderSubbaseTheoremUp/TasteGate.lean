import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AlexanderSubbaseTheoremUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AlexanderSubbaseTheoremCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X S F U B H C P N subbaseRead finiteRead coverRead productRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X -> UnaryHistory S -> UnaryHistory F -> UnaryHistory U ->
      UnaryHistory B -> UnaryHistory P -> UnaryHistory N -> Cont X S subbaseRead ->
        Cont subbaseRead F finiteRead -> Cont finiteRead U coverRead ->
          Cont coverRead B productRead -> Cont productRead N namedRead ->
            PkgSig bundle P pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row S ∨ hsame row F ∨ hsame row U ∨
                      hsame row B ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row subbaseRead ∨ hsame row finiteRead ∨
                          hsame row coverRead ∨ hsame row productRead ∨
                            hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont X S subbaseRead ∧
                      Cont subbaseRead F finiteRead ∧ Cont finiteRead U coverRead ∧
                        Cont coverRead B productRead ∧ Cont productRead N namedRead ∧
                          PkgSig bundle P pkg)
                  hsame := by
  -- BEDC touchpoint anchor: AlexanderSubbaseTheoremUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryX unaryS unaryF unaryU unaryB _unaryP unaryN subbaseRoute finiteRoute
    coverRoute productRoute namedRoute packageP
  have subbaseUnary : UnaryHistory subbaseRead :=
    unary_cont_closed unaryX unaryS subbaseRoute
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed subbaseUnary unaryF finiteRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed finiteUnary unaryU coverRoute
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed coverUnary unaryB productRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed productUnary unaryN namedRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, subbaseRoute, finiteRoute, coverRoute, productRoute, namedRoute,
          packageP⟩
  }

end BEDC.Derived.AlexanderSubbaseTheoremUp
