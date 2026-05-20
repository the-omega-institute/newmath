import BEDC.Derived.CauchyChoiceBoundaryUp.DiagonalBudgetFactorization
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CauchyChoiceBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyChoiceBoundary_no_choice_nonescape [AskSetup] [PackageSetup]
    {M E I T S R _H _C _P N selectedRead tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont M E I ->
      Cont I T selectedRead ->
        Cont selectedRead S tailRead ->
          Cont tailRead R sealRead ->
            UnaryHistory M ->
              UnaryHistory E ->
                UnaryHistory T ->
                  UnaryHistory S ->
                    UnaryHistory R ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row sealRead ∧ Cont selectedRead S tailRead ∧
                                Cont tailRead R sealRead)
                            (fun row : BHist => hsame row sealRead ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory selectedRead ∧ UnaryHistory tailRead ∧
                            UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro routeI routeSelected routeTail routeSeal unaryM unaryE unaryT unaryS unaryR namePkg
  have unaryI : UnaryHistory I :=
    unary_cont_closed unaryM unaryE routeI
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed unaryI unaryT routeSelected
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed selectedUnary unaryS routeTail
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary unaryR routeSeal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row sealRead ∧ Cont selectedRead S tailRead ∧ Cont tailRead R sealRead)
        (fun row : BHist => hsame row sealRead ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact ⟨source.left, routeTail, routeSeal⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact ⟨cert, selectedUnary, tailUnary, sealUnary⟩

end BEDC.Derived.CauchyChoiceBoundaryUp
