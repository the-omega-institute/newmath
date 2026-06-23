import BEDC.Derived.RegularCauchyWindowFusionUp.NameCertObligations

namespace BEDC.Derived.RegularCauchyWindowFusionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWindowFusionFiniteWindowExactness [AskSetup] [PackageSetup]
    {R W S D E H C P N tailRead windowRead dyadicRead sealRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory W ->
        UnaryHistory S ->
          UnaryHistory D ->
            UnaryHistory E ->
              UnaryHistory H ->
                Cont R W tailRead ->
                  Cont tailRead S windowRead ->
                    Cont windowRead D dyadicRead ->
                      Cont dyadicRead E sealRead ->
                        Cont H sealRead named ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle named pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row named ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row R ∨ hsame row W ∨ hsame row S ∨
                                      hsame row D ∨ hsame row E ∨ hsame row H ∨
                                        hsame row C ∨ hsame row P ∨ hsame row N ∨
                                          hsame row tailRead ∨ hsame row windowRead ∨
                                            hsame row dyadicRead ∨ hsame row sealRead ∨
                                              hsame row named)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont R W tailRead ∧
                                      Cont tailRead S windowRead ∧
                                        Cont windowRead D dyadicRead ∧
                                          Cont dyadicRead E sealRead ∧
                                            Cont H sealRead named ∧
                                              PkgSig bundle named pkg)
                                  hsame ∧
                                UnaryHistory tailRead ∧ UnaryHistory windowRead ∧
                                  UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                                    UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro rUnary wUnary sUnary dUnary eUnary hUnary tailRoute windowRoute dyadicRoute
    sealRoute namedRoute _sourcePkg namedPkg
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed rUnary wUnary tailRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tailUnary sUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary eUnary sealRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary sealUnary namedRoute
  have sourceAtNamed :
      (fun row : BHist => hsame row named ∧ UnaryHistory row) named := by
    exact ⟨hsame_refl named, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row S ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row tailRead ∨ hsame row windowRead ∨ hsame row dyadicRead ∨
                  hsame row sealRead ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W tailRead ∧ Cont tailRead S windowRead ∧
              Cont windowRead D dyadicRead ∧ Cont dyadicRead E sealRead ∧
                Cont H sealRead named ∧ PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named sourceAtNamed
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, windowRoute, dyadicRoute, sealRoute, namedRoute,
          namedPkg⟩
  }
  exact ⟨cert, tailUnary, windowUnary, dyadicUnary, sealUnary, namedUnary⟩

end BEDC.Derived.RegularCauchyWindowFusionUp
