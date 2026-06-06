import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletenessDiagonalSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletenessDiagonalSelectorNonescape [AskSetup] [PackageSetup]
    {R E T S Q D A H C P N selectorRead tailRead windowRead dyadicRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory E →
        UnaryHistory T →
          UnaryHistory S →
            UnaryHistory D →
              UnaryHistory A →
                UnaryHistory N →
                  Cont R E selectorRead →
                    Cont selectorRead T tailRead →
                      Cont tailRead S windowRead →
                        Cont windowRead D dyadicRead →
                          Cont dyadicRead A sealRead →
                            Cont sealRead N namedRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle namedRead pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row namedRead ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row R ∨ hsame row E ∨ hsame row T ∨
                                          hsame row S ∨ hsame row Q ∨ hsame row D ∨
                                            hsame row A ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont R E selectorRead ∧
                                          Cont selectorRead T tailRead ∧
                                            Cont tailRead S windowRead ∧
                                              Cont windowRead D dyadicRead ∧
                                                Cont dyadicRead A sealRead ∧
                                                  Cont sealRead N namedRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle namedRead pkg)
                                      hsame ∧
                                    UnaryHistory selectorRead ∧ UnaryHistory tailRead ∧
                                      UnaryHistory windowRead ∧ UnaryHistory dyadicRead ∧
                                        UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro rUnary eUnary tUnary sUnary dUnary aUnary nUnary selectorRoute tailRoute
    windowRoute dyadicRoute sealRoute namedRoute provenancePkg namedPkg
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed rUnary eUnary selectorRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed selectorUnary tUnary tailRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tailUnary sUnary windowRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowUnary dUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary aUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row E ∨ hsame row T ∨ hsame row S ∨ hsame row Q ∨
              hsame row D ∨ hsame row A ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R E selectorRead ∧ Cont selectorRead T tailRead ∧
              Cont tailRead S windowRead ∧ Cont windowRead D dyadicRead ∧
                Cont dyadicRead A sealRead ∧ Cont sealRead N namedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectorRoute, tailRoute, windowRoute, dyadicRoute, sealRoute,
          namedRoute, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, selectorUnary, tailUnary, windowUnary, dyadicUnary, sealUnary, namedUnary⟩

end BEDC.Derived.RealCompletenessDiagonalSelectorUp
