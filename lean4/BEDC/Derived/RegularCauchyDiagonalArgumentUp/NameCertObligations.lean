import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyDiagonalArgumentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalArgumentNamecertObligations [AskSetup] [PackageSetup]
    {F W D R E H C P N diagonalRead windowRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory R →
            UnaryHistory E →
              UnaryHistory N →
                Cont F W diagonalRead →
                  Cont diagonalRead D windowRead →
                    Cont windowRead E realRead →
                      Cont realRead N namedRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle namedRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row F ∨ hsame row W ∨ hsame row D ∨
                                    hsame row R ∨ hsame row E ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont F W diagonalRead ∧
                                    Cont diagonalRead D windowRead ∧
                                      Cont windowRead E realRead ∧
                                        Cont realRead N namedRead ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle namedRead pkg)
                                hsame ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fUnary wUnary dUnary _rUnary eUnary nUnary diagonalRoute windowRoute realRoute
    namedRoute provenancePkg namePkg
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed fUnary wUnary diagonalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed diagonalUnary dUnary windowRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed windowUnary eUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F W diagonalRead ∧ Cont diagonalRead D windowRead ∧
              Cont windowRead E realRead ∧ Cont realRead N namedRead ∧
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diagonalRoute, windowRoute, realRoute, namedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.RegularCauchyDiagonalArgumentUp
