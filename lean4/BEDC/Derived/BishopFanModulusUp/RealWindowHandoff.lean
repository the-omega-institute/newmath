import BEDC.Derived.BishopFanModulusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BishopFanModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BishopFanModulusRealWindowHandoff [AskSetup] [PackageSetup]
    {F A B S Q D R U H C P N fanAddress barWindow streamRead dyadicRead realSeal
      uniformRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F ->
      UnaryHistory A ->
        UnaryHistory B ->
          UnaryHistory S ->
            UnaryHistory Q ->
              UnaryHistory D ->
                UnaryHistory R ->
                  UnaryHistory U ->
                    UnaryHistory H ->
                      Cont F A fanAddress ->
                        Cont fanAddress B barWindow ->
                          Cont barWindow S streamRead ->
                            Cont Q D dyadicRead ->
                              Cont streamRead dyadicRead realSeal ->
                                Cont realSeal U uniformRead ->
                                  Cont H uniformRead named ->
                                    PkgSig bundle P pkg ->
                                      PkgSig bundle named pkg ->
                                        SemanticNameCert
                                            (fun row : BHist =>
                                              hsame row named ∧ UnaryHistory row)
                                            (fun row : BHist =>
                                              hsame row F ∨ hsame row A ∨
                                                hsame row B ∨ hsame row S ∨
                                                  hsame row Q ∨ hsame row D ∨
                                                    hsame row R ∨ hsame row U ∨
                                                      hsame row H ∨ hsame row C ∨
                                                        hsame row P ∨ hsame row N ∨
                                                          hsame row named)
                                            (fun row : BHist =>
                                              UnaryHistory row ∧
                                                Cont F A fanAddress ∧
                                                  Cont fanAddress B barWindow ∧
                                                    Cont barWindow S streamRead ∧
                                                      Cont Q D dyadicRead ∧
                                                        Cont streamRead dyadicRead
                                                          realSeal ∧
                                                          Cont realSeal U
                                                            uniformRead ∧
                                                            Cont H uniformRead named ∧
                                                              PkgSig bundle named pkg)
                                            hsame ∧
                                          UnaryHistory fanAddress ∧
                                            UnaryHistory barWindow ∧
                                              UnaryHistory streamRead ∧
                                                UnaryHistory dyadicRead ∧
                                                  UnaryHistory realSeal ∧
                                                    UnaryHistory uniformRead ∧
                                                      UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fUnary aUnary bUnary sUnary qUnary dUnary _rUnary uUnary hUnary fanRoute
    barRoute streamRoute dyadicRoute realRoute uniformRoute namedRoute _packageRead namedPkg
  have fanUnary : UnaryHistory fanAddress :=
    unary_cont_closed fUnary aUnary fanRoute
  have barUnary : UnaryHistory barWindow :=
    unary_cont_closed fanUnary bUnary barRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed barUnary sUnary streamRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed qUnary dUnary dyadicRoute
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed streamUnary dyadicUnary realRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed realUnary uUnary uniformRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed hUnary uniformUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row A ∨ hsame row B ∨ hsame row S ∨ hsame row Q ∨
              hsame row D ∨ hsame row R ∨ hsame row U ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F A fanAddress ∧ Cont fanAddress B barWindow ∧
              Cont barWindow S streamRead ∧ Cont Q D dyadicRead ∧
                Cont streamRead dyadicRead realSeal ∧ Cont realSeal U uniformRead ∧
                  Cont H uniformRead named ∧ PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, fanRoute, barRoute, streamRoute, dyadicRoute, realRoute,
          uniformRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, fanUnary, barUnary, streamUnary, dyadicUnary, realUnary, uniformUnary, namedUnary⟩

end BEDC.Derived.BishopFanModulusUp
