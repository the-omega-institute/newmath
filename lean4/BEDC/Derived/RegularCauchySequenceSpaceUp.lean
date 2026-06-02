import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchySequenceSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchySequenceSpaceRealHandoff [AskSetup] [PackageSetup]
    {F rho sigma W D Q E H C P N rateRead windowRead cauchyRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F ->
      UnaryHistory rho ->
        UnaryHistory sigma ->
          UnaryHistory W ->
            UnaryHistory D ->
              UnaryHistory Q ->
                UnaryHistory E ->
                  Cont F rho rateRead ->
                    Cont rateRead W windowRead ->
                      Cont windowRead Q cauchyRead ->
                        Cont cauchyRead E sealRead ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row F ∨ hsame row rho ∨ hsame row sigma ∨
                                    hsame row W ∨ hsame row D ∨ hsame row Q ∨
                                      hsame row E ∨ hsame row rateRead ∨
                                        hsame row windowRead ∨ hsame row cauchyRead ∨
                                          hsame row sealRead ∨ hsame row N)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont F rho rateRead ∧
                                    Cont rateRead W windowRead ∧
                                      Cont windowRead Q cauchyRead ∧
                                        Cont cauchyRead E sealRead ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory rateRead ∧ UnaryHistory windowRead ∧
                                UnaryHistory cauchyRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro unaryF _unaryRho _unarySigma unaryW _unaryD unaryQ unaryE rateRoute windowRoute
    cauchyRoute sealRoute packageN
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed unaryF _unaryRho rateRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rateUnary unaryW windowRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed windowUnary unaryQ cauchyRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed cauchyUnary unaryE sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row rho ∨ hsame row sigma ∨ hsame row W ∨
              hsame row D ∨ hsame row Q ∨ hsame row E ∨ hsame row rateRead ∨
                hsame row windowRead ∨ hsame row cauchyRead ∨ hsame row sealRead ∨
                  hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F rho rateRead ∧ Cont rateRead W windowRead ∧
              Cont windowRead Q cauchyRead ∧ Cont cauchyRead E sealRead ∧
                PkgSig bundle N pkg)
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
                            (Or.inl source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, rateRoute, windowRoute, cauchyRoute, sealRoute, packageN⟩
  }
  exact ⟨cert, rateUnary, windowUnary, cauchyUnary, sealUnary⟩

end BEDC.Derived.RegularCauchySequenceSpaceUp
