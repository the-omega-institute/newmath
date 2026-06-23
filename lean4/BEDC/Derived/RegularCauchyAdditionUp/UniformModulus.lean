import BEDC.Derived.RegularCauchyAdditionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyAdditionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAddition_uniform_modulus [AskSetup] [PackageSetup]
    {R0 R1 W0 W1 T0 T1 D E S Z H C P N windowRead sumRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R0 →
      UnaryHistory R1 →
        UnaryHistory W0 →
          UnaryHistory W1 →
            UnaryHistory T0 →
              UnaryHistory T1 →
                UnaryHistory D →
                  UnaryHistory E →
                    UnaryHistory S →
                      Cont W0 W1 windowRead →
                        Cont T0 T1 D →
                          Cont windowRead D sumRead →
                            Cont sumRead S sealRead →
                              PkgSig bundle sealRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row R0 ∨ hsame row R1 ∨ hsame row W0 ∨
                                        hsame row W1 ∨ hsame row D ∨ hsame row E ∨
                                          hsame row S ∨ hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont W0 W1 windowRead ∧
                                        Cont T0 T1 D ∧ Cont windowRead D sumRead ∧
                                          Cont sumRead S sealRead ∧
                                            PkgSig bundle sealRead pkg)
                                    hsame ∧
                                  UnaryHistory windowRead ∧ UnaryHistory sumRead ∧
                                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _r0Unary _r1Unary w0Unary w1Unary t0Unary t1Unary _dUnary _eUnary sUnary
    windowRoute toleranceRoute sumRoute sealRoute sealPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed w0Unary w1Unary windowRoute
  have dFromRoute : UnaryHistory D :=
    unary_cont_closed t0Unary t1Unary toleranceRoute
  have sumUnary : UnaryHistory sumRead :=
    unary_cont_closed windowUnary dFromRoute sumRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sumUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R0 ∨ hsame row R1 ∨ hsame row W0 ∨ hsame row W1 ∨
              hsame row D ∨ hsame row E ∨ hsame row S ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W0 W1 windowRead ∧ Cont T0 T1 D ∧
              Cont windowRead D sumRead ∧ Cont sumRead S sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
        exact ⟨source.right, windowRoute, toleranceRoute, sumRoute, sealRoute, sealPkg⟩
    }
  exact ⟨cert, windowUnary, sumUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyAdditionUp
