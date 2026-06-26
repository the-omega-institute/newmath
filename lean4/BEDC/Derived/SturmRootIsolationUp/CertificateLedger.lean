import BEDC.Derived.SturmRootIsolationUp.SignVariationHandoff
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SturmRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SturmRootIsolationCarrier_certificate_ledger [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N branchRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P V branchRead →
      Cont branchRead B windowRead →
        Cont windowRead S sealRead →
          PkgSig bundle sealRead pkg →
            UnaryHistory P →
              UnaryHistory V →
                UnaryHistory B →
                  UnaryHistory S →
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row P ∨ hsame row V ∨ hsame row B ∨ hsame row S ∨
                            hsame row sealRead)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                        hsame ∧
                      UnaryHistory branchRead ∧ UnaryHistory windowRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro branchRoute windowRoute sealRoute sealPkg polynomialUnary variationUnary branchUnary
    sealUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed polynomialUnary variationUnary branchRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed branchReadUnary branchUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnary sealRoute
  have _ledgerDisplay :
      sturmRootIsolationToEventFlow (SturmRootIsolationUp.mk P I D V B W R S H C Q N) =
        sturmRootIsolationToEventFlow (SturmRootIsolationUp.mk P I D V B W R S H C Q N) := by
    rfl
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row V ∨ hsame row B ∨ hsame row S ∨ hsame row sealRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg⟩
  }
  exact ⟨cert, branchReadUnary, windowReadUnary, sealReadUnary⟩

end BEDC.Derived.SturmRootIsolationUp
