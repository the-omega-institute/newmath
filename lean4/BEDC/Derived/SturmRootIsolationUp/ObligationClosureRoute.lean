import BEDC.Derived.SturmRootIsolationUp.CertificateLedger

namespace BEDC.Derived.SturmRootIsolationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SturmRootIsolationCarrier_obligation_closure_route [AskSetup] [PackageSetup]
    {P I D V B W R S H C Q N branchRead refinedRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont P V branchRead →
      Cont I D refinedRead →
        Cont refinedRead W windowRead →
          Cont windowRead S sealRead →
            PkgSig bundle sealRead pkg →
              UnaryHistory P →
                UnaryHistory V →
                  UnaryHistory I →
                    UnaryHistory D →
                      UnaryHistory W →
                        UnaryHistory S →
                          SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row P ∨ hsame row I ∨ hsame row D ∨ hsame row V ∨
                                  hsame row W ∨ hsame row S ∨ hsame row sealRead)
                              (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                              hsame ∧
                            UnaryHistory branchRead ∧ UnaryHistory refinedRead ∧
                              UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro branchRoute refinedRoute windowRoute sealRoute sealPkg polynomialUnary
    variationUnary intervalUnary dyadicUnary windowUnary sealUnary
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed polynomialUnary variationUnary branchRoute
  have refinedReadUnary : UnaryHistory refinedRead :=
    unary_cont_closed intervalUnary dyadicUnary refinedRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed refinedReadUnary windowUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnary sealRoute
  have sealListed :
      List.Mem (sturmRootIsolationEncodeBHist S)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) := by
    change
      List.Mem (sturmRootIsolationEncodeBHist S)
        [[BMark.b0], sturmRootIsolationEncodeBHist P, [BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist I, [BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist D, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist V,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist B,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist W,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist R,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          sturmRootIsolationEncodeBHist S,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist Q,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          sturmRootIsolationEncodeBHist N]
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row I ∨ hsame row D ∨ hsame row V ∨ hsame row W ∨
              hsame row S ∨ hsame row sealRead)
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
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg⟩
  }
  have _sturmSpecific :
      List.Mem (sturmRootIsolationEncodeBHist S)
        (sturmRootIsolationToEventFlow
          (SturmRootIsolationUp.mk P I D V B W R S H C Q N)) :=
    sealListed
  exact ⟨cert, branchReadUnary, refinedReadUnary, windowReadUnary, sealReadUnary⟩

end BEDC.Derived.SturmRootIsolationUp
