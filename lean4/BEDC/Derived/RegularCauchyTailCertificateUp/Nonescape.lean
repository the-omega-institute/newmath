import BEDC.Derived.RegularCauchyTailCertificateUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailCertificateNonescape [AskSetup] [PackageSetup]
    {X W R D E H C P N selectorRead readbackRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    regularCauchyTailCertificateFields (RegularCauchyTailCertificateUp.mk X W R D E H C P N) =
        [X, W, R, D, E, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory W ->
          UnaryHistory R ->
            UnaryHistory D ->
              UnaryHistory N ->
                Cont X W selectorRead ->
                  Cont selectorRead R readbackRead ->
                    Cont readbackRead D sealRead ->
                      Cont sealRead N namedRead ->
                        PkgSig bundle namedRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row X ∨ hsame row W ∨ hsame row R ∨
                                  hsame row D ∨ hsame row E ∨ hsame row H ∨
                                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                                      hsame row selectorRead ∨ hsame row readbackRead ∨
                                        hsame row sealRead ∨ hsame row namedRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont X W selectorRead ∧
                                  Cont selectorRead R readbackRead ∧
                                    Cont readbackRead D sealRead ∧
                                      Cont sealRead N namedRead ∧
                                        PkgSig bundle namedRead pkg)
                              hsame ∧
                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: RegularCauchyTailCertificateUp regularCauchyTailCertificateFields BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields sourceUnary windowUnary readbackUnary dyadicUnary nameUnary selectorRoute
    readbackRoute sealRoute namedRoute packageRead
  have _acceptedFields :
      regularCauchyTailCertificateFields
          (RegularCauchyTailCertificateUp.mk X W R D E H C P N) =
        [X, W, R, D, E, H, C, P, N] := fields
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed sourceUnary windowUnary selectorRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectorUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary dyadicUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary nameUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row selectorRead ∨ hsame row readbackRead ∨ hsame row sealRead ∨
                  hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W selectorRead ∧
              Cont selectorRead R readbackRead ∧ Cont readbackRead D sealRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectorRoute, readbackRoute, sealRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.RegularCauchyTailCertificateUp
