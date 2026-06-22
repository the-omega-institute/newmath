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

theorem RegularCauchyTailCertificateVisionHandoff [AskSetup] [PackageSetup]
    {X W R D E H C P N tailRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont X W tailRead ->
      Cont tailRead R readbackRead ->
        Cont readbackRead D sealRead ->
          PkgSig bundle sealRead pkg ->
            UnaryHistory X ->
              UnaryHistory W ->
                UnaryHistory R ->
                  UnaryHistory D ->
                    SemanticNameCert
                        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                            hsame row E ∨ hsame row sealRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont X W tailRead ∧
                            Cont tailRead R readbackRead ∧ Cont readbackRead D sealRead ∧
                              PkgSig bundle sealRead pkg)
                        hsame ∧
                      UnaryHistory tailRead ∧ UnaryHistory readbackRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyTailCertificateUp BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro tailRoute readbackRoute sealRoute sealPkg sourceUnary windowUnary readbackUnary
    dyadicUnary
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed sourceUnary windowUnary tailRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed tailUnary readbackUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary dyadicUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E ∨
              hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont X W tailRead ∧ Cont tailRead R readbackRead ∧
              Cont readbackRead D sealRead ∧ PkgSig bundle sealRead pkg)
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, tailRoute, readbackRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, tailUnary, readbackReadUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyTailCertificateUp
