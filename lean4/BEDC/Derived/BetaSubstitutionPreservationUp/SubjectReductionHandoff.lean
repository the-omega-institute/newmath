import BEDC.Derived.BetaSubstitutionPreservationUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BetaSubstitutionPreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BetaSubstitutionPreservationSubjectReductionHandoff [AskSetup] [PackageSetup]
    {body argument redex codomain substitutedBody substitutedCodomain ledger transport routes
      provenance localName redexRead residualRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory body →
      UnaryHistory argument →
        UnaryHistory redex →
          UnaryHistory codomain →
            UnaryHistory substitutedCodomain →
              UnaryHistory routes →
                Cont body argument redexRead →
                  Cont redex codomain substitutedBody →
                    Cont substitutedBody substitutedCodomain residualRead →
                      Cont residualRead routes handoffRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle handoffRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row body ∨ hsame row argument ∨ hsame row redex ∨
                                    hsame row codomain ∨ hsame row substitutedBody ∨
                                      hsame row substitutedCodomain ∨ hsame row ledger ∨
                                        hsame row routes ∨ hsame row handoffRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont body argument redexRead ∧
                                    Cont redex codomain substitutedBody ∧
                                      Cont substitutedBody substitutedCodomain residualRead ∧
                                        Cont residualRead routes handoffRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle handoffRead pkg)
                                hsame ∧
                              UnaryHistory redexRead ∧ UnaryHistory substitutedBody ∧
                                UnaryHistory residualRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro bodyUnary argumentUnary redexUnary codomainUnary substitutedCodomainUnary routesUnary
    bodyArgumentRead redexCodomainSubstituted substitutedResidual residualRoutesHandoff
    provenancePkg handoffPkg
  have _transportSelf : hsame transport transport := hsame_refl transport
  have _localNameSelf : hsame localName localName := hsame_refl localName
  have redexReadUnary : UnaryHistory redexRead :=
    unary_cont_closed bodyUnary argumentUnary bodyArgumentRead
  have substitutedBodyUnary : UnaryHistory substitutedBody :=
    unary_cont_closed redexUnary codomainUnary redexCodomainSubstituted
  have residualReadUnary : UnaryHistory residualRead :=
    unary_cont_closed substitutedBodyUnary substitutedCodomainUnary substitutedResidual
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed residualReadUnary routesUnary residualRoutesHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row body ∨ hsame row argument ∨ hsame row redex ∨
              hsame row codomain ∨ hsame row substitutedBody ∨
                hsame row substitutedCodomain ∨ hsame row ledger ∨ hsame row routes ∨
                  hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont body argument redexRead ∧
              Cont redex codomain substitutedBody ∧
                Cont substitutedBody substitutedCodomain residualRead ∧
                  Cont residualRead routes handoffRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffReadUnary⟩
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
                (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, bodyArgumentRead, redexCodomainSubstituted, substitutedResidual,
          residualRoutesHandoff, provenancePkg, handoffPkg⟩
  }
  exact
    ⟨cert, redexReadUnary, substitutedBodyUnary, residualReadUnary, handoffReadUnary⟩

end BEDC.Derived.BetaSubstitutionPreservationUp
