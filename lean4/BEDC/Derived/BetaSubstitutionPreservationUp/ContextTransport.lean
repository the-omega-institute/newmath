import BEDC.Derived.BetaSubstitutionPreservationUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BetaSubstitutionPreservationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BetaSubstitutionPreservationContextTransport [AskSetup] [PackageSetup]
    {body argument redex codomain substitutedBody substitutedCodomain ledger transport routes
      provenance name contextRead transportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory body →
      UnaryHistory codomain →
        UnaryHistory transport →
          Cont body codomain contextRead →
            Cont contextRead transport transportedRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle name pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row body ∨ hsame row argument ∨ hsame row redex ∨
                          hsame row codomain ∨ hsame row substitutedBody ∨
                            hsame row substitutedCodomain ∨ hsame row ledger ∨
                              hsame row transport ∨ hsame row routes ∨
                                hsame row provenance ∨ hsame row name ∨
                                  hsame row contextRead ∨ hsame row transportedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont body codomain contextRead ∧
                          Cont contextRead transport transportedRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
                      hsame ∧
                    UnaryHistory contextRead ∧ UnaryHistory transportedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro bodyUnary codomainUnary transportUnary contextRoute transportedRoute provenancePkg
    namePkg
  have contextUnary : UnaryHistory contextRead :=
    unary_cont_closed bodyUnary codomainUnary contextRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed contextUnary transportUnary transportedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row transportedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row body ∨ hsame row argument ∨ hsame row redex ∨
              hsame row codomain ∨ hsame row substitutedBody ∨
                hsame row substitutedCodomain ∨ hsame row ledger ∨
                  hsame row transport ∨ hsame row routes ∨ hsame row provenance ∨
                    hsame row name ∨ hsame row contextRead ∨
                      hsame row transportedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont body codomain contextRead ∧
              Cont contextRead transport transportedRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro transportedRead ⟨hsame_refl transportedRead, transportedUnary⟩
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
      exact ⟨source.right, contextRoute, transportedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, contextUnary, transportedUnary⟩

end BEDC.Derived.BetaSubstitutionPreservationUp
