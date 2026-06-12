import BEDC.Derived.BetaSubstitutionPreservationUp
import BEDC.FKernel.Cont
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

theorem BetaSubstitutionPreservationRedexClosure [AskSetup] [PackageSetup]
    {body argument redex codomain substitutedBody substitutedCodomain ledger transport routes
      provenance localName redexRead codomainRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont body argument redexRead →
      Cont redex codomain codomainRead →
        PkgSig bundle provenance pkg →
          PkgSig bundle localName pkg →
            SemanticNameCert
              (fun row : BHist => hsame row codomainRead)
              (fun row : BHist =>
                hsame row body ∨ hsame row argument ∨ hsame row redex ∨
                  hsame row codomain ∨ hsame row substitutedBody ∨
                    hsame row substitutedCodomain ∨ hsame row ledger ∨
                      hsame row transport ∨ hsame row routes ∨ hsame row provenance ∨
                        hsame row localName ∨ hsame row redexRead ∨
                          hsame row codomainRead)
              (fun row : BHist =>
                hsame row codomainRead ∧ Cont body argument redexRead ∧
                  Cont redex codomain codomainRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro redexRoute codomainRoute provenancePkg localNamePkg
  exact {
    core := {
      carrier_inhabited := Exists.intro codomainRead (hsame_refl codomainRead)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
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
                            (Or.inr source)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source, redexRoute, codomainRoute, provenancePkg, localNamePkg⟩
  }

end BEDC.Derived.BetaSubstitutionPreservationUp
