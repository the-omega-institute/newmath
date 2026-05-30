import BEDC.Derived.ScientificObjectUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ScientificObjectUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ScientificObjectTruthDomainGapScope [AskSetup] [PackageSetup]
    {T D G truthRead gapRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory D →
        UnaryHistory G →
          Cont T D truthRead →
            Cont G D gapRead →
              PkgSig bundle truthRead pkg →
                PkgSig bundle gapRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row truthRead ∨ hsame row gapRead)
                      (fun row : BHist =>
                        hsame row T ∨ hsame row D ∨ hsame row G ∨
                          hsame row truthRead ∨ hsame row gapRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧
                          (PkgSig bundle truthRead pkg ∨ PkgSig bundle gapRead pkg))
                      hsame ∧
                    UnaryHistory truthRead ∧ UnaryHistory gapRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro truthUnary domainUnary gapUnary truthRoute gapRoute truthPkg gapPkg
  have truthReadUnary : UnaryHistory truthRead :=
    unary_cont_closed truthUnary domainUnary truthRoute
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed gapUnary domainUnary gapRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row truthRead ∨ hsame row gapRead)
          (fun row : BHist =>
            hsame row T ∨ hsame row D ∨ hsame row G ∨
              hsame row truthRead ∨ hsame row gapRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle truthRead pkg ∨ PkgSig bundle gapRead pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro truthRead (Or.inl (hsame_refl truthRead))
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
        cases source with
        | inl sameTruth =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameTruth)
        | inr sameGap =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameGap)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameTruth =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameTruth)))
      | inr sameGap =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameGap)))
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameTruth =>
          exact
            ⟨unary_transport truthReadUnary (hsame_symm sameTruth), Or.inl truthPkg⟩
      | inr sameGap =>
          exact
            ⟨unary_transport gapReadUnary (hsame_symm sameGap), Or.inr gapPkg⟩
  }
  exact ⟨cert, truthReadUnary, gapReadUnary⟩

end BEDC.Derived.ScientificObjectUp
