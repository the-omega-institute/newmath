import BEDC.Derived.ScientificObjectUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ScientificObjectUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ScientificObjectGapReportLedger [AskSetup] [PackageSetup]
    {G N reportRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory G →
      UnaryHistory N →
        Cont G N reportRead →
          PkgSig bundle reportRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row G ∨ hsame row reportRead)
                (fun row : BHist => hsame row G ∨ hsame row N ∨ hsame row reportRead)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle reportRead pkg)
                hsame ∧
              UnaryHistory reportRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro gapUnary nameUnary reportRoute reportPkg
  have reportUnary : UnaryHistory reportRead :=
    unary_cont_closed gapUnary nameUnary reportRoute
  have source :
      (fun row : BHist => hsame row G ∨ hsame row reportRead) G := by
    exact Or.inl (hsame_refl G)
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row G ∨ hsame row reportRead)
          (fun row : BHist => hsame row G ∨ hsame row N ∨ hsame row reportRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle reportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro G source
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
        intro _row _other sameRows rowSource
        cases rowSource with
        | inl sameGap =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameGap)
        | inr sameReport =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameReport)
    }
    pattern_sound := by
      intro _row rowSource
      cases rowSource with
      | inl sameGap =>
          exact Or.inl sameGap
      | inr sameReport =>
          exact Or.inr (Or.inr sameReport)
    ledger_sound := by
      intro _row rowSource
      cases rowSource with
      | inl sameGap =>
          exact ⟨unary_transport gapUnary (hsame_symm sameGap), reportPkg⟩
      | inr sameReport =>
          exact ⟨unary_transport reportUnary (hsame_symm sameReport), reportPkg⟩
  }
  exact ⟨cert, reportUnary⟩

end BEDC.Derived.ScientificObjectUp
