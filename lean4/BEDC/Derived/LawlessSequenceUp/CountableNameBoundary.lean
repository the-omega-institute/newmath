import BEDC.Derived.LawlessSequenceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceCountableNameBoundary [AskSetup] [PackageSetup]
    {window digit index transport replay provenance name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont window digit index → Cont index transport replay → Cont replay provenance consumer →
      PkgSig bundle name pkg →
        UnaryHistory window → UnaryHistory digit → UnaryHistory transport →
          UnaryHistory provenance →
          SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist => hsame row window ∨ hsame row digit ∨ hsame row index ∨
              hsame row replay ∨ hsame row consumer)
            (fun row : BHist => hsame row consumer ∧ PkgSig bundle name pkg)
            hsame ∧ UnaryHistory index ∧ UnaryHistory replay ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro windowDigit indexTransport replayProvenance namePkg windowUnary digitUnary transportUnary
    provenanceUnary
  have indexUnary : UnaryHistory index :=
    unary_cont_closed windowUnary digitUnary windowDigit
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed indexUnary transportUnary indexTransport
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed replayUnary provenanceUnary replayProvenance
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist => hsame row window ∨ hsame row digit ∨ hsame row index ∨
          hsame row replay ∨ hsame row consumer)
        (fun row : BHist => hsame row consumer ∧ PkgSig bundle name pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, namePkg⟩
  }
  exact ⟨cert, indexUnary, replayUnary, consumerUnary⟩

end BEDC.Derived.LawlessSequenceUp
