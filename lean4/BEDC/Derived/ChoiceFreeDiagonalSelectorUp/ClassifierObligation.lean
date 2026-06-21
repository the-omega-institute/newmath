import BEDC.Derived.ChoiceFreeDiagonalSelectorUp.ObligationCarrier

namespace BEDC.Derived.ChoiceFreeDiagonalSelectorUp.ClassifierObligation

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ChoiceFreeDiagonalSelectorCarrier_classifier_obligation [AskSetup] [PackageSetup]
    {epsilon window stream readback realSeal transport replay provenance localName
      transportedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ChoiceFreeDiagonalSelectorCarrier epsilon window stream readback realSeal transport replay
        provenance localName bundle pkg →
      Cont transport replay transportedRead →
        Cont transportedRead realSeal sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
                    hsame row readback ∨ hsame row realSeal ∨ hsame row transport ∨
                      hsame row replay ∨ hsame row transportedRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont transport replay transportedRead ∧
                    Cont transportedRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory transportedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: ChoiceFreeDiagonalSelectorCarrier BHist Cont Pkg SemanticNameCert hsame
  intro carrier transportReplay transportedReal sealPkg
  obtain ⟨_epsilonUnary, _windowUnary, _streamUnary, _readbackUnary, realSealUnary,
    transportUnary, replayUnary, _provenanceUnary, _localNameUnary, _storedWindowRoute,
    _storedReplayRoute, provenancePkg⟩ := carrier
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed transportUnary replayUnary transportReplay
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed transportedUnary realSealUnary transportedReal
  have sourceSeal : hsame sealRead sealRead ∧ UnaryHistory sealRead :=
    ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row epsilon ∨ hsame row window ∨ hsame row stream ∨
              hsame row readback ∨ hsame row realSeal ∨ hsame row transport ∨
                hsame row replay ∨ hsame row transportedRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont transport replay transportedRead ∧
              Cont transportedRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, transportReplay, transportedReal, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, transportedUnary, sealUnary⟩

end BEDC.Derived.ChoiceFreeDiagonalSelectorUp.ClassifierObligation
