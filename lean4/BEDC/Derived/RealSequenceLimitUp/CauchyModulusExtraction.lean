import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealSequenceLimitCauchyModulusExtraction [AskSetup] [PackageSetup]
    {sequence limit window dyadic classifier transport replay provenance name threshold
      sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitCarrier sequence limit window dyadic classifier transport replay provenance name
        bundle pkg ->
      Cont dyadic window threshold ->
        Cont threshold classifier sealRow ->
          PkgSig bundle sealRow pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row window ∨ hsame row threshold ∨
                    hsame row classifier ∨ hsame row sealRow)
                (fun row : BHist => hsame row sealRow ∧ PkgSig bundle sealRow pkg)
                hsame ∧
              UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory threshold ∧
                UnaryHistory sealRow ∧ Cont dyadic window threshold ∧
                  Cont threshold classifier sealRow := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier thresholdCont sealCont sealPkg
  rcases carrier with
    ⟨_sequenceUnary, _limitUnary, windowUnary, dyadicUnary, classifierUnary,
      _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _sequenceWindowReplay,
      _limitDyadicClassifier, _transportSame, _replaySame, _provenancePkg, _namePkg⟩
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed dyadicUnary windowUnary thresholdCont
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed thresholdUnary classifierUnary sealCont
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dyadic ∨ hsame row window ∨ hsame row threshold ∨
            hsame row classifier ∨ hsame row sealRow)
        (fun row : BHist => hsame row sealRow ∧ PkgSig bundle sealRow pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow ⟨hsame_refl sealRow, sealUnary⟩
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
      exact ⟨source.left, sealPkg⟩
  }
  exact
    ⟨cert, windowUnary, dyadicUnary, thresholdUnary, sealUnary, thresholdCont, sealCont⟩

end BEDC.Derived.RealSequenceLimitUp
