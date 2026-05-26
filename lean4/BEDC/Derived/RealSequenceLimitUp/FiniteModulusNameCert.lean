import BEDC.Derived.RealSequenceLimitUp.NameCertObligations

namespace BEDC.Derived.RealSequenceLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealSequenceLimitFiniteModulusCarrier [AskSetup] [PackageSetup]
    (sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name threshold admitted : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  RealSequenceLimitCarrier sequenceRow limitRow windowSchedule dyadicLedger classifierRow
      transport route provenance name bundle pkg ∧
    UnaryHistory threshold ∧ UnaryHistory admitted ∧
      Cont windowSchedule dyadicLedger threshold ∧ Cont threshold classifierRow admitted ∧
        PkgSig bundle admitted pkg

theorem RealSequenceLimitModulusNameCertObligations [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name threshold admitted : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitFiniteModulusCarrier sequenceRow limitRow windowSchedule dyadicLedger
        classifierRow transport route provenance name threshold admitted bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RealSequenceLimitFiniteModulusCarrier sequenceRow limitRow windowSchedule
            dyadicLedger classifierRow transport route provenance name threshold admitted
            bundle pkg ∧
            (hsame row threshold ∨ hsame row admitted ∨ hsame row classifierRow))
        (fun row : BHist =>
          RealSequenceLimitFiniteModulusCarrier sequenceRow limitRow windowSchedule
            dyadicLedger classifierRow transport route provenance name threshold admitted
            bundle pkg ∧
            (hsame row threshold ∨ hsame row admitted ∨ hsame row classifierRow))
        (fun row : BHist =>
          PkgSig bundle admitted pkg ∧
            (hsame row threshold ∨ hsame row admitted ∨ hsame row classifierRow))
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier
  have admittedPkg : PkgSig bundle admitted pkg := carrier.right.right.right.right.right
  exact {
    core := {
      carrier_inhabited := Exists.intro threshold
        ⟨carrier, Or.inl (hsame_refl threshold)⟩
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
        obtain ⟨finiteCarrier, sourceRow⟩ := source
        refine ⟨finiteCarrier, ?_⟩
        cases sourceRow with
        | inl sameThreshold =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameThreshold)
        | inr rest =>
            cases rest with
            | inl sameAdmitted =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameAdmitted))
            | inr sameClassifier =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameClassifier))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨admittedPkg, source.right⟩
  }

theorem RealSequenceLimitFiniteModulusCarrier_threshold_route [AskSetup] [PackageSetup]
    {sequenceRow limitRow windowSchedule dyadicLedger classifierRow transport route provenance
      name threshold admitted thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSequenceLimitFiniteModulusCarrier sequenceRow limitRow windowSchedule dyadicLedger
        classifierRow transport route provenance name threshold admitted bundle pkg ->
      Cont admitted threshold thresholdRead ->
        PkgSig bundle thresholdRead pkg ->
          UnaryHistory threshold ∧ UnaryHistory admitted ∧ UnaryHistory thresholdRead ∧
            Cont windowSchedule dyadicLedger threshold ∧ Cont threshold classifierRow admitted ∧
              Cont admitted threshold thresholdRead ∧ PkgSig bundle admitted pkg ∧
                PkgSig bundle thresholdRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier thresholdRoute thresholdReadPkg
  have thresholdReadUnary : UnaryHistory thresholdRead :=
    unary_cont_closed carrier.right.right.left carrier.right.left thresholdRoute
  exact
    ⟨carrier.right.left,
      carrier.right.right.left,
      thresholdReadUnary,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      thresholdRoute,
      carrier.right.right.right.right.right,
      thresholdReadPkg⟩

end BEDC.Derived.RealSequenceLimitUp
