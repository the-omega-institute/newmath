import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_downstream_unblock_package [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      monotoneRead criterionRead observationRead extractionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source witness monotoneRead →
        Cont witness regular criterionRead →
          Cont schedule ledger observationRead →
            Cont schedule witness extractionRead →
              PkgSig bundle monotoneRead pkg →
                PkgSig bundle criterionRead pkg →
                  PkgSig bundle observationRead pkg →
                    PkgSig bundle extractionRead pkg →
                      SemanticNameCert
                        (fun row : BHist =>
                          BoundedMonotoneCauchyWitnessCarrier source regular schedule witness
                              ledger trap sealRow transport route provenance localCert bundle
                              pkg ∧
                            (hsame row monotoneRead ∨ hsame row criterionRead ∨
                              hsame row observationRead ∨ hsame row extractionRead))
                        (fun row : BHist =>
                          Cont source witness monotoneRead ∧
                            Cont witness regular criterionRead ∧
                              Cont schedule ledger observationRead ∧
                                Cont schedule witness extractionRead ∧ PkgSig bundle row pkg)
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle row pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceWitnessMonotone witnessRegularCriterion scheduleLedgerObservation
    scheduleWitnessExtraction monotonePkg criterionPkg observationPkg extractionPkg
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    _sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ :=
    carrier
  have monotoneUnary : UnaryHistory monotoneRead :=
    unary_cont_closed sourceUnary witnessUnary sourceWitnessMonotone
  have criterionUnary : UnaryHistory criterionRead :=
    unary_cont_closed witnessUnary regularUnary witnessRegularCriterion
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed scheduleUnary ledgerUnary scheduleLedgerObservation
  have extractionUnary : UnaryHistory extractionRead :=
    unary_cont_closed scheduleUnary witnessUnary scheduleWitnessExtraction
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro monotoneRead
          (And.intro carrierFull (Or.inl (hsame_refl monotoneRead)))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact source.left
        · cases source.right with
          | inl sameMonotone =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameMonotone)
          | inr rest =>
              cases rest with
              | inl sameCriterion =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameCriterion))
              | inr restTail =>
                  cases restTail with
                  | inl sameObservation =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameObservation)))
                  | inr sameExtraction =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) sameExtraction)))
    }
    pattern_sound := by
      intro row source
      constructor
      · exact sourceWitnessMonotone
      · constructor
        · exact witnessRegularCriterion
        · constructor
          · exact scheduleLedgerObservation
          · constructor
            · exact scheduleWitnessExtraction
            · cases source.right with
              | inl sameMonotone =>
                  cases sameMonotone
                  exact monotonePkg
              | inr rest =>
                  cases rest with
                  | inl sameCriterion =>
                      cases sameCriterion
                      exact criterionPkg
                  | inr restTail =>
                      cases restTail with
                      | inl sameObservation =>
                          cases sameObservation
                          exact observationPkg
                      | inr sameExtraction =>
                          cases sameExtraction
                          exact extractionPkg
    ledger_sound := by
      intro row source
      cases source.right with
      | inl sameMonotone =>
          cases sameMonotone
          exact And.intro monotoneUnary monotonePkg
      | inr rest =>
          cases rest with
          | inl sameCriterion =>
              cases sameCriterion
              exact And.intro criterionUnary criterionPkg
          | inr restTail =>
              cases restTail with
              | inl sameObservation =>
                  cases sameObservation
                  exact And.intro observationUnary observationPkg
              | inr sameExtraction =>
                  cases sameExtraction
                  exact And.intro extractionUnary extractionPkg
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
