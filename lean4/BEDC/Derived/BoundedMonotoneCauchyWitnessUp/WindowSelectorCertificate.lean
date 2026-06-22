import BEDC.Derived.BoundedMonotoneCauchyWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessWindowSelectorCertificate [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      windowRead witnessRead trapRead realRead selectorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule windowRead →
        Cont windowRead regular witnessRead →
          Cont witnessRead ledger trapRead →
            Cont trapRead sealRow realRead →
              Cont realRead provenance selectorRead →
                PkgSig bundle selectorRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row windowRead ∨ hsame row witnessRead ∨ hsame row trapRead ∨
                          hsame row realRead ∨ hsame row selectorRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont source schedule windowRead ∧
                          Cont windowRead regular witnessRead ∧
                            Cont witnessRead ledger trapRead ∧
                              Cont trapRead sealRow realRead ∧
                                Cont realRead provenance selectorRead ∧
                                  PkgSig bundle selectorRead pkg)
                      hsame ∧
                    UnaryHistory selectorRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceScheduleWindow windowRegularWitness witnessLedgerTrap trapSealReal
    realProvenanceSelector selectorPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleWindow
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed windowUnary regularUnary windowRegularWitness
  have trapReadUnary : UnaryHistory trapRead :=
    unary_cont_closed witnessReadUnary ledgerUnary witnessLedgerTrap
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed trapReadUnary sealUnary trapSealReal
  have selectorReadUnary : UnaryHistory selectorRead :=
    unary_cont_closed realReadUnary provenanceUnary realProvenanceSelector
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selectorRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windowRead ∨ hsame row witnessRead ∨ hsame row trapRead ∨
              hsame row realRead ∨ hsame row selectorRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source schedule windowRead ∧
              Cont windowRead regular witnessRead ∧ Cont witnessRead ledger trapRead ∧
                Cont trapRead sealRow realRead ∧ Cont realRead provenance selectorRead ∧
                  PkgSig bundle selectorRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro selectorRead ⟨hsame_refl selectorRead, selectorReadUnary⟩
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
      exact
        ⟨source.right, sourceScheduleWindow, windowRegularWitness, witnessLedgerTrap,
          trapSealReal, realProvenanceSelector, selectorPkg⟩
  }
  exact ⟨cert, selectorReadUnary⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
