import BEDC.Derived.EgorovUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EgorovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Egorov_measure_ledger_nonescape [AskSetup] [PackageSetup]
    {M Omega F X S R A W U L H C P N ledgerRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier M Omega F X S R A W U L H C P N bundle pkg ->
      Cont A L ledgerRead ->
        Cont ledgerRead C consumerRead ->
          PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row Omega ∨ hsame row A ∨ hsame row L ∨
                    hsame row ledgerRead ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont A L ledgerRead ∧ Cont ledgerRead C consumerRead ∧
                    PkgSig bundle P pkg)
                hsame ∧
              UnaryHistory ledgerRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier measureLedgerRoute consumerRoute provenancePkg
  obtain ⟨_packetWitness, measureUnary, probUnary, _familyUnary, _limitUnary,
    _scheduleUnary, _readbackUnary, exceptionalUnary, _windowUnary, _uniformityUnary,
    ledgerUnary, _transportUnary, replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed exceptionalUnary ledgerUnary measureLedgerRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerReadUnary replayUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Omega ∨ hsame row A ∨ hsame row L ∨
              hsame row ledgerRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A L ledgerRead ∧ Cont ledgerRead C consumerRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, measureLedgerRoute, consumerRoute, provenancePkg⟩
  }
  exact ⟨cert, ledgerReadUnary, consumerReadUnary⟩

theorem Egorov_measure_ledger_obligation_consumer_handoff [AskSetup] [PackageSetup]
    {M Omega F X S R A W U L H C P N ledgerRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier M Omega F X S R A W U L H C P N bundle pkg ->
      Cont A W U ->
        Cont U L C ->
          Cont A L ledgerRead ->
            Cont ledgerRead C consumerRead ->
              PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row U ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row W ∨ hsame row U ∨ hsame row L)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A W U ∧ Cont U L C ∧ PkgSig bundle P pkg)
                    hsame ∧
                  SemanticNameCert
                      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row Omega ∨ hsame row A ∨ hsame row L ∨
                          hsame row ledgerRead ∨ hsame row consumerRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont A L ledgerRead ∧
                          Cont ledgerRead C consumerRead ∧ PkgSig bundle P pkg)
                      hsame ∧
                    UnaryHistory ledgerRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier exceptionalWindowRoute uniformityLedgerRoute measureLedgerRoute
    consumerRoute provenancePkg
  have obligationSurface :=
    EgorovCarrier_namecert_obligations carrier exceptionalWindowRoute uniformityLedgerRoute
      provenancePkg
  obtain ⟨localCert, exceptionalUnary, _windowUnary, _uniformityUnary, ledgerUnary⟩ :=
    obligationSurface
  obtain ⟨_packetWitness, _measureUnary, _probUnary, _familyUnary, _limitUnary,
    _scheduleUnary, _readbackUnary, _exceptionalUnary, _windowUnaryCarrier,
    _uniformityUnaryCarrier, _ledgerUnaryCarrier, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed exceptionalUnary ledgerUnary measureLedgerRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerReadUnary replayUnary consumerRoute
  have consumerCert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Omega ∨ hsame row A ∨ hsame row L ∨
              hsame row ledgerRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A L ledgerRead ∧ Cont ledgerRead C consumerRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, measureLedgerRoute, consumerRoute, provenancePkg⟩
  }
  exact ⟨localCert, consumerCert, ledgerReadUnary, consumerReadUnary⟩

end BEDC.Derived.EgorovUp
