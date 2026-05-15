import BEDC.Derived.CauchyWitnessLedgerUp.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CauchyWitnessLedgerCarrier_root_consumer_exhaustion [AskSetup] [PackageSetup]
    {Q B S K H C P N endpoint consumer : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    Cont Q B S →
      Cont S K endpoint →
        Cont endpoint N consumer →
          hsame N endpoint →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row consumer ∧
                    ∃ packet : CauchyWitnessLedgerUp,
                      packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                (fun row : BHist =>
                  Cont Q B S ∧ Cont S K endpoint ∧ Cont endpoint N consumer ∧
                    hsame row consumer)
                (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeS routeEndpoint routeConsumer _sameEndpoint consumerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer
          ⟨hsame_refl consumer,
            Exists.intro (CauchyWitnessLedgerUp.mk Q B S K H C P N) rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨routeS, routeEndpoint, routeConsumer, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }

theorem CauchyWitnessLedgerCarrier_streamname_window_source_lock [AskSetup] [PackageSetup]
    {Q B S K H C P N streamWindow observationRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B S →
      Cont B H streamWindow →
        Cont streamWindow S observationRead →
          Cont observationRead K sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row sealRead ∧
                    ∃ packet : CauchyWitnessLedgerUp,
                      packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
                (fun row : BHist =>
                  Cont Q B S ∧ Cont B H streamWindow ∧
                    Cont streamWindow S observationRead ∧
                      Cont observationRead K sealRead ∧ hsame row sealRead)
                (fun row : BHist => hsame row sealRead ∧ PkgSig bundle sealRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeS routeWindow routeObservation routeSeal sealPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead
          ⟨hsame_refl sealRead,
            Exists.intro (CauchyWitnessLedgerUp.mk Q B S K H C P N) rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨routeS, routeWindow, routeObservation, routeSeal, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealPkg⟩
  }

theorem CauchyWitnessLedgerCarrier_root_budget_refusal_boundary [AskSetup] [PackageSetup]
    {Q B S K H C P N endpoint refused : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    Cont Q B S →
      Cont S K endpoint →
        hsame refused endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row endpoint ∧
                  ∃ packet : CauchyWitnessLedgerUp,
                    packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
              (fun row : BHist => Cont Q B S ∧ Cont S K endpoint ∧ hsame row endpoint)
              (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeS routeEndpoint refusedSame endpointPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro refused
          ⟨refusedSame,
            Exists.intro (CauchyWitnessLedgerUp.mk Q B S K H C P N) rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨routeS, routeEndpoint, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
