import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_consumer_nonescape [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
            (fun row : BHist => Cont terminal normal row ∧ PkgSig bundle consumer pkg)
            (fun _row : BHist =>
              UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
                UnaryHistory normal ∧ UnaryHistory continuation ∧ PkgSig bundle provenance pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet terminalNormalConsumer consumerPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed terminalUnary normalUnary terminalNormalConsumer
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport terminalNormalConsumer (hsame_symm source.left),
          consumerPkg⟩
    ledger_sound := by
      intro _row _source
      exact
        ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
          provenancePkg⟩
  }

end BEDC.Derived.ZnormalUp
