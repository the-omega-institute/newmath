import BEDC.Derived.ObserverRegularUp.Carrier

namespace BEDC.Derived.ObserverRegularUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverRegularCarrier_resolving_window_ledger_exactness [AskSetup] [PackageSetup]
    {alphabet resolvingState schedule window readback transport route provenance name
      selectedWindow consumer handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverRegularCarrier alphabet resolvingState schedule window readback transport route
        provenance name bundle pkg →
      Cont resolvingState window selectedWindow →
        Cont selectedWindow readback consumer →
          Cont consumer provenance handoff →
            PkgSig bundle handoff pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row resolvingState ∨ hsame row selectedWindow ∨
                      hsame row consumer ∨ hsame row handoff)
                  (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
                  hsame ∧
                UnaryHistory selectedWindow ∧ UnaryHistory consumer ∧
                  UnaryHistory handoff ∧ Cont resolvingState window selectedWindow ∧
                    Cont selectedWindow readback consumer ∧
                      Cont consumer provenance handoff ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier selectedRoute consumerRoute handoffRoute handoffPkg
  obtain ⟨_alphabetUnary, resolvingStateUnary, _scheduleUnary, windowUnary, readbackUnary,
    _transportUnary, _routeUnary, provenanceUnary, _nameUnary, _alphabetResolvingSchedule,
    _scheduleWindowReadback, _readbackTransportRoute, _routeNameProvenance, provenancePkg,
    _semanticCert⟩ := carrier
  have selectedUnary : UnaryHistory selectedWindow :=
    unary_cont_closed resolvingStateUnary windowUnary selectedRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed selectedUnary readbackUnary consumerRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed consumerUnary provenanceUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row resolvingState ∨ hsame row selectedWindow ∨
              hsame row consumer ∨ hsame row handoff)
          (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff ⟨hsame_refl handoff, handoffUnary⟩
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
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffPkg⟩
  }
  exact
    ⟨cert,
      selectedUnary,
      consumerUnary,
      handoffUnary,
      selectedRoute,
      consumerRoute,
      handoffRoute,
      provenancePkg,
      handoffPkg⟩

end BEDC.Derived.ObserverRegularUp
