import BEDC.Derived.CauchyModulusUp.DependencyBoundary

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusPacket_explicit_modulus_standard_bridge [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule observationLedger consumptionLedger window endpoint
      handoff explicitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusPacket precision threshold tolerance schedule observationLedger consumptionLedger
        window endpoint bundle pkg →
      Cont endpoint consumptionLedger handoff →
        Cont handoff tolerance explicitRead →
          PkgSig bundle explicitRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row explicitRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row precision ∨ hsame row threshold ∨ hsame row tolerance ∨
                    hsame row schedule ∨ hsame row observationLedger ∨
                      hsame row consumptionLedger ∨ hsame row window ∨
                        hsame row endpoint ∨ hsame row handoff ∨ hsame row explicitRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont precision threshold schedule ∧
                    Cont schedule tolerance observationLedger ∧
                      Cont observationLedger consumptionLedger window ∧
                        Cont window threshold endpoint ∧ Cont endpoint consumptionLedger handoff ∧
                          Cont handoff tolerance explicitRead ∧
                            PkgSig bundle explicitRead pkg)
                hsame ∧
              UnaryHistory explicitRead ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet handoffRoute explicitRoute explicitPkg
  have boundary :=
    CauchyModulusPacket_public_consumer_boundary
      (precision := precision) (threshold := threshold) (tolerance := tolerance)
      (schedule := schedule) (observationLedger := observationLedger)
      (consumptionLedger := consumptionLedger) (window := window) (endpoint := endpoint)
      (handoff := handoff) (bundle := bundle) (pkg := pkg) packet handoffRoute
  have handoffUnary : UnaryHistory handoff :=
    boundary.right.right.right.right.right.left
  have endpointPkg : PkgSig bundle endpoint pkg :=
    boundary.right.right.right.right.right.right
  have explicitUnary : UnaryHistory explicitRead :=
    unary_cont_closed handoffUnary packet.right.right.left explicitRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row explicitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row precision ∨ hsame row threshold ∨ hsame row tolerance ∨
              hsame row schedule ∨ hsame row observationLedger ∨
                hsame row consumptionLedger ∨ hsame row window ∨ hsame row endpoint ∨
                  hsame row handoff ∨ hsame row explicitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont precision threshold schedule ∧
              Cont schedule tolerance observationLedger ∧
                Cont observationLedger consumptionLedger window ∧
                  Cont window threshold endpoint ∧ Cont endpoint consumptionLedger handoff ∧
                    Cont handoff tolerance explicitRead ∧ PkgSig bundle explicitRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro explicitRead
        ⟨hsame_refl explicitRead, explicitUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right,
          packet.right.right.right.right.right.right.right.right.left,
          packet.right.right.right.right.right.right.right.right.right.left,
          packet.right.right.right.right.right.right.right.right.right.right.left,
          packet.right.right.right.right.right.right.right.right.right.right.right.left,
          handoffRoute, explicitRoute, explicitPkg⟩
  }
  exact ⟨cert, explicitUnary, endpointPkg⟩

end BEDC.Derived.CauchyModulusUp
