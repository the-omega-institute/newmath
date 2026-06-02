import BEDC.Derived.RiemannStieltjesUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RiemannStieltjesUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannStieltjesCarrier_step_integrator_exactness [AskSetup] [PackageSetup]
    {regulated variation tagged step handoff sealRow transportRow replayRow provenance nameRow
      meshRead variationRead handoffRead terminalRead stepContribution : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannStieltjesCarrier regulated variation tagged step handoff sealRow transportRow replayRow
      provenance nameRow bundle pkg ->
      Cont tagged step meshRead ->
        Cont variation step variationRead ->
          Cont meshRead handoff handoffRead ->
            Cont handoffRead sealRow terminalRead ->
              Cont step variation stepContribution ->
                PkgSig bundle terminalRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row stepContribution ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row step ∨ hsame row variation ∨ hsame row meshRead ∨
                          hsame row variationRead ∨ hsame row stepContribution ∨
                            hsame row terminalRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont tagged step meshRead ∧
                          Cont variation step variationRead ∧
                            Cont step variation stepContribution ∧
                              PkgSig bundle terminalRead pkg)
                      hsame ∧
                    UnaryHistory meshRead ∧ UnaryHistory variationRead ∧
                      UnaryHistory handoffRead ∧ UnaryHistory terminalRead ∧
                        UnaryHistory stepContribution := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier meshRoute variationRoute handoffRoute terminalRoute contributionRoute
    terminalPkg
  obtain ⟨_regulatedUnary, variationUnary, taggedUnary, stepUnary, handoffUnary,
    sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _regulatedTaggedRoute,
    _taggedStepRoute, _handoffSealRoute, _namePkg⟩ := carrier
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed taggedUnary stepUnary meshRoute
  have variationReadUnary : UnaryHistory variationRead :=
    unary_cont_closed variationUnary stepUnary variationRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed meshUnary handoffUnary handoffRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed handoffReadUnary sealUnary terminalRoute
  have contributionUnary : UnaryHistory stepContribution :=
    unary_cont_closed stepUnary variationUnary contributionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stepContribution ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row step ∨ hsame row variation ∨ hsame row meshRead ∨
              hsame row variationRead ∨ hsame row stepContribution ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tagged step meshRead ∧ Cont variation step variationRead ∧
              Cont step variation stepContribution ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro stepContribution ⟨hsame_refl stepContribution, contributionUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, meshRoute, variationRoute, contributionRoute, terminalPkg⟩
  }
  exact
    ⟨cert, meshUnary, variationReadUnary, handoffReadUnary, terminalReadUnary,
      contributionUnary⟩

end BEDC.Derived.RiemannStieltjesUp
