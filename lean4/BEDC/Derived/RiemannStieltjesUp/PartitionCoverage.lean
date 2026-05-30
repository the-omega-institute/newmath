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

theorem RiemannStieltjesCarrier_bounded_variation_partition_coverage
    [AskSetup] [PackageSetup]
    {regulated variation tagged step handoff sealRow transportRow replayRow provenance nameRow
      meshRead variationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannStieltjesCarrier regulated variation tagged step handoff sealRow transportRow replayRow
      provenance nameRow bundle pkg ->
      Cont tagged step meshRead ->
        Cont variation step variationRead ->
          PkgSig bundle variationRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row variationRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row tagged ∨ hsame row step ∨ hsame row variation ∨
                    hsame row meshRead ∨ hsame row variationRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont tagged step meshRead ∧
                    Cont variation step variationRead ∧ PkgSig bundle variationRead pkg)
                hsame ∧
              UnaryHistory meshRead ∧ UnaryHistory variationRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier meshRoute variationRoute variationPkg
  obtain ⟨_regulatedUnary, variationUnary, taggedUnary, stepUnary, _handoffUnary,
    _sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _regulatedTaggedRoute,
    _handoffRoute, _replayRoute, _namePkg⟩ := carrier
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed taggedUnary stepUnary meshRoute
  have variationReadUnary : UnaryHistory variationRead :=
    unary_cont_closed variationUnary stepUnary variationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row variationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tagged ∨ hsame row step ∨ hsame row variation ∨
              hsame row meshRead ∨ hsame row variationRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tagged step meshRead ∧
              Cont variation step variationRead ∧ PkgSig bundle variationRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro variationRead ⟨hsame_refl variationRead, variationReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, meshRoute, variationRoute, variationPkg⟩
  }
  exact ⟨cert, meshUnary, variationReadUnary⟩

end BEDC.Derived.RiemannStieltjesUp
