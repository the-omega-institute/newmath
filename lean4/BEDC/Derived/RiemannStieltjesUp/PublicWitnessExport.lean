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

theorem RiemannStieltjesCarrier_public_witness_export [AskSetup] [PackageSetup]
    {regulated variation tagged step handoff sealRow transportRow replayRow provenance nameRow
      witnessRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannStieltjesCarrier regulated variation tagged step handoff sealRow transportRow
      replayRow provenance nameRow bundle pkg →
      Cont handoff sealRow witnessRead →
        Cont witnessRead replayRow publicRead →
          PkgSig bundle publicRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row regulated ∨ hsame row variation ∨ hsame row tagged ∨
                    hsame row step ∨ hsame row handoff ∨ hsame row sealRow ∨
                      hsame row witnessRead ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont handoff sealRow witnessRead ∧
                    Cont witnessRead replayRow publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory witnessRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier witnessRoute publicRoute publicPkg
  obtain ⟨_regulatedUnary, _variationUnary, _taggedUnary, _stepUnary, handoffUnary,
    sealUnary, _transportUnary, replayUnary, _provenanceUnary, _regulatedVariationTagged,
    _taggedStepHandoff, _handoffSealReplay, _namePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed handoffUnary sealUnary witnessRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed witnessUnary replayUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regulated ∨ hsame row variation ∨ hsame row tagged ∨
              hsame row step ∨ hsame row handoff ∨ hsame row sealRow ∨
                hsame row witnessRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont handoff sealRow witnessRead ∧
              Cont witnessRead replayRow publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, witnessRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, witnessUnary, publicUnary⟩

end BEDC.Derived.RiemannStieltjesUp
