import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRootBasisNamecertExhaustion [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      Cont route localName consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                  hsame row stream ∨ hsame row readback ∨ hsame row alignment ∨
                    hsame row consumer)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory route ∧ UnaryHistory consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeLocalConsumer consumerPkg
  obtain ⟨metricUnary, _completeUnary, _separableUnary, _streamUnary, _readbackUnary,
    ledgerUnary, _alignmentUnary, transportUnary, localNameUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, ledgerTransportRoute, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory route :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary localNameUnary routeLocalConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row alignment ∨
                hsame row consumer)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, routeUnary, consumerUnary⟩

end BEDC.Derived.PolishspaceUp
