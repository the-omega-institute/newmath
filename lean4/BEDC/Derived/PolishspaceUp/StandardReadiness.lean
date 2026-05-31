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

theorem PolishspaceStandardReadiness [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName completionRead separableRead handoffRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg ->
      Cont metric complete completionRead ->
        Cont metric separable separableRead ->
          Cont completionRead separableRead handoffRead ->
            Cont handoffRead readback realSeal ->
              PkgSig bundle realSeal pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                        hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                          hsame row alignment ∨ hsame row transport ∨ hsame row route ∨
                            hsame row provenance ∨ hsame row localName ∨
                              hsame row completionRead ∨ hsame row separableRead ∨
                                hsame row handoffRead ∨ hsame row realSeal)
                    (fun row : BHist =>
                      hsame row realSeal ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory completionRead ∧ UnaryHistory separableRead ∧
                    UnaryHistory handoffRead ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: PolishspaceRootCauchyBasisCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier metricCompleteRead metricSeparableRead completionSeparableHandoff
    handoffReadbackSeal realSealPkg
  obtain ⟨metricUnary, completeUnary, separableUnary, _streamUnary, readbackUnary,
    _ledgerUnary, _alignmentUnary, _transportUnary, _localNameUnary,
    _metricCompleteAlignment, _alignmentStreamReadback, _ledgerTransportRoute,
    provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have separableReadUnary : UnaryHistory separableRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableRead
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionUnary separableReadUnary completionSeparableHandoff
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed handoffUnary readbackUnary handoffReadbackSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row alignment ∨ hsame row transport ∨ hsame row route ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row completionRead ∨
                    hsame row separableRead ∨ hsame row handoffRead ∨ hsame row realSeal)
          (fun row : BHist =>
            hsame row realSeal ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr source.left)))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, realSealPkg⟩
  }
  exact ⟨cert, completionUnary, separableReadUnary, handoffUnary, realSealUnary⟩

end BEDC.Derived.PolishspaceUp
