import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.Derived.PolishspaceUp.RootUnblockSurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceL10RootUnblockPackage [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName completionRead separableRead handoffRead realSeal l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg ->
      Cont metric complete completionRead ->
        Cont metric separable separableRead ->
          Cont completionRead separableRead handoffRead ->
            Cont handoffRead readback realSeal ->
              Cont realSeal ledger l10Read ->
                PkgSig bundle l10Read pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                          hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                            hsame row alignment ∨ hsame row route ∨ hsame row realSeal ∨
                              hsame row l10Read)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont realSeal ledger l10Read ∧
                          PkgSig bundle l10Read pkg)
                      hsame ∧
                    UnaryHistory realSeal ∧ UnaryHistory l10Read := by
  -- BEDC touchpoint anchor: PolishspaceRootCauchyBasisCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier metricCompleteRead metricSeparableRead completionSeparableHandoff
    handoffReadbackSeal realSealLedgerL10 l10Pkg
  obtain ⟨metricUnary, completeUnary, separableUnary, _streamUnary, readbackUnary,
    ledgerUnary, _alignmentUnary, _transportUnary, _localNameUnary,
    _metricCompleteAlignment, _alignmentStreamReadback, _ledgerTransportRoute,
    _provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have separableReadUnary : UnaryHistory separableRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableRead
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionUnary separableReadUnary completionSeparableHandoff
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed handoffUnary readbackUnary handoffReadbackSeal
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed realSealUnary ledgerUnary realSealLedgerL10
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row alignment ∨ hsame row route ∨ hsame row realSeal ∨
                  hsame row l10Read)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont realSeal ledger l10Read ∧ PkgSig bundle l10Read pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro l10Read ⟨hsame_refl l10Read, l10Unary⟩
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
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealLedgerL10, l10Pkg⟩
  }
  exact ⟨cert, realSealUnary, l10Unary⟩

theorem PolishSpaceL10RootUnblockPackage [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      completionRead denseRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg →
      Cont complete stream completionRead →
        Cont separable stream denseRead →
          Cont completionRead denseRead rootRead →
            PkgSig bundle rootRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                      hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                        hsame row rootRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg ∧ PkgSig bundle rootRead pkg)
                  hsame ∧
                UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                  UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface completionRoute denseRoute rootRoute rootPkg
  obtain ⟨metricUnary, completeUnary, separableUnary, streamUnary, _readbackUnary,
    _ledgerUnary, _transportUnary, _metricCompleteRoute, _metricSeparableRoute,
    _replayRoute, provenancePkg, localNamePkg⟩ := surface
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completionRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary denseRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed completionUnary denseUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row ledger ∨
                hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
      exact ⟨source.right, provenancePkg, localNamePkg, rootPkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, rootUnary⟩

end BEDC.Derived.PolishspaceUp
