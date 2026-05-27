import BEDC.Derived.CauchyCompletionReflectorUp

namespace BEDC.Derived.CauchyCompletionReflectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionReflectorPacket_unit_counit_scope [AskSetup] [PackageSetup]
    {source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName exported scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionReflectorPacket source completionObject unit counit idempotent extension
        reflection transport componentTransport replay provenance localName exported bundle pkg →
      Cont unit counit scopeRead →
        PkgSig bundle scopeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row unit ∨ hsame row completionObject ∨
                  hsame row counit ∨ hsame row transport ∨ hsame row scopeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle exported pkg ∧ PkgSig bundle scopeRead pkg)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory unit ∧ UnaryHistory completionObject ∧
              UnaryHistory counit ∧ UnaryHistory transport ∧ UnaryHistory scopeRead ∧
                Cont source unit completionObject ∧ Cont completionObject counit transport ∧
                  Cont unit counit scopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet scopeRoute scopePkg
  obtain ⟨sourceUnary, completionUnary, unitUnary, counitUnary, _idempotentUnary,
    _extensionUnary, _reflectionUnary, transportUnary, _componentTransportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _exportedUnary, sourceRoute,
    completionRoute, _idempotentRoute, _componentRoute, _provenanceRoute, exportedPkg⟩ :=
      packet
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed unitUnary counitUnary scopeRoute
  have sourceScope : (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row) scopeRead :=
    ⟨hsame_refl scopeRead, scopeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row unit ∨ hsame row completionObject ∨
              hsame row counit ∨ hsame row transport ∨ hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle exported pkg ∧ PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceScope
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
        intro _row _row' sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, exportedPkg, scopePkg⟩
  }
  exact
    ⟨cert, sourceUnary, unitUnary, completionUnary, counitUnary, transportUnary, scopeUnary,
      sourceRoute, completionRoute, scopeRoute⟩

end BEDC.Derived.CauchyCompletionReflectorUp
