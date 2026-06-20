import BEDC.Derived.CompactOperatorUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CompactOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactOperatorCarrier_obligation_scope [AskSetup] [PackageSetup]
    {source target operator imageNet modulus transport replay provenance localName compactRead
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.CompactOperatorCarrier source target operator imageNet modulus transport replay
        provenance localName bundle pkg ->
      Cont operator imageNet compactRead ->
        Cont compactRead modulus scopeRead ->
          PkgSig bundle scopeRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row target ∨ hsame row operator ∨
                    hsame row imageNet ∨ hsame row modulus ∨ hsame row compactRead ∨
                      hsame row scopeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont operator imageNet compactRead ∧
                    Cont compactRead modulus scopeRead ∧ PkgSig bundle scopeRead pkg)
                hsame ∧
              UnaryHistory compactRead ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: CompactOperatorCarrier BHist ProbeBundle Pkg Cont hsame
  intro carrier compactRoute scopeRoute scopePkg
  obtain ⟨_sourceUnary, _targetUnary, operatorUnary, imageNetUnary, modulusUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _sourceTargetOperator,
    _operatorImageNetModulus, _provenanceTransportLocalName, _localNamePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed operatorUnary imageNetUnary compactRoute
  have scopeUnary : UnaryHistory scopeRead :=
    unary_cont_closed compactUnary modulusUnary scopeRoute
  have sourceScope :
      (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row) scopeRead := by
    exact ⟨hsame_refl scopeRead, scopeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row operator ∨
              hsame row imageNet ∨ hsame row modulus ∨ hsame row compactRead ∨
                hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont operator imageNet compactRead ∧
              Cont compactRead modulus scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead sourceScope
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, compactRoute, scopeRoute, scopePkg⟩
  }
  exact ⟨cert, compactUnary, scopeUnary⟩

end BEDC.Derived.CompactOperatorUp
