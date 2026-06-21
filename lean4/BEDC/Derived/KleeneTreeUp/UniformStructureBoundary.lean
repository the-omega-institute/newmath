import BEDC.Derived.KleeneTreeUp.NameCertObligations

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KleeneTreeUniformStructureBoundary [AskSetup] [PackageSetup]
    {tree boolLedger listSpine stream obstruction transport traversal provenance cert uniformRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger listSpine stream obstruction transport traversal provenance
        cert bundle pkg →
      Cont stream listSpine uniformRead →
        Cont uniformRead obstruction boundaryRead →
          PkgSig bundle boundaryRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row stream ∨ hsame row listSpine ∨ hsame row obstruction ∨
                    hsame row uniformRead ∨ hsame row boundaryRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont stream listSpine uniformRead ∧
                    Cont uniformRead obstruction boundaryRead ∧
                      PkgSig bundle boundaryRead pkg)
                hsame ∧
              UnaryHistory uniformRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: KleeneTreeCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier uniformRoute boundaryRoute boundaryPkg
  obtain ⟨_treeUnary, _boolUnary, listUnary, streamUnary, obstructionUnary, _transportUnary,
    _traversalUnary, _provenanceUnary, _certUnary, _provenancePkg, _certPkg⟩ :=
    carrier
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed streamUnary listUnary uniformRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed uniformUnary obstructionUnary boundaryRoute
  have certObj :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row listSpine ∨ hsame row obstruction ∨
              hsame row uniformRead ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream listSpine uniformRead ∧
              Cont uniformRead obstruction boundaryRead ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundaryRead ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, uniformRoute, boundaryRoute, boundaryPkg⟩
  }
  exact ⟨certObj, uniformUnary, boundaryUnary⟩

end BEDC.Derived.KleeneTreeUp
