import BEDC.Derived.KleeneTreeUp.NameCertObligations

namespace BEDC.Derived.KleeneTreeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KleeneTreeCarrier_scoped_prefix_choice_refusal [AskSetup] [PackageSetup]
    {tree boolLedger prefixSpine streamSchedule obstruction transport traversal provenance
      localName prefixRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KleeneTreeCarrier tree boolLedger prefixSpine streamSchedule obstruction transport traversal
        provenance localName bundle pkg →
      Cont prefixSpine obstruction prefixRead →
        Cont prefixRead traversal refusalRead →
          PkgSig bundle refusalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row tree ∨ hsame row boolLedger ∨ hsame row prefixSpine ∨
                    hsame row streamSchedule ∨ hsame row obstruction ∨
                      hsame row prefixRead ∨ hsame row refusalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont prefixSpine obstruction prefixRead ∧
                    Cont prefixRead traversal refusalRead ∧ PkgSig bundle refusalRead pkg)
                hsame ∧
              UnaryHistory prefixRead ∧ UnaryHistory refusalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier prefixObstruction prefixTraversal refusalPkg
  obtain ⟨_treeUnary, _boolUnary, prefixUnary, _streamUnary, obstructionUnary,
    _transportUnary, traversalUnary, _provenanceUnary, _localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed prefixUnary obstructionUnary prefixObstruction
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed prefixReadUnary traversalUnary prefixTraversal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tree ∨ hsame row boolLedger ∨ hsame row prefixSpine ∨
              hsame row streamSchedule ∨ hsame row obstruction ∨ hsame row prefixRead ∨
                hsame row refusalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont prefixSpine obstruction prefixRead ∧
              Cont prefixRead traversal refusalRead ∧ PkgSig bundle refusalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalRead ⟨hsame_refl refusalRead, refusalReadUnary⟩
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
      exact ⟨source.right, prefixObstruction, prefixTraversal, refusalPkg⟩
  }
  exact ⟨cert, prefixReadUnary, refusalReadUnary⟩

end BEDC.Derived.KleeneTreeUp
