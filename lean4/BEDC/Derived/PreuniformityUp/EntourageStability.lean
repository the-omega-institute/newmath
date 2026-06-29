import BEDC.Derived.PreuniformityUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PreuniformityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PreuniformityCarrier_entourage_stability [AskSetup] [PackageSetup]
    {source entourage base topology transport replay provenance localName entourageRead baseRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory entourage →
        UnaryHistory base →
          PkgSig bundle provenance pkg →
            PkgSig bundle localName pkg →
              hsame entourageRead entourage →
                Cont entourage base baseRead →
                  SemanticNameCert
                    (fun row : BHist => hsame row entourageRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row entourage ∨ hsame row base ∨
                        hsame row topology ∨ hsame row transport ∨ hsame row replay ∨
                          hsame row provenance ∨ hsame row localName ∨
                            hsame row entourageRead ∨ hsame row baseRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont entourage base baseRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                    UnaryHistory entourageRead ∧ UnaryHistory baseRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro _sourceUnary entourageUnary baseUnary provenancePkg localNamePkg sameRead
    entourageBase
  have entourageReadUnary : UnaryHistory entourageRead :=
    unary_transport entourageUnary (hsame_symm sameRead)
  have baseReadUnary : UnaryHistory baseRead :=
    unary_cont_closed entourageUnary baseUnary entourageBase
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row entourageRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row source ∨ hsame row entourage ∨ hsame row base ∨
            hsame row topology ∨ hsame row transport ∨ hsame row replay ∨
              hsame row provenance ∨ hsame row localName ∨ hsame row entourageRead ∨
                hsame row baseRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont entourage base baseRead ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := by
    refine
      { core :=
          { carrier_inhabited := ⟨entourageRead, hsame_refl entourageRead,
              entourageReadUnary⟩
            equiv_refl := ?_
            equiv_symm := ?_
            equiv_trans := ?_
            carrier_respects_equiv := ?_ }
        pattern_sound := ?_
        ledger_sound := ?_ }
    · intro row _source
      exact hsame_refl row
    · intro _row _other sameRows
      exact hsame_symm sameRows
    · intro _row _middle _other sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro _row _other sameRows sourceRow
      exact
        ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
          unary_transport sourceRow.right sameRows⟩
    · intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl sourceRow.left))))))))
    · intro _row sourceRow
      exact ⟨sourceRow.right, entourageBase, provenancePkg, localNamePkg⟩
  exact ⟨cert, entourageReadUnary, baseReadUnary⟩

end BEDC.Derived.PreuniformityUp
