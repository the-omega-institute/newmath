import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SternBrocotUp.FareyNeighborBoundary

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SternBrocotFareyNeighborBoundary [AskSetup] [PackageSetup]
    {address lower upper mediantRow farey branch output readback transport replay provenance
      localName boundaryRead treeRead streamRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory address ∧ UnaryHistory lower ∧ UnaryHistory upper ∧
        UnaryHistory mediantRow ∧ UnaryHistory farey ∧ UnaryHistory branch ∧
          UnaryHistory output ∧ UnaryHistory readback ∧ UnaryHistory transport ∧
            UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
              PkgSig bundle provenance pkg →
      Cont address lower boundaryRead →
        Cont boundaryRead upper mediantRow →
          Cont mediantRow farey treeRead →
            Cont treeRead readback streamRead →
              PkgSig bundle streamRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row streamRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row address ∨ hsame row lower ∨ hsame row upper ∨
                        hsame row mediantRow ∨ hsame row farey ∨ hsame row branch ∨
                          hsame row output ∨ hsame row readback ∨ hsame row transport ∨
                            hsame row replay ∨ hsame row provenance ∨
                              hsame row localName ∨ hsame row boundaryRead ∨
                                hsame row treeRead ∨ hsame row streamRead)
                    (fun row : BHist => UnaryHistory row ∧ PkgSig bundle streamRead pkg)
                    hsame ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory treeRead ∧
                    UnaryHistory streamRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute mediantRoute treeRoute streamRoute streamPkg
  obtain ⟨addressUnary, lowerUnary, upperUnary, _mediantUnary, fareyUnary, _branchUnary,
    _outputUnary, readbackUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _provenancePkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed addressUnary lowerUnary boundaryRoute
  have mediantUnary : UnaryHistory mediantRow :=
    unary_cont_closed boundaryUnary upperUnary mediantRoute
  have treeUnary : UnaryHistory treeRead :=
    unary_cont_closed mediantUnary fareyUnary treeRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed treeUnary readbackUnary streamRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row streamRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row address ∨ hsame row lower ∨ hsame row upper ∨ hsame row mediantRow ∨
              hsame row farey ∨ hsame row branch ∨ hsame row output ∨ hsame row readback ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row boundaryRead ∨ hsame row treeRead ∨
                    hsame row streamRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle streamRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro streamRead ⟨hsame_refl streamRead, streamUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, streamPkg⟩
  }
  exact ⟨cert, boundaryUnary, treeUnary, streamUnary⟩

end BEDC.Derived.SternBrocotUp.FareyNeighborBoundary
