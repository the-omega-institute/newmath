import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceStreamNameBasis [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport _route provenance localName
      basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory complete →
        UnaryHistory separable →
          UnaryHistory stream →
            UnaryHistory readback →
              UnaryHistory ledger →
                UnaryHistory transport →
                  Cont stream readback basisRead →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row stream ∨ hsame row readback ∨ hsame row basisRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle localName pkg)
                            hsame ∧
                          UnaryHistory basisRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro _metricUnary _completeUnary _separableUnary streamUnary readbackUnary _ledgerUnary
    _transportUnary streamReadbackBasis provenancePkg localNamePkg
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed streamUnary readbackUnary streamReadbackBasis
  have sourceBasis :
      (fun row : BHist => hsame row basisRead ∧ UnaryHistory row) basisRead := by
    exact ⟨hsame_refl basisRead, basisUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row basisRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro basisRead sourceBasis
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, basisUnary⟩

end BEDC.Derived.PolishspaceUp
