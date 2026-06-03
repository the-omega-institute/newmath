import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
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

theorem PolishSpaceSeparableDenseScheduleHandoff [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName denseRead completionRead denseHandoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger
        alignment transport route provenance localName bundle pkg →
      Cont separable stream denseRead →
        Cont complete stream completionRead →
          Cont denseRead readback denseHandoff →
            PkgSig bundle localName pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row denseHandoff ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row separable ∨ hsame row stream ∨ hsame row readback ∨
                      hsame row denseRead ∨ hsame row denseHandoff)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle localName pkg)
                  hsame ∧
                UnaryHistory denseRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory denseHandoff := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier separableStreamDense completeStreamCompletion denseReadbackHandoff
    localNamePkg
  obtain ⟨_metricUnary, completeUnary, separableUnary, streamUnary, readbackUnary,
    _ledgerUnary, _alignmentUnary, _transportUnary, _localNameUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, _ledgerTransportRoute, provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed completeUnary streamUnary completeStreamCompletion
  have handoffUnary : UnaryHistory denseHandoff :=
    unary_cont_closed denseUnary readbackUnary denseReadbackHandoff
  have sourceHandoff :
      (fun row : BHist => hsame row denseHandoff ∧ UnaryHistory row) denseHandoff := by
    exact ⟨hsame_refl denseHandoff, handoffUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row denseHandoff ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row separable ∨ hsame row stream ∨ hsame row readback ∨
              hsame row denseRead ∨ hsame row denseHandoff)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denseHandoff sourceHandoff
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, denseUnary, completionUnary, handoffUnary⟩

end BEDC.Derived.PolishspaceUp
