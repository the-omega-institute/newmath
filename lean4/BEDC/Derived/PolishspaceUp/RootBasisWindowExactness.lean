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

theorem PolishspaceRootBasisWindowExactness [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName basisRead completionRead denseRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger
        alignment transport route provenance localName bundle pkg →
      Cont metric stream basisRead →
        Cont alignment complete completionRead →
          Cont alignment separable denseRead →
            Cont completionRead denseRead finalRead →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row metric ∨ hsame row stream ∨ hsame row readback ∨
                        hsame row alignment ∨ hsame row finalRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory basisRead ∧ UnaryHistory completionRead ∧
                    UnaryHistory denseRead ∧ UnaryHistory finalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont SemanticNameCert hsame UnaryHistory
  intro carrier metricStreamBasis alignmentCompleteRead alignmentSeparableRead
    completionDenseFinal localNamePkg
  obtain ⟨metricUnary, completeUnary, separableUnary, streamUnary, _readbackUnary,
    _ledgerUnary, alignmentUnary, _transportUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, _ledgerTransportRoute, provenancePkg⟩ := carrier
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed metricUnary streamUnary metricStreamBasis
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed alignmentUnary completeUnary alignmentCompleteRead
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed alignmentUnary separableUnary alignmentSeparableRead
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed completionUnary denseUnary completionDenseFinal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row stream ∨ hsame row readback ∨
              hsame row alignment ∨ hsame row finalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finalRead
        (And.intro (hsame_refl finalRead) finalUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro (hsame_trans (hsame_symm same) source.left)
          (unary_transport source.right same)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact And.intro source.right (And.intro provenancePkg localNamePkg)
  }
  exact ⟨cert, basisUnary, completionUnary, denseUnary, finalUnary⟩

end BEDC.Derived.PolishspaceUp
