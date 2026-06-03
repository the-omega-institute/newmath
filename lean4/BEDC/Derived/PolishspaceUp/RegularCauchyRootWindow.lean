import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRegularCauchyRootWindow [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName regularWindow terminalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg ->
      Cont readback alignment regularWindow ->
        Cont regularWindow localName terminalSeal ->
          PkgSig bundle terminalSeal pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row metric ∨ hsame row stream ∨ hsame row readback ∨
                    hsame row alignment ∨ hsame row regularWindow ∨ hsame row terminalSeal)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle terminalSeal pkg)
                hsame ∧
              UnaryHistory regularWindow ∧ UnaryHistory terminalSeal := by
  -- BEDC touchpoint anchor: PolishspaceRootCauchyBasisCarrier BHist Cont ProbeBundle PkgSig
  intro carrier readbackAlignmentRegular regularLocalTerminal terminalPkg
  obtain ⟨metricUnary, _completeUnary, _separableUnary, streamUnary, readbackUnary,
    _ledgerUnary, alignmentUnary, _transportUnary, localNameUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, _ledgerTransportRoute, provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory regularWindow :=
    unary_cont_closed readbackUnary alignmentUnary readbackAlignmentRegular
  have terminalUnary : UnaryHistory terminalSeal :=
    unary_cont_closed regularUnary localNameUnary regularLocalTerminal
  have sourceTerminal :
      (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row) terminalSeal := by
    exact ⟨hsame_refl terminalSeal, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row stream ∨ hsame row readback ∨
              hsame row alignment ∨ hsame row regularWindow ∨ hsame row terminalSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle terminalSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalSeal sourceTerminal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, terminalPkg⟩
  }
  exact ⟨cert, regularUnary, terminalUnary⟩

end BEDC.Derived.PolishspaceUp
