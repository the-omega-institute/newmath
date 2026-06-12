import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.ParacompactUp.TasteGate

namespace BEDC.Derived.ParacompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParacompactCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {topology cover refinement coverage normal metric transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory topology ->
      UnaryHistory cover ->
        UnaryHistory refinement ->
          UnaryHistory coverage ->
            UnaryHistory normal ->
              UnaryHistory metric ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    UnaryHistory provenance ->
                      UnaryHistory localName ->
                        Cont topology cover refinement ->
                          Cont refinement coverage normal ->
                            Cont metric transport replay ->
                              Cont replay provenance localName ->
                                PkgSig bundle provenance pkg ->
                                  PkgSig bundle localName pkg ->
                                    SemanticNameCert
                                      (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row topology ∨ hsame row cover ∨
                                          hsame row refinement ∨ hsame row coverage ∨
                                            hsame row normal ∨ hsame row metric ∨
                                              Cont topology cover refinement)
                                      (fun row : BHist =>
                                        PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg ∧ hsame row localName)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _topologyUnary _coverUnary _refinementUnary _coverageUnary _normalUnary _metricUnary
    _transportUnary _replayUnary _provenanceUnary localNameUnary topologyCoverRefinement
    _refinementCoverageNormal _metricTransportReplay _replayProvenanceLocal provenancePkg
    localNamePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localName ⟨hsame_refl localName, localNameUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr topologyCoverRefinement)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }

end BEDC.Derived.ParacompactUp
