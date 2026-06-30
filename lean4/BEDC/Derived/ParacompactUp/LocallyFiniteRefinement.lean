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

theorem ParacompactCarrier_refinement_namecert_obligations [AskSetup] [PackageSetup]
    {topology window cover refinement localFinite coverage normal urysohn metric transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory topology ->
      UnaryHistory window ->
        UnaryHistory cover ->
          UnaryHistory refinement ->
            UnaryHistory localFinite ->
              UnaryHistory coverage ->
                UnaryHistory normal ->
                  UnaryHistory urysohn ->
                    UnaryHistory metric ->
                      UnaryHistory transport ->
                        UnaryHistory replay ->
                          UnaryHistory provenance ->
                            UnaryHistory localName ->
                              Cont topology window cover ->
                                Cont cover refinement coverage ->
                                  Cont window refinement localFinite ->
                                    Cont normal urysohn refinement ->
                                      Cont metric transport replay ->
                                        Cont replay provenance localName ->
                                          PkgSig bundle provenance pkg ->
                                            PkgSig bundle localName pkg ->
                                              SemanticNameCert
                                                (fun row : BHist =>
                                                  hsame row localName ∧ UnaryHistory row)
                                                (fun row : BHist =>
                                                  hsame row topology ∨ hsame row cover ∨
                                                    hsame row refinement ∨
                                                      hsame row localFinite ∨
                                                        hsame row coverage ∨ hsame row normal ∨
                                                          hsame row urysohn ∨ hsame row metric ∨
                                                            Cont cover refinement coverage ∨
                                                              Cont window refinement localFinite)
                                                (fun row : BHist =>
                                                  PkgSig bundle provenance pkg ∧
                                                    PkgSig bundle localName pkg ∧
                                                      hsame row localName)
                                                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _topologyUnary _windowUnary _coverUnary _refinementUnary _localFiniteUnary
    _coverageUnary _normalUnary _urysohnUnary _metricUnary _transportUnary _replayUnary
    _provenanceUnary localNameUnary _topologyWindowCover coverRefinementCoverage
    windowRefinementLocalFinite _normalUrysohnRefinement _metricTransportReplay
    _replayProvenanceLocal provenancePkg localNamePkg
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inl coverRefinementCoverage))))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }

end BEDC.Derived.ParacompactUp
