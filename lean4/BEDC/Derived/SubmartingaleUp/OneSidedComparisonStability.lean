import BEDC.Derived.SubmartingaleUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubmartingaleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubmartingaleCarrier_one_sided_comparison_stability [AskSetup] [PackageSetup]
    {omega randomVar condExp filtration endpoint expectation comparison time transport replay
      provenance localName comparisonRead transportedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubmartingaleCarrier omega randomVar condExp filtration endpoint expectation comparison time
        transport replay provenance localName bundle pkg →
      Cont endpoint expectation comparisonRead →
        hsame transportedRead comparisonRead →
          Cont transportedRead replay replayRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row endpoint ∨ hsame row expectation ∨ hsame row comparison ∨
                        hsame row transport ∨ hsame row replay ∨ hsame row comparisonRead ∨
                          hsame row transportedRead ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont endpoint expectation comparisonRead ∧
                        Cont transportedRead replay replayRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory comparisonRead ∧ UnaryHistory transportedRead ∧
                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier comparisonRoute sameTransport replayRoute provenancePkg localNamePkg
  obtain ⟨_omegaUnary, _randomVarUnary, _condExpUnary, _filtrationUnary, endpointUnary,
    expectationUnary, _comparisonUnary, _timeUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _localNameCarrierPkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed endpointUnary expectationUnary comparisonRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport comparisonUnary (hsame_symm sameTransport)
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary replayUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row endpoint ∨ hsame row expectation ∨ hsame row comparison ∨
              hsame row transport ∨ hsame row replay ∨ hsame row comparisonRead ∨
                hsame row transportedRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont endpoint expectation comparisonRead ∧
              Cont transportedRead replay replayRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, comparisonRoute, replayRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, comparisonUnary, transportedUnary, replayReadUnary⟩

end BEDC.Derived.SubmartingaleUp
