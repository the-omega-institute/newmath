import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCoveringNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedCoveringNumberCarrier [AskSetup] [PackageSetup]
    (metric request tolerance centers budget witness transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory metric ∧ UnaryHistory request ∧ UnaryHistory tolerance ∧
    UnaryHistory centers ∧ UnaryHistory budget ∧ UnaryHistory witness ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont request tolerance centers ∧
          Cont centers budget witness ∧ Cont transport replay localName ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem LocatedCoveringNumberNameCertObligations [AskSetup] [PackageSetup]
    {metric request tolerance centers budget witness transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCoveringNumberCarrier metric request tolerance centers budget witness transport
        replay provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist => hsame row localName ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row metric ∨ hsame row request ∨ hsame row tolerance ∨
            hsame row centers ∨ hsame row budget ∨ hsame row witness ∨
              hsame row localName)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
            hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨_metricUnary, _requestUnary, _toleranceUnary, _centersUnary, _budgetUnary,
    _witnessUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    _requestToleranceCenters, _centersBudgetWitness, _transportReplayName,
    provenancePkg, localNamePkg⟩ := carrier
  have sourceLocalName :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact ⟨hsame_refl localName, localNameUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocalName
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
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }

end BEDC.Derived.LocatedCoveringNumberUp
