import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberPhaseRealSourceLock [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow phaseRead
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      UnaryHistory phaseRead →
        Cont provenance phaseRead consumerRead →
          PkgSig bundle consumerRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row radius ∨ hsame row route ∨ hsame row consumerRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
                    Cont provenance phaseRead consumerRead ∧ hsame row consumerRead)
                hsame ∧
              UnaryHistory radius ∧ UnaryHistory consumerRead ∧ Cont cover window radius ∧
                Cont radius mesh route ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier phaseUnary provenancePhaseConsumer consumerPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    provenanceUnary, _nameRowUnary, coverWindowRadius, radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed provenanceUnary phaseUnary provenancePhaseConsumer
  have sourceConsumer :
      (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row) consumerRead := by
    exact ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
        (fun row : BHist => hsame row radius ∨ hsame row route ∨ hsame row consumerRead)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg ∧
            Cont provenance phaseRead consumerRead ∧ hsame row consumerRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
        cases same
        exact source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, provenancePhaseConsumer, source.left⟩
  }
  exact
    ⟨cert, radiusUnary, consumerUnary, coverWindowRadius, radiusMeshRoute, consumerPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
