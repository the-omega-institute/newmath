import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_refinement_handoff [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name rootUse
      refinement handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail rootUse →
        Cont rootUse sealRow refinement →
          Cont index sealRow handoff →
            PkgSig bundle refinement pkg →
              PkgSig bundle handoff pkg →
                UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                  UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                    UnaryHistory rootUse ∧ UnaryHistory refinement ∧ UnaryHistory handoff ∧
                      Cont index tail rootUse ∧ Cont rootUse sealRow refinement ∧
                        Cont index sealRow handoff ∧ PkgSig bundle name pkg ∧
                          PkgSig bundle refinement pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailRoot rootSealRefinement indexSealHandoff refinementPkg handoffPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have rootUseUnary : UnaryHistory rootUse :=
    unary_cont_closed indexUnary tailUnary indexTailRoot
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed rootUseUnary sealRowUnary rootSealRefinement
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed indexUnary sealRowUnary indexSealHandoff
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      rootUseUnary, refinementUnary, handoffUnary, indexTailRoot, rootSealRefinement,
      indexSealHandoff, namePkg, refinementPkg, handoffPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
