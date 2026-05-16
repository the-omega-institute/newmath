import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_late_boundary_formal_target_packet [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name familyRead
      sealRead overlapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg ->
      Cont index tail familyRead ->
        Cont tail sealRow sealRead ->
          Cont familyRead sealRead overlapRead ->
            PkgSig bundle overlapRead pkg ->
              UnaryHistory index ∧ UnaryHistory windows ∧ UnaryHistory modulus ∧
                UnaryHistory tolerance ∧ UnaryHistory tail ∧ UnaryHistory sealRow ∧
                  UnaryHistory familyRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory overlapRead ∧ Cont index windows modulus ∧
                      Cont modulus tolerance tail ∧ Cont index tail familyRead ∧
                        Cont tail sealRow sealRead ∧ Cont familyRead sealRead overlapRead ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle overlapRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet indexTailFamily tailSealRead familySealOverlap overlapPkg
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, indexWindowsModulus,
    modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, namePkg⟩ :=
    packet
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed indexUnary tailUnary indexTailFamily
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have overlapUnary : UnaryHistory overlapRead :=
    unary_cont_closed familyUnary sealReadUnary familySealOverlap
  exact
    ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
      familyUnary, sealReadUnary, overlapUnary, indexWindowsModulus, modulusToleranceTail,
      indexTailFamily, tailSealRead, familySealOverlap, namePkg, overlapPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
