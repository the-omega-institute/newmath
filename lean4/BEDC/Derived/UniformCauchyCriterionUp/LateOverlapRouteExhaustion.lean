import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_late_overlap_route_exhaustion
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name left right
      overlap route hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index tail left →
        Cont index tail right →
          Cont left right overlap →
            Cont overlap sealRow route →
              PkgSig bundle route pkg →
                UnaryHistory overlap ∧ UnaryHistory route ∧ hsame left right ∧
                  Cont left right overlap ∧ Cont overlap sealRow route ∧
                    PkgSig bundle route pkg ∧
                      (Cont route (BHist.e1 hostTail) overlap → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet indexTailLeft indexTailRight leftRightOverlap overlapSealRoute routePkg
  obtain ⟨indexUnary, _windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have leftUnary : UnaryHistory left :=
    unary_cont_closed indexUnary tailUnary indexTailLeft
  have rightUnary : UnaryHistory right :=
    unary_cont_closed indexUnary tailUnary indexTailRight
  have overlapUnary : UnaryHistory overlap :=
    unary_cont_closed leftUnary rightUnary leftRightOverlap
  have routeUnary : UnaryHistory route :=
    unary_cont_closed overlapUnary sealRowUnary overlapSealRoute
  have sameLeftRight : hsame left right :=
    cont_deterministic indexTailLeft indexTailRight
  exact
    ⟨overlapUnary, routeUnary, sameLeftRight, leftRightOverlap, overlapSealRoute,
      routePkg,
      (fun back =>
        cont_mutual_extension_right_tail_absurd.right overlapSealRoute back)⟩

end BEDC.Derived.UniformCauchyCriterionUp
