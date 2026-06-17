import BEDC.Derived.RegularCauchyRingUp

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyRingCarrier_terminal_seal_discipline [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N sumSeal negSeal
      productSeal scaleSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      Cont S ES sumSeal →
        Cont G EG negSeal →
          Cont M EM productSeal →
            Cont L EL scaleSeal →
              UnaryHistory RS ∧ UnaryHistory RG ∧ UnaryHistory RM ∧ UnaryHistory RL ∧
                UnaryHistory sumSeal ∧ UnaryHistory negSeal ∧ UnaryHistory productSeal ∧
                  UnaryHistory scaleSeal ∧ Cont S ES sumSeal ∧ Cont G EG negSeal ∧
                    Cont M EM productSeal ∧ Cont L EL scaleSeal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier sumSealRoute negSealRoute productSealRoute scaleSealRoute
  obtain ⟨_unaryA, _unaryB, _unaryWA, _unaryWB, _unaryDA, _unaryDB, sUnary, gUnary,
    mUnary, lUnary, rsUnary, rgUnary, rmUnary, rlUnary, esUnary, egUnary, emUnary,
    elUnary, _unaryH, _unaryC, _unaryP, _unaryN, _sourceWindowA, _sourceWindowB,
    _transportReplay, _provenancePkg, _namePkg⟩ := carrier
  have sumSealUnary : UnaryHistory sumSeal :=
    unary_cont_closed sUnary esUnary sumSealRoute
  have negSealUnary : UnaryHistory negSeal :=
    unary_cont_closed gUnary egUnary negSealRoute
  have productSealUnary : UnaryHistory productSeal :=
    unary_cont_closed mUnary emUnary productSealRoute
  have scaleSealUnary : UnaryHistory scaleSeal :=
    unary_cont_closed lUnary elUnary scaleSealRoute
  exact
    ⟨rsUnary, rgUnary, rmUnary, rlUnary, sumSealUnary, negSealUnary, productSealUnary,
      scaleSealUnary, sumSealRoute, negSealRoute, productSealRoute, scaleSealRoute⟩

end BEDC.Derived.RegularCauchyRingUp
