import BEDC.Derived.DyadicIntervalCoverUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRegSeqRatRoute [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N windowRead readbackRead coverRead sealRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
        UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg) →
      Cont W Q windowRead →
        Cont windowRead M readbackRead →
          Cont readbackRead V coverRead →
            Cont coverRead A sealRead →
              Cont sealRead N namedRead →
                PkgSig bundle namedRead pkg →
                  UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory M ∧
                    UnaryHistory R ∧ UnaryHistory V ∧ UnaryHistory A ∧
                      UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                        UnaryHistory coverRead ∧ UnaryHistory sealRead ∧
                          UnaryHistory namedRead ∧ Cont W Q windowRead ∧
                            Cont windowRead M readbackRead ∧
                              Cont readbackRead V coverRead ∧
                                Cont coverRead A sealRead ∧ Cont sealRead N namedRead ∧
                                  PkgSig bundle P pkg ∧
                                    PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrierRows windowRoute readbackRoute coverRoute sealRoute namedRoute namedPkg
  obtain ⟨_unaryL, _unaryU, unaryM, unaryR, unaryV, unaryW, unaryQ, unaryA,
    _unaryH, _unaryC, _unaryP, unaryN, provenancePkg, _localNamePkg⟩ := carrierRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryW unaryQ windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryM readbackRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed readbackUnary unaryV coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary unaryA sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  exact
    ⟨unaryW, unaryQ, unaryM, unaryR, unaryV, unaryA, windowUnary, readbackUnary,
      coverUnary, sealUnary, namedUnary, windowRoute, readbackRoute, coverRoute,
      sealRoute, namedRoute, provenancePkg, namedPkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
