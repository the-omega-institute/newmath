import BEDC.Derived.ModulusContinuityUp.TasteGate

namespace BEDC.Derived.ModulusContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ModulusContinuityUniformCauchyHandoff [AskSetup] [PackageSetup]
    {graph sourceWindow modulus dyadic readback realSeal cauchyLedger toleranceRead windowRead
      graphRead readbackRead realRead cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory graph ->
      UnaryHistory sourceWindow ->
        UnaryHistory modulus ->
          UnaryHistory dyadic ->
            UnaryHistory readback ->
              UnaryHistory realSeal ->
                UnaryHistory cauchyLedger ->
                  Cont dyadic modulus toleranceRead ->
                    Cont toleranceRead sourceWindow windowRead ->
                      Cont windowRead graph graphRead ->
                        Cont graphRead readback readbackRead ->
                          Cont readbackRead realSeal realRead ->
                            Cont realRead cauchyLedger cauchyRead ->
                              PkgSig bundle cauchyRead pkg ->
                                UnaryHistory toleranceRead ∧ UnaryHistory windowRead ∧
                                  UnaryHistory graphRead ∧ UnaryHistory readbackRead ∧
                                    UnaryHistory realRead ∧ UnaryHistory cauchyRead ∧
                                      Cont dyadic modulus toleranceRead ∧
                                        Cont toleranceRead sourceWindow windowRead ∧
                                          Cont windowRead graph graphRead ∧
                                            Cont graphRead readback readbackRead ∧
                                              Cont readbackRead realSeal realRead ∧
                                                Cont realRead cauchyLedger cauchyRead ∧
                                                  PkgSig bundle cauchyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro graphUnary sourceWindowUnary modulusUnary dyadicUnary readbackUnary realSealUnary
    cauchyLedgerUnary toleranceCont windowCont graphCont readbackCont realCont cauchyCont
    cauchyPkg
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed dyadicUnary modulusUnary toleranceCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed toleranceUnary sourceWindowUnary windowCont
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed windowUnary graphUnary graphCont
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed graphReadUnary readbackUnary readbackCont
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed readbackReadUnary realSealUnary realCont
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed realReadUnary cauchyLedgerUnary cauchyCont
  exact
    ⟨toleranceUnary, windowUnary, graphReadUnary, readbackReadUnary, realReadUnary,
      cauchyReadUnary, toleranceCont, windowCont, graphCont, readbackCont, realCont,
      cauchyCont, cauchyPkg⟩

end BEDC.Derived.ModulusContinuityUp
