import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.FiniteTailFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteTailFilterCarrier_refinement_seal_witness_ledger_pullback
    [AskSetup] [PackageSetup]
    {S D R B Q E H C P N sealRow refinementRead witnessRead limitSealRead
      terminalRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteTailFilterCarrier S D R B Q E H C P N ->
      Cont Q E sealRow ->
        Cont sealRow H refinementRead ->
          Cont refinementRead C witnessRead ->
            Cont witnessRead H limitSealRead ->
              Cont limitSealRead C terminalRead ->
                PkgSig bundle terminalRead pkg ->
                  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory B ∧
                    UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
                      UnaryHistory sealRow ∧ UnaryHistory refinementRead ∧
                        UnaryHistory witnessRead ∧ UnaryHistory limitSealRead ∧
                          UnaryHistory terminalRead ∧ Cont S D R ∧ Cont R B Q ∧
                            Cont Q E sealRow ∧ Cont sealRow H refinementRead ∧
                              Cont refinementRead C witnessRead ∧
                                Cont witnessRead H limitSealRead ∧
                                  Cont limitSealRead C terminalRead ∧ hsame N E ∧
                                    PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier sealRoute refinementRoute witnessRoute limitSealRoute terminalRoute terminalPkg
  obtain ⟨unaryS, unaryD, unaryB, unaryE, unaryH, unaryC, routeR, routeQ,
    sameNameSeal⟩ := carrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have unarySeal : UnaryHistory sealRow :=
    unary_cont_closed unaryQ unaryE sealRoute
  have unaryRefinement : UnaryHistory refinementRead :=
    unary_cont_closed unarySeal unaryH refinementRoute
  have unaryWitness : UnaryHistory witnessRead :=
    unary_cont_closed unaryRefinement unaryC witnessRoute
  have unaryLimitSeal : UnaryHistory limitSealRead :=
    unary_cont_closed unaryWitness unaryH limitSealRoute
  have unaryTerminal : UnaryHistory terminalRead :=
    unary_cont_closed unaryLimitSeal unaryC terminalRoute
  exact
    ⟨unaryS, unaryD, unaryR, unaryB, unaryQ, unaryE, unaryH, unaryC, unarySeal,
      unaryRefinement, unaryWitness, unaryLimitSeal, unaryTerminal, routeR, routeQ,
      sealRoute, refinementRoute, witnessRoute, limitSealRoute, terminalRoute,
      sameNameSeal, terminalPkg⟩

end BEDC.Derived.FiniteTailFilterUp
