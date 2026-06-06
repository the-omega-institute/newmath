import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History
import BEDC.Derived.RiemannLebesgueLemmaUp.TasteGate

namespace BEDC.Derived.RiemannLebesgueLemmaUp.OscillatoryHandoff

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannLebesgueLemmaOscillatoryHandoff [AskSetup] [PackageSetup]
    {F S I W T A _Q E _H _C P N coefficientRead _phaseRead integralRead toleranceRead
      decayRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory S →
        UnaryHistory I →
          UnaryHistory W →
          UnaryHistory T →
            UnaryHistory A →
              UnaryHistory E →
                Cont F S coefficientRead →
                  Cont coefficientRead I integralRead →
                    Cont W T toleranceRead →
                      Cont integralRead A decayRead →
                        Cont decayRead E sealRead →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              UnaryHistory coefficientRead ∧
                                UnaryHistory integralRead ∧
                                  UnaryHistory toleranceRead ∧
                                    UnaryHistory decayRead ∧
                                      UnaryHistory sealRead ∧
                                        Cont F S coefficientRead ∧
                                          Cont coefficientRead I integralRead ∧
                                            Cont integralRead A decayRead ∧
                                              Cont decayRead E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro unaryF unaryS unaryI unaryW unaryT unaryA unaryE coefficientRoute integralRoute
    toleranceRoute decayRoute sealRoute _provenancePkg _namePkg
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed unaryF unaryS coefficientRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed coefficientUnary unaryI integralRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryW unaryT toleranceRoute
  have decayUnary : UnaryHistory decayRead :=
    unary_cont_closed integralUnary unaryA decayRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed decayUnary unaryE sealRoute
  exact
    ⟨coefficientUnary, integralUnary, toleranceUnary, decayUnary, sealUnary,
      coefficientRoute, integralRoute, decayRoute, sealRoute⟩

end BEDC.Derived.RiemannLebesgueLemmaUp.OscillatoryHandoff
