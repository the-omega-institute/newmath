import BEDC.Derived.ScientificIdealizationResidueSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ScientificIdealizationResidueSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ScientificIdealizationResidueSeal_scope_refinement [AskSetup] [PackageSetup]
    {E M O B A I R D F Sigma T C P N explanationRead residueRead descentRead failureRead
      scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont E I explanationRead →
      Cont I R residueRead →
        Cont R D descentRead →
          Cont D F failureRead →
            Cont failureRead Sigma scopeRead →
              PkgSig bundle P pkg →
                UnaryHistory E →
                  UnaryHistory I →
                    UnaryHistory R →
                      UnaryHistory D →
                        UnaryHistory F →
                          UnaryHistory Sigma →
                            scientificIdealizationResidueSealFields
                                (ScientificIdealizationResidueSealUp.mk E M O B A I R D F
                                  Sigma T C P N) =
                              [E, M, O, B, A, I, R, D, F, Sigma, T, C, P, N] ∧
                              UnaryHistory explanationRead ∧
                                UnaryHistory residueRead ∧
                                  UnaryHistory descentRead ∧
                                    UnaryHistory failureRead ∧
                                      UnaryHistory scopeRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro explanationCont residueCont descentCont failureCont scopeCont provenancePkg
    explanationUnary idealizationUnary residueUnary descentUnary failureUnary scopeUnary
  have explanationReadUnary : UnaryHistory explanationRead :=
    unary_cont_closed explanationUnary idealizationUnary explanationCont
  have residueReadUnary : UnaryHistory residueRead :=
    unary_cont_closed idealizationUnary residueUnary residueCont
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed residueUnary descentUnary descentCont
  have failureReadUnary : UnaryHistory failureRead :=
    unary_cont_closed descentUnary failureUnary failureCont
  have scopeReadUnary : UnaryHistory scopeRead :=
    unary_cont_closed failureReadUnary scopeUnary scopeCont
  exact
    ⟨rfl, explanationReadUnary, residueReadUnary, descentReadUnary, failureReadUnary,
      scopeReadUnary, provenancePkg⟩

end BEDC.Derived.ScientificIdealizationResidueSealUp
