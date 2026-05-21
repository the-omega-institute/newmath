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

theorem ScientificIdealizationResidueSealNameCertObligations [AskSetup] [PackageSetup]
    {E M O B A I R D F Sigma T C P N explanationRead residueRead descentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont E I explanationRead ->
      Cont I R residueRead ->
        Cont R D descentRead ->
          PkgSig bundle P pkg ->
            UnaryHistory E ->
              UnaryHistory I ->
                UnaryHistory R ->
                  UnaryHistory D ->
                    UnaryHistory explanationRead ∧
                      UnaryHistory residueRead ∧
                        UnaryHistory descentRead ∧
                          Cont E I explanationRead ∧
                            Cont I R residueRead ∧
                              Cont R D descentRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro explanationCont residueCont descentCont provenancePkg explanationUnary idealizationUnary
    residueUnary descentUnary
  have explanationReadUnary : UnaryHistory explanationRead :=
    unary_cont_closed explanationUnary idealizationUnary explanationCont
  have residueReadUnary : UnaryHistory residueRead :=
    unary_cont_closed idealizationUnary residueUnary residueCont
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed residueUnary descentUnary descentCont
  exact
    ⟨explanationReadUnary, residueReadUnary, descentReadUnary, explanationCont, residueCont,
      descentCont, provenancePkg⟩

end BEDC.Derived.ScientificIdealizationResidueSealUp
