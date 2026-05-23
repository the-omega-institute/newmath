import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyTailCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailCertificateSelectorCoverage [AskSetup] [PackageSetup]
    {source window readback dyadic sealRow support localName windowRead readbackRead sealRead :
      BHist} :
    UnaryHistory source ->
      UnaryHistory window ->
        UnaryHistory readback ->
          UnaryHistory dyadic ->
            UnaryHistory support ->
              Cont source window windowRead ->
                Cont window readback readbackRead ->
                  Cont readback dyadic sealRead ->
                    UnaryHistory windowRead /\ UnaryHistory readbackRead /\
                      UnaryHistory sealRead /\ Cont source window windowRead /\
                        Cont window readback readbackRead /\ Cont readback dyadic sealRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont
  intro sourceUnary windowUnary readbackUnary dyadicUnary _supportUnary sourceWindow
    windowReadback readbackDyadic
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary readbackUnary windowReadback
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary dyadicUnary readbackDyadic
  exact
    ⟨windowReadUnary, readbackReadUnary, sealReadUnary, sourceWindow, windowReadback,
      readbackDyadic⟩

end BEDC.Derived.RegularCauchyTailCertificateUp
