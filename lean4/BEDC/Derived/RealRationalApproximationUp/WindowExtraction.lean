import BEDC.Derived.RealRationalApproximationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealRationalApproximationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealRationalApproximationCarrier_window_extraction [AskSetup] [PackageSetup]
    {R Q D S G A _H _C _P _N windowRead readbackRead toleranceRead ledgerRead
      approximantRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory S →
        UnaryHistory G →
          UnaryHistory D →
            UnaryHistory A →
              UnaryHistory Q →
                Cont R S windowRead →
                  Cont windowRead G readbackRead →
                    Cont readbackRead D toleranceRead →
                      Cont toleranceRead A ledgerRead →
                        Cont ledgerRead Q approximantRead →
                          PkgSig bundle approximantRead pkg →
                            UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                              UnaryHistory toleranceRead ∧ UnaryHistory ledgerRead ∧
                                UnaryHistory approximantRead ∧ Cont R S windowRead ∧
                                  Cont windowRead G readbackRead ∧
                                    Cont readbackRead D toleranceRead ∧
                                      Cont toleranceRead A ledgerRead ∧
                                        Cont ledgerRead Q approximantRead ∧
                                          PkgSig bundle approximantRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro realUnary streamUnary readbackUnary toleranceUnary ledgerUnary approximantUnary
    windowCont readbackCont toleranceCont ledgerCont approximantCont approximantPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed realUnary streamUnary windowCont
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary readbackUnary readbackCont
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackReadUnary toleranceUnary toleranceCont
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed toleranceReadUnary ledgerUnary ledgerCont
  have approximantReadUnary : UnaryHistory approximantRead :=
    unary_cont_closed ledgerReadUnary approximantUnary approximantCont
  exact
    ⟨windowUnary, readbackReadUnary, toleranceReadUnary, ledgerReadUnary, approximantReadUnary,
      windowCont, readbackCont, toleranceCont, ledgerCont, approximantCont, approximantPkg⟩

end BEDC.Derived.RealRationalApproximationUp
