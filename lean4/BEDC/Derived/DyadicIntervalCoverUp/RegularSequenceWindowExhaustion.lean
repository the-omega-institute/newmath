import BEDC.Derived.DyadicIntervalCoverUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRegularSequenceWindowExhaustion [AskSetup] [PackageSetup]
    {W Q A windowRead sealRead : BHist} :
    UnaryHistory W →
      UnaryHistory Q →
        UnaryHistory A →
          Cont W Q windowRead →
            Cont windowRead A sealRead →
              UnaryHistory windowRead ∧ UnaryHistory sealRead ∧
                Cont W Q windowRead ∧ Cont windowRead A sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro wUnary qUnary aUnary windowRoute sealRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary aUnary sealRoute
  exact ⟨windowUnary, sealUnary, windowRoute, sealRoute⟩

end BEDC.Derived.DyadicIntervalCoverUp
