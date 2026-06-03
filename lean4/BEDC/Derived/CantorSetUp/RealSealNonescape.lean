import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {T G I D R E prefixRead endpointRead regularRead sealedRead : BHist}
    (prefixRoute : Cont T G prefixRead) (endpointRoute : Cont prefixRead D endpointRead)
    (regularRoute : Cont endpointRead R regularRead) (sealRoute : Cont regularRead E sealedRead)
    (unaryT : UnaryHistory T) (unaryG : UnaryHistory G) (unaryD : UnaryHistory D)
    (unaryR : UnaryHistory R) (unaryE : UnaryHistory E) :
    UnaryHistory prefixRead ∧ UnaryHistory endpointRead ∧ UnaryHistory regularRead ∧
      UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryT unaryG prefixRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed prefixUnary unaryD endpointRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointUnary unaryR regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary unaryE sealRoute
  exact And.intro prefixUnary (And.intro endpointUnary (And.intro regularUnary sealedUnary))

end BEDC.Derived.CantorSetUp
