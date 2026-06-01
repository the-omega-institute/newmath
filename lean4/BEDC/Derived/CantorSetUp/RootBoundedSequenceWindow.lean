import BEDC.Derived.CantorSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CantorSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CantorSetCarrier_root_bounded_sequence_window [AskSetup] [PackageSetup]
    {T G I D R E H K P N prefixRead endpointRead regularRead sealedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T G prefixRead →
      Cont prefixRead D endpointRead →
        Cont endpointRead R regularRead →
          Cont regularRead E sealedRead →
            Cont sealedRead N namedRead →
              UnaryHistory T →
                UnaryHistory G →
                  UnaryHistory D →
                    UnaryHistory R →
                      UnaryHistory E →
                        UnaryHistory N →
                          PkgSig bundle P pkg →
                            PkgSig bundle N pkg →
                              UnaryHistory prefixRead ∧ UnaryHistory endpointRead ∧
                                UnaryHistory regularRead ∧ UnaryHistory sealedRead ∧
                                  UnaryHistory namedRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro prefixRoute endpointRoute regularRoute sealRoute namedRoute unaryT unaryG unaryD
    unaryR unaryE unaryN pkgP _pkgN
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryT unaryG prefixRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed prefixUnary unaryD endpointRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed endpointUnary unaryR regularRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed regularUnary unaryE sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealedUnary unaryN namedRoute
  exact ⟨prefixUnary, endpointUnary, regularUnary, sealedUnary, namedUnary, pkgP⟩

end BEDC.Derived.CantorSetUp
