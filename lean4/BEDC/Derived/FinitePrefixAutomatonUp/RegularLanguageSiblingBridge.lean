import BEDC.Derived.FinitePrefixAutomatonUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.FinitePrefixAutomatonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixAutomaton_regularlanguage_sibling_bridge [AskSetup] [PackageSetup]
    {Q q0 A T W R E H C P N regularRead continuationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont W E regularRead →
      Cont T C continuationRead →
        PkgSig bundle P pkg →
          UnaryHistory W →
            UnaryHistory E →
              UnaryHistory T →
                UnaryHistory C →
                  UnaryHistory regularRead ∧ UnaryHistory continuationRead ∧
                    List.Mem (finitePrefixAutomatonEncodeBHist W)
                      (finitePrefixAutomatonToEventFlow
                        (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                    List.Mem (finitePrefixAutomatonEncodeBHist T)
                      (finitePrefixAutomatonToEventFlow
                        (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) ∧
                    PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro regularRoute continuationRoute pkgSig wUnary eUnary tUnary cUnary
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed wUnary eUnary regularRoute
  have continuationUnary : UnaryHistory continuationRead :=
    unary_cont_closed tUnary cUnary continuationRoute
  have wordDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist W)
        (finitePrefixAutomatonToEventFlow
          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
    simp only [finitePrefixAutomatonToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  have transitionDisplayed :
      List.Mem (finitePrefixAutomatonEncodeBHist T)
        (finitePrefixAutomatonToEventFlow
          (FinitePrefixAutomatonUp.mk Q q0 A T W R E H C P N)) := by
    simp only [finitePrefixAutomatonToEventFlow]
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    apply List.Mem.tail
    exact List.Mem.head _
  constructor
  · exact regularUnary
  constructor
  · exact continuationUnary
  constructor
  · exact wordDisplayed
  constructor
  · exact transitionDisplayed
  · exact pkgSig

end BEDC.Derived.FinitePrefixAutomatonUp
