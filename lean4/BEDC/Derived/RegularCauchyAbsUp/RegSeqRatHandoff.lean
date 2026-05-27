import BEDC.Derived.RegularCauchyAbsUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAbsCarrier_regseqrat_handoff [AskSetup] [PackageSetup]
    {X W D V R C windowRead endpointRead absRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory V →
            UnaryHistory R →
              Cont X W windowRead →
                Cont windowRead D endpointRead →
                  Cont endpointRead V absRead →
                    Cont absRead R C →
                      PkgSig bundle R pkg →
                        PkgSig bundle C pkg →
                          UnaryHistory windowRead ∧
                            UnaryHistory endpointRead ∧
                              UnaryHistory absRead ∧
                                UnaryHistory C ∧
                                  Cont X W windowRead ∧
                                    Cont windowRead D endpointRead ∧
                                      Cont endpointRead V absRead ∧
                                        Cont absRead R C ∧
                                          PkgSig bundle R pkg ∧
                                            PkgSig bundle C pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro unaryX unaryW unaryD unaryV unaryR xWindow windowEndpoint endpointAbs absResult
    rPkg cPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryX unaryW xWindow
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed windowUnary unaryD windowEndpoint
  have absUnary : UnaryHistory absRead :=
    unary_cont_closed endpointUnary unaryV endpointAbs
  have cUnary : UnaryHistory C :=
    unary_cont_closed absUnary unaryR absResult
  exact
    ⟨windowUnary, endpointUnary, absUnary, cUnary, xWindow, windowEndpoint,
      endpointAbs, absResult, rPkg, cPkg⟩

end BEDC.Derived.RegularCauchyAbsUp
