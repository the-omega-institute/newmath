import BEDC.Derived.RegularCauchyAbsUp.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyAbsCarrier_obligation_closure [AskSetup] [PackageSetup]
    {X W D V R E H C P N windowRead endpointRead absRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory W ->
        UnaryHistory D ->
          UnaryHistory V ->
            UnaryHistory R ->
              UnaryHistory E ->
                Cont X W windowRead ->
                  Cont windowRead D endpointRead ->
                    Cont endpointRead V absRead ->
                      Cont absRead R realRead ->
                        Cont R E realRead ->
                          PkgSig bundle R pkg ->
                            PkgSig bundle realRead pkg ->
                              SemanticNameCert
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row W ∨ hsame row D ∨
                                    hsame row V ∨ hsame row R ∨ hsame row E ∨
                                      hsame row H ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row W ∨ hsame row D ∨
                                    hsame row V ∨ hsame row R ∨ hsame row E ∨
                                      hsame row H ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N)
                                (fun row : BHist =>
                                  hsame row X ∨ hsame row W ∨ hsame row D ∨
                                    hsame row V ∨ hsame row R ∨ hsame row E ∨
                                      hsame row H ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N)
                                hsame ∧
                                UnaryHistory windowRead ∧ UnaryHistory endpointRead ∧
                                  UnaryHistory absRead ∧ UnaryHistory realRead ∧
                                    Cont X W windowRead ∧
                                      Cont windowRead D endpointRead ∧
                                        Cont endpointRead V absRead ∧
                                          Cont absRead R realRead ∧ Cont R E realRead ∧
                                            PkgSig bundle R pkg ∧
                                              PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro unaryX unaryW unaryD unaryV unaryR _unaryE xWindow windowEndpoint endpointAbs
    absReal realSeal rPkg realPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryX unaryW xWindow
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed windowUnary unaryD windowEndpoint
  have absUnary : UnaryHistory absRead :=
    unary_cont_closed endpointUnary unaryV endpointAbs
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed absUnary unaryR absReal
  have obligationCert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        (fun row : BHist =>
          hsame row X ∨ hsame row W ∨ hsame row D ∨ hsame row V ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
        hsame :=
    RegularCauchyAbsCarrier_namecert_obligations X W D V R E H C P N
  exact
    ⟨obligationCert, windowUnary, endpointUnary, absUnary, realUnary, xWindow,
      windowEndpoint, endpointAbs, absReal, realSeal, rPkg, realPkg⟩

end BEDC.Derived.RegularCauchyAbsUp
