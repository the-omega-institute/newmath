import BEDC.Derived.LocatedCauchyFilterUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedCauchyFilterBasisRefinementRoute [AskSetup] [PackageSetup]
    {F B R S Q D T E H C P N basisRead dyadicRead regularRead streamRead readbackRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory B →
        UnaryHistory R →
          UnaryHistory S →
            UnaryHistory Q →
              UnaryHistory D →
                UnaryHistory T →
                  UnaryHistory E →
                    UnaryHistory P →
                      Cont F B basisRead →
                        Cont basisRead D dyadicRead →
                          Cont dyadicRead R regularRead →
                            Cont regularRead S streamRead →
                              Cont streamRead Q readbackRead →
                                Cont readbackRead E realRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle realRead pkg →
                                      UnaryHistory basisRead ∧ UnaryHistory dyadicRead ∧
                                        UnaryHistory regularRead ∧ UnaryHistory streamRead ∧
                                          UnaryHistory readbackRead ∧
                                            UnaryHistory realRead ∧
                                              Cont F B basisRead ∧
                                                Cont basisRead D dyadicRead ∧
                                                  Cont dyadicRead R regularRead ∧
                                                    Cont regularRead S streamRead ∧
                                                      Cont streamRead Q readbackRead ∧
                                                        Cont readbackRead E realRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro fUnary bUnary rUnary sUnary qUnary dUnary _tUnary eUnary _pUnary basisCont
    dyadicCont regularCont streamCont readbackCont realCont provenancePkg realPkg
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed fUnary bUnary basisCont
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed basisUnary dUnary dyadicCont
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed dyadicUnary rUnary regularCont
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed regularUnary sUnary streamCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed streamUnary qUnary readbackCont
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed readbackUnary eUnary realCont
  exact
    ⟨basisUnary, dyadicUnary, regularUnary, streamUnary, readbackUnary, realUnary,
      basisCont, dyadicCont, regularCont, streamCont, readbackCont, realCont,
      provenancePkg, realPkg⟩

end BEDC.Derived.LocatedCauchyFilterUp
