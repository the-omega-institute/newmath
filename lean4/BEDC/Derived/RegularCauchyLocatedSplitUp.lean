import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive RegularCauchyLocatedSplitUp : Type where
  | mk :
      (source located budget window readback realSeal transport replay provenance localName : BHist) →
      RegularCauchyLocatedSplitUp
  deriving DecidableEq

end BEDC.Derived

namespace BEDC.Derived.RegularCauchyLocatedSplitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyLocatedSplit_real_handoff [AskSetup] [PackageSetup]
    {Q L D W R E H C P N sourceLocated splitRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q →
      UnaryHistory L →
        UnaryHistory D →
          UnaryHistory W →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont Q L sourceLocated →
                          Cont sourceLocated D splitRead →
                            Cont splitRead R sealRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle sealRead pkg →
                                  UnaryHistory sourceLocated ∧ UnaryHistory splitRead ∧
                                    UnaryHistory sealRead ∧ Cont Q L sourceLocated ∧
                                      Cont sourceLocated D splitRead ∧
                                        Cont splitRead R sealRead ∧
                                          PkgSig bundle P pkg ∧
                                            PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro qUnary lUnary dUnary _wUnary rUnary _eUnary _hUnary _cUnary _pUnary _nUnary
  intro sourceRoute splitRoute sealRoute provenancePkg sealPkg
  have sourceLocatedUnary : UnaryHistory sourceLocated :=
    unary_cont_closed qUnary lUnary sourceRoute
  have splitReadUnary : UnaryHistory splitRead :=
    unary_cont_closed sourceLocatedUnary dUnary splitRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed splitReadUnary rUnary sealRoute
  exact
    ⟨sourceLocatedUnary, splitReadUnary, sealReadUnary, sourceRoute, splitRoute, sealRoute,
      provenancePkg, sealPkg⟩

end BEDC.Derived.RegularCauchyLocatedSplitUp
