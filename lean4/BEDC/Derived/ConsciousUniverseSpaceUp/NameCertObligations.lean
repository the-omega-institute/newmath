import BEDC.Derived.ConsciousUniverseSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConsciousUniverseSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConsciousUniverseSpaceNameCertObligations [AskSetup] [PackageSetup]
    {L U _T S I _H _C _P _N universeRead localityRead identityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L U universeRead →
      Cont S I localityRead →
        Cont universeRead localityRead identityRead →
          PkgSig bundle identityRead pkg →
            UnaryHistory L →
              UnaryHistory U →
                UnaryHistory S →
                  UnaryHistory I →
                    UnaryHistory universeRead ∧ UnaryHistory localityRead ∧
                      UnaryHistory identityRead ∧ Cont L U universeRead ∧
                        Cont S I localityRead ∧ Cont universeRead localityRead identityRead ∧
                          PkgSig bundle identityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro universeRoute localityRoute identityRoute identityPkg LUnary UUnary SUnary IUnary
  have universeUnary : UnaryHistory universeRead :=
    unary_cont_closed LUnary UUnary universeRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed SUnary IUnary localityRoute
  have identityUnary : UnaryHistory identityRead :=
    unary_cont_closed universeUnary localityUnary identityRoute
  exact
    ⟨universeUnary, localityUnary, identityUnary, universeRoute, localityRoute, identityRoute,
      identityPkg⟩

end BEDC.Derived.ConsciousUniverseSpaceUp
