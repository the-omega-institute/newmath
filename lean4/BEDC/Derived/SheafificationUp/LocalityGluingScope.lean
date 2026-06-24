import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationLocalityGluingScope [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead localityRead gluedRead
      sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverWindow →
        Cont J P restrictionRead →
          Cont coverWindow restrictionRead localityRead →
            Cont localityRead G gluedRead →
              Cont gluedRead S sheafRead →
                PkgSig bundle sheafRead pkg →
                  UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory J ∧ UnaryHistory P ∧
                    UnaryHistory localityRead ∧ UnaryHistory gluedRead ∧
                      UnaryHistory sheafRead ∧ Cont C T coverWindow ∧
                        Cont J P restrictionRead ∧
                          Cont coverWindow restrictionRead localityRead ∧
                            Cont localityRead G gluedRead ∧ Cont gluedRead S sheafRead ∧
                              PkgSig bundle N pkg ∧ PkgSig bundle sheafRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier coverRoute restrictionRoute localityRoute gluingRoute sheafRoute sheafPkg
  obtain
    ⟨CUnary, TUnary, JUnary, PUnary, _LUnary, GUnary, SUnary, _HUnary, _RUnary,
      _QUnary, _NUnary, namePkg⟩ := carrier
  have coverUnary : UnaryHistory coverWindow :=
    unary_cont_closed CUnary TUnary coverRoute
  have restrictionUnary : UnaryHistory restrictionRead :=
    unary_cont_closed JUnary PUnary restrictionRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed coverUnary restrictionUnary localityRoute
  have gluedUnary : UnaryHistory gluedRead :=
    unary_cont_closed localityUnary GUnary gluingRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed gluedUnary SUnary sheafRoute
  exact
    ⟨CUnary, TUnary, JUnary, PUnary, localityUnary, gluedUnary, sheafUnary, coverRoute,
      restrictionRoute, localityRoute, gluingRoute, sheafRoute, namePkg, sheafPkg⟩

end BEDC.Derived.SheafificationUp
