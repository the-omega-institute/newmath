import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationSeparatedReflectionRoute [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead separatedRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg ->
      Cont C T coverWindow ->
        Cont J P restrictionRead ->
          Cont coverWindow restrictionRead separatedRead ->
            Cont separatedRead S sheafRead ->
              PkgSig bundle sheafRead pkg ->
                UnaryHistory P ∧ UnaryHistory L ∧ UnaryHistory S ∧
                  UnaryHistory separatedRead ∧ UnaryHistory sheafRead ∧
                    Cont C T coverWindow ∧ Cont J P restrictionRead ∧
                      Cont coverWindow restrictionRead separatedRead ∧
                        Cont separatedRead S sheafRead ∧ PkgSig bundle N pkg ∧
                          PkgSig bundle sheafRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier coverRoute restrictionRoute separatedRoute sheafRoute sheafPkg
  obtain ⟨CUnary, TUnary, JUnary, PUnary, LUnary, _GUnary, SUnary, _HUnary, _RUnary,
    _QUnary, _NUnary, _provenancePkg, namePkg⟩ := carrier
  have coverUnary : UnaryHistory coverWindow :=
    unary_cont_closed CUnary TUnary coverRoute
  have restrictionUnary : UnaryHistory restrictionRead :=
    unary_cont_closed JUnary PUnary restrictionRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed coverUnary restrictionUnary separatedRoute
  have sheafUnary : UnaryHistory sheafRead :=
    unary_cont_closed separatedUnary SUnary sheafRoute
  exact
    ⟨PUnary, LUnary, SUnary, separatedUnary, sheafUnary, coverRoute, restrictionRoute,
      separatedRoute, sheafRoute, namePkg, sheafPkg⟩

end BEDC.Derived.SheafificationUp
