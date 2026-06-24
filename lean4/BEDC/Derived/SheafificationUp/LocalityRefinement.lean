import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationLocalityRefinement [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead localityRead refinedLocality :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg ->
      Cont C T coverWindow ->
        Cont J P restrictionRead ->
          Cont coverWindow restrictionRead localityRead ->
            hsame refinedLocality localityRead ->
              PkgSig bundle refinedLocality pkg ->
                UnaryHistory coverWindow ∧ UnaryHistory restrictionRead ∧
                  UnaryHistory localityRead ∧ UnaryHistory refinedLocality ∧
                    hsame refinedLocality localityRead ∧ Cont C T coverWindow ∧
                      Cont J P restrictionRead ∧
                        Cont coverWindow restrictionRead localityRead ∧
                          PkgSig bundle N pkg ∧ PkgSig bundle refinedLocality pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier coverRoute restrictionRoute localityRoute sameRefinedLocality refinedPkg
  obtain ⟨CUnary, TUnary, JUnary, PUnary, _LUnary, _GUnary, _SUnary, _HUnary, _RUnary,
    _QUnary, _NUnary, namePkg⟩ := carrier
  have coverWindowUnary : UnaryHistory coverWindow :=
    unary_cont_closed CUnary TUnary coverRoute
  have restrictionReadUnary : UnaryHistory restrictionRead :=
    unary_cont_closed JUnary PUnary restrictionRoute
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed coverWindowUnary restrictionReadUnary localityRoute
  have refinedLocalityUnary : UnaryHistory refinedLocality :=
    unary_transport_symm localityReadUnary sameRefinedLocality
  exact
    ⟨coverWindowUnary, restrictionReadUnary, localityReadUnary, refinedLocalityUnary,
      sameRefinedLocality, coverRoute, restrictionRoute, localityRoute, namePkg, refinedPkg⟩

end BEDC.Derived.SheafificationUp
