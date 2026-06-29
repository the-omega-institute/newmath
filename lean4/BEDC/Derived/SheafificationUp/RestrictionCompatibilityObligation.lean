import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationRestrictionCompatibilityObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead restrictionRead localityRead gluingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T sourceRead →
        Cont sourceRead P restrictionRead →
          Cont restrictionRead L localityRead →
            Cont localityRead G gluingRead →
              PkgSig bundle gluingRead pkg →
                UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory P ∧
                  UnaryHistory L ∧ UnaryHistory G ∧ UnaryHistory sourceRead ∧
                    UnaryHistory restrictionRead ∧ UnaryHistory localityRead ∧
                      UnaryHistory gluingRead ∧ Cont C T sourceRead ∧
                        Cont sourceRead P restrictionRead ∧
                          Cont restrictionRead L localityRead ∧
                            Cont localityRead G gluingRead ∧
                              PkgSig bundle N pkg ∧ PkgSig bundle gluingRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier sourceRoute restrictionRoute localityRoute gluingRoute gluingPkg
  obtain ⟨cUnary, tUnary, _jUnary, pUnary, lUnary, gUnary, _sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, _qPkg, nPkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed cUnary tUnary sourceRoute
  have restrictionUnary : UnaryHistory restrictionRead :=
    unary_cont_closed sourceUnary pUnary restrictionRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed restrictionUnary lUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  exact
    ⟨cUnary, tUnary, pUnary, lUnary, gUnary, sourceUnary, restrictionUnary,
      localityUnary, gluingUnary, sourceRoute, restrictionRoute, localityRoute,
      gluingRoute, nPkg, gluingPkg⟩

end BEDC.Derived.SheafificationUp
