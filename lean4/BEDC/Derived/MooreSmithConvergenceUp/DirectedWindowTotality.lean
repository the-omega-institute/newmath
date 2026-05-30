import BEDC.Derived.MooreSmithConvergenceUp

namespace BEDC.Derived.MooreSmithConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MooreSmithConvergencePacket_directed_window_totality [AskSetup] [PackageSetup]
    {D V U C B R L H K P N directedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg ->
      Cont D V directedRead ->
        UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
          UnaryHistory B ∧ UnaryHistory directedRead ∧ Cont D V directedRead ∧
            Cont U C B ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet directedRoute
  obtain ⟨dUnary, vUnary, uUnary, cUnary, bUnary, _rUnary, _lUnary, _hUnary,
    _kUnary, _nUnary, _dvu, ucb, _brl, provenancePkg⟩ := packet
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed dUnary vUnary directedRoute
  exact
    ⟨dUnary, vUnary, uUnary, cUnary, bUnary, directedUnary, directedRoute, ucb,
      provenancePkg⟩

end BEDC.Derived.MooreSmithConvergenceUp
