import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.MooreSmithConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MooreSmithConvergencePacket [AskSetup] [PackageSetup]
    (D V U C B R L H K P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
    UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory H ∧
      UnaryHistory K ∧ UnaryHistory N ∧ Cont D V U ∧ Cont U C B ∧
        Cont B R L ∧ PkgSig bundle P pkg

theorem MooreSmithConvergencePacket_namecert_obligations [AskSetup] [PackageSetup]
    {D V U C B R L H K P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg ->
      UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
        UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory L ∧ Cont D V U ∧
          Cont U C B ∧ Cont B R L ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet
  obtain ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, _hUnary,
    _kUnary, _nUnary, dvu, ucb, brl, pPkg⟩ := packet
  exact
    ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, dvu, ucb, brl,
      pPkg⟩

theorem MooreSmithConvergencePacket_uniform_handoff [AskSetup] [PackageSetup]
    {D V U C B R L H K P N boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg →
      Cont B R boundaryRead →
        UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
          UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory boundaryRead ∧ Cont D V U ∧
            Cont U C B ∧ Cont B R boundaryRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet boundaryRoute
  obtain ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, _lUnary, _hUnary,
    _kUnary, _nUnary, dvu, ucb, _brl, pPkg⟩ := packet
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary rUnary boundaryRoute
  exact
    ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, boundaryUnary, dvu, ucb,
      boundaryRoute, pPkg⟩

theorem MooreSmithConvergencePacket_completion_boundary [AskSetup] [PackageSetup]
    {D V U C B R L H K P N boundaryRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg ->
      Cont B R boundaryRead ->
        Cont boundaryRead L realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
              UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory L ∧
                UnaryHistory boundaryRead ∧ UnaryHistory realRead ∧ Cont D V U ∧
                  Cont U C B ∧ Cont B R boundaryRead ∧
                    Cont boundaryRead L realRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet boundaryRoute realRoute realPkg
  obtain ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, _hUnary,
    _kUnary, _nUnary, dvu, ucb, _brl, pPkg⟩ := packet
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary rUnary boundaryRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed boundaryUnary lUnary realRoute
  exact
    ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, boundaryUnary,
      realUnary, dvu, ucb, boundaryRoute, realRoute, pPkg, realPkg⟩

theorem MooreSmithConvergencePacket_boundary_scope [AskSetup] [PackageSetup]
    {D V U C B R L H K P N boundaryRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg ->
      Cont B R boundaryRead ->
        Cont boundaryRead L completionRead ->
          UnaryHistory D ∧ UnaryHistory V ∧ UnaryHistory U ∧ UnaryHistory C ∧
            UnaryHistory B ∧ UnaryHistory R ∧ UnaryHistory L ∧
              UnaryHistory boundaryRead ∧ UnaryHistory completionRead ∧ Cont D V U ∧
                Cont U C B ∧ Cont B R boundaryRead ∧
                  Cont boundaryRead L completionRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet boundaryRoute completionRoute
  obtain ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, _hUnary,
    _kUnary, _nUnary, dvu, ucb, _brl, pPkg⟩ := packet
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary rUnary boundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed boundaryUnary lUnary completionRoute
  exact
    ⟨dUnary, vUnary, uUnary, cUnary, bUnary, rUnary, lUnary, boundaryUnary,
      completionUnary, dvu, ucb, boundaryRoute, completionRoute, pPkg⟩

end BEDC.Derived.MooreSmithConvergenceUp
