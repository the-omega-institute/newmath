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

theorem MooreSmithConvergencePacket_obligation_exhaustion [AskSetup] [PackageSetup]
    {D V U C B R L H K P N request boundaryRead realReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg →
      Cont D U request →
        Cont B R boundaryRead →
          Cont boundaryRead L realReadback →
            PkgSig bundle realReadback pkg →
              UnaryHistory D ∧ UnaryHistory U ∧ UnaryHistory request ∧ UnaryHistory B ∧
                UnaryHistory R ∧ UnaryHistory L ∧ UnaryHistory boundaryRead ∧
                  UnaryHistory realReadback ∧ Cont D U request ∧
                    Cont B R boundaryRead ∧ Cont boundaryRead L realReadback ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle realReadback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet requestRoute boundaryRoute readbackRoute readbackPkg
  obtain ⟨dUnary, _vUnary, uUnary, _cUnary, bUnary, rUnary, lUnary, _hUnary,
    _kUnary, _nUnary, _dvu, _ucb, _brl, pPkg⟩ := packet
  have requestUnary : UnaryHistory request :=
    unary_cont_closed dUnary uUnary requestRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary rUnary boundaryRoute
  have readbackUnary : UnaryHistory realReadback :=
    unary_cont_closed boundaryUnary lUnary readbackRoute
  exact
    ⟨dUnary, uUnary, requestUnary, bUnary, rUnary, lUnary, boundaryUnary,
      readbackUnary, requestRoute, boundaryRoute, readbackRoute, pPkg, readbackPkg⟩

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

theorem MooreSmithConvergencePacket_directed_window_stability [AskSetup] [PackageSetup]
    {D V U C B R L H K P N D' V' U' C' B' R' L' H' K' P' N'
      directedRead directedRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg ->
      MooreSmithConvergencePacket D' V' U' C' B' R' L' H' K' P' N' bundle pkg ->
        hsame D D' ->
          hsame V V' ->
            hsame U U' ->
              hsame C C' ->
                hsame B B' ->
                  Cont D V directedRead ->
                    Cont D' V' directedRead' ->
                      PkgSig bundle directedRead' pkg ->
                        hsame directedRead directedRead' ∧ UnaryHistory directedRead ∧
                          UnaryHistory directedRead' ∧ Cont D V directedRead ∧
                            Cont D' V' directedRead' ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle directedRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory PkgSig
  intro packet packet' sameD sameV _sameU _sameC _sameB directedRoute directedRoute'
    directedReadPkg
  obtain ⟨dUnary, vUnary, _uUnary, _cUnary, _bUnary, _rUnary, _lUnary, _hUnary,
    _kUnary, _nUnary, _dvu, _ucb, _brl, provenancePkg⟩ := packet
  obtain ⟨_dUnary', _vUnary', _uUnary', _cUnary', _bUnary', _rUnary', _lUnary',
    _hUnary', _kUnary', _nUnary', _dvu', _ucb', _brl', _provenancePkg'⟩ := packet'
  have directedSame : hsame directedRead directedRead' :=
    cont_respects_hsame sameD sameV directedRoute directedRoute'
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed dUnary vUnary directedRoute
  have directedUnary' : UnaryHistory directedRead' :=
    unary_transport directedUnary directedSame
  exact
    ⟨directedSame, directedUnary, directedUnary', directedRoute, directedRoute',
      provenancePkg, directedReadPkg⟩

theorem MooreSmithConvergencePacket_completion_readback_exactness [AskSetup] [PackageSetup]
    {D V U C B R L H K P N boundaryRead realReadback exportedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MooreSmithConvergencePacket D V U C B R L H K P N bundle pkg →
      Cont B R boundaryRead →
        Cont boundaryRead L realReadback →
          Cont realReadback H exportedRead →
            PkgSig bundle exportedRead pkg →
              UnaryHistory boundaryRead ∧ UnaryHistory realReadback ∧
                UnaryHistory exportedRead ∧ Cont B R boundaryRead ∧
                  Cont boundaryRead L realReadback ∧
                    Cont realReadback H exportedRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle exportedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet boundaryRoute readbackRoute exportedRoute exportedPkg
  obtain ⟨_dUnary, _vUnary, _uUnary, _cUnary, bUnary, rUnary, lUnary, hUnary,
    _kUnary, _nUnary, _dvu, _ucb, _brl, provenancePkg⟩ := packet
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary rUnary boundaryRoute
  have readbackUnary : UnaryHistory realReadback :=
    unary_cont_closed boundaryUnary lUnary readbackRoute
  have exportedUnary : UnaryHistory exportedRead :=
    unary_cont_closed readbackUnary hUnary exportedRoute
  exact
    ⟨boundaryUnary, readbackUnary, exportedUnary, boundaryRoute, readbackRoute,
      exportedRoute, provenancePkg, exportedPkg⟩

end BEDC.Derived.MooreSmithConvergenceUp
