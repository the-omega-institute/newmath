import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalCofinalTailCarrier [AskSetup] [PackageSetup]
    (q s g d r w h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
    UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory n ∧ Cont q s g ∧ Cont g d r ∧
        Cont w h c ∧ PkgSig bundle p pkg

theorem DiagonalCofinalTailCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {q s g d r w h c p n consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont w r consumer →
      PkgSig bundle consumer pkg →
        UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
          UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory h ∧ UnaryHistory c ∧
            UnaryHistory p ∧ UnaryHistory n ∧ UnaryHistory consumer ∧
              Cont q s g ∧ Cont g d r ∧ Cont w h c ∧ Cont w r consumer ∧
                PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row p ∧ UnaryHistory row)
                    (fun row : BHist => hsame row p)
                    (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier consumerRoute consumerPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary,
    pUnary, nUnary, qsRoute, gdRoute, whRoute, pPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed wUnary rUnary consumerRoute
  have sourceP : (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact And.intro (hsame_refl p) pUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro p sourceP
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pPkg
    }
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary, pUnary,
      nUnary, consumerUnary, qsRoute, gdRoute, whRoute, consumerRoute, pPkg,
      consumerPkg, cert⟩

theorem DiagonalCofinalTailCarrier_seed_window_readback [AskSetup] [PackageSetup]
    {q s g d r w h c p n windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont c r windowRead →
        PkgSig bundle windowRead pkg →
          UnaryHistory w ∧ UnaryHistory h ∧ UnaryHistory c ∧ UnaryHistory r ∧
            UnaryHistory windowRead ∧ Cont w h c ∧ Cont c r windowRead ∧
              PkgSig bundle p pkg ∧ PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier windowRoute windowPkg
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, rUnary, wUnary, hUnary, cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, whRoute, pPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed cUnary rUnary windowRoute
  exact ⟨wUnary, hUnary, cUnary, rUnary, windowUnary, whRoute, windowRoute, pPkg, windowPkg⟩

theorem DiagonalCofinalTailCarrier_common_window_refinement [AskSetup] [PackageSetup]
    {q s g d r w h c p n leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont c r leftRead →
        Cont c r rightRead →
          PkgSig bundle leftRead pkg →
            PkgSig bundle rightRead pkg →
              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧ Cont c r leftRead ∧
                Cont c r rightRead ∧ PkgSig bundle p pkg ∧ PkgSig bundle leftRead pkg ∧
                  PkgSig bundle rightRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig
  intro carrier leftRoute rightRoute leftPkg rightPkg
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, rUnary, _wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed cUnary rUnary leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed cUnary rUnary rightRoute
  exact ⟨leftUnary, rightUnary, leftRoute, rightRoute, pPkg, leftPkg, rightPkg⟩

theorem DiagonalCofinalTailCarrier_route_composition [AskSetup] [PackageSetup]
    {q s g d r w h c p n sealRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont r w sealRead →
        Cont sealRead c finalRead →
          PkgSig bundle finalRead pkg →
            UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
              UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory sealRead ∧
                UnaryHistory finalRead ∧ Cont q s g ∧ Cont g d r ∧
                  Cont r w sealRead ∧ Cont sealRead c finalRead ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier rwSeal sealFinal finalPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, _hUnary, cUnary,
    _pUnary, _nUnary, qsRoute, gdRoute, _whRoute, pPkg⟩ := carrier
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary wUnary rwSeal
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed sealUnary cUnary sealFinal
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, sealUnary, finalUnary, qsRoute,
      gdRoute, rwSeal, sealFinal, pPkg, finalPkg⟩

theorem DiagonalCofinalTailCarrier_hsame_transport_lock [AskSetup] [PackageSetup]
    {q s g d r w h c p n h' c' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      hsame h h' ->
        Cont w h' c' ->
          UnaryHistory h' ∧ UnaryHistory c' ∧ Cont w h' c' ∧ PkgSig bundle p pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig UnaryHistory
  intro carrier sameH transportedSeal
  obtain ⟨_qUnary, _sUnary, _gUnary, _dUnary, _rUnary, wUnary, hUnary, _cUnary,
    _pUnary, _nUnary, _qsRoute, _gdRoute, _whRoute, pPkg⟩ := carrier
  have transportedHUnary : UnaryHistory h' :=
    unary_transport hUnary sameH
  have transportedCUnary : UnaryHistory c' :=
    unary_cont_closed wUnary transportedHUnary transportedSeal
  exact ⟨transportedHUnary, transportedCUnary, transportedSeal, pPkg⟩

theorem DiagonalCofinalTailCarrier_tail_selector_lock [AskSetup] [PackageSetup]
    {q s g d r w h c p n streamRead tailRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg ->
      Cont s g streamRead ->
        Cont streamRead r tailRead ->
          Cont tailRead c consumer ->
            PkgSig bundle consumer pkg ->
              UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
                UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory h ∧ UnaryHistory c ∧
                  UnaryHistory p ∧ UnaryHistory n ∧ UnaryHistory streamRead ∧
                    UnaryHistory tailRead ∧ UnaryHistory consumer ∧ Cont q s g ∧
                      Cont g d r ∧ Cont w h c ∧ Cont s g streamRead ∧
                        Cont streamRead r tailRead ∧ Cont tailRead c consumer ∧
                          PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier streamRoute tailRoute consumerRoute consumerPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary, pUnary,
    nUnary, qsRoute, gdRoute, whRoute, pPkg⟩ := carrier
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed sUnary gUnary streamRoute
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed streamUnary rUnary tailRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed tailUnary cUnary consumerRoute
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary, pUnary, nUnary,
      streamUnary, tailUnary, consumerUnary, qsRoute, gdRoute, whRoute, streamRoute,
      tailRoute, consumerRoute, pPkg, consumerPkg⟩

theorem DiagonalCofinalTailCarrier_real_seal_handoff [AskSetup] [PackageSetup]
    {q s g d r w h c p n realConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont r w realConsumer →
        PkgSig bundle realConsumer pkg →
          UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
            UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory realConsumer ∧
              Cont q s g ∧ Cont g d r ∧ Cont r w realConsumer ∧
                PkgSig bundle p pkg ∧ PkgSig bundle realConsumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier realSealRoute realConsumerPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, qsRoute, gdRoute, _whRoute, pPkg⟩ := carrier
  have realConsumerUnary : UnaryHistory realConsumer :=
    unary_cont_closed rUnary wUnary realSealRoute
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, realConsumerUnary, qsRoute,
      gdRoute, realSealRoute, pPkg, realConsumerPkg⟩

end BEDC.Derived.DiagonalCofinalTailUp
