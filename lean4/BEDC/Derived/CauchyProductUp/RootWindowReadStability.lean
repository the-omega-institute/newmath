import BEDC.Derived.CauchyProductUp

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_window_read_stability [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name streamReadA streamReadB productReadA
      productReadB : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont transport routes streamReadA ->
        Cont transport routes streamReadB ->
          Cont streamReadA product productReadA ->
            Cont streamReadB product productReadB ->
              hsame productReadA productReadB ∧ UnaryHistory productReadA ∧
                UnaryHistory productReadB := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet transportRoutesStreamReadA transportRoutesStreamReadB streamProductReadA
    streamProductReadB
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, _ledgerUnary,
    windowTransport, productRoute, _classifierRoute, _namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed windowAUnary windowBUnary windowTransport
  have sameStreamRead : hsame streamReadA streamReadB :=
    cont_deterministic transportRoutesStreamReadA transportRoutesStreamReadB
  have sameProductRead : hsame productReadA productReadB :=
    cont_respects_hsame sameStreamRead (hsame_refl product) streamProductReadA
      streamProductReadB
  have streamReadAUnary : UnaryHistory streamReadA :=
    unary_cont_closed transportUnary routesUnary transportRoutesStreamReadA
  have streamReadBUnary : UnaryHistory streamReadB :=
    unary_cont_closed transportUnary routesUnary transportRoutesStreamReadB
  have productReadAUnary : UnaryHistory productReadA :=
    unary_cont_closed streamReadAUnary productUnary streamProductReadA
  have productReadBUnary : UnaryHistory productReadB :=
    unary_cont_closed streamReadBUnary productUnary streamProductReadB
  exact ⟨sameProductRead, productReadAUnary, productReadBUnary⟩

end BEDC.Derived.CauchyProductUp
