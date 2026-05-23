import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DarbouxIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DarbouxIntegralPacket [AskSetup] [PackageSetup]
    (partition upper lower upperSum lowerSum gap realHandoff transports routes name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory partition ∧ UnaryHistory upper ∧ UnaryHistory lower ∧
    UnaryHistory upperSum ∧ UnaryHistory lowerSum ∧ UnaryHistory gap ∧
      UnaryHistory realHandoff ∧ UnaryHistory transports ∧ UnaryHistory routes ∧
        UnaryHistory name ∧ Cont upper lower upperSum ∧ Cont upperSum lowerSum gap ∧
          PkgSig bundle name pkg

theorem DarbouxIntegralPacket_namecert_obligations [AskSetup] [PackageSetup]
    {partition upper lower upperSum lowerSum gap realHandoff transports routes name consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DarbouxIntegralPacket partition upper lower upperSum lowerSum gap realHandoff transports routes
        name bundle pkg →
      Cont gap realHandoff consumer →
        PkgSig bundle consumer pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row name ∧
                  DarbouxIntegralPacket partition upper lower upperSum lowerSum gap realHandoff
                    transports routes name bundle pkg)
              (fun row : BHist => hsame row name)
              (fun row : BHist => hsame row name ∧ PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory partition ∧ UnaryHistory upper ∧ UnaryHistory lower ∧
              UnaryHistory upperSum ∧ UnaryHistory lowerSum ∧ UnaryHistory gap ∧
                UnaryHistory realHandoff ∧ UnaryHistory consumer ∧ Cont upper lower upperSum ∧
                  Cont upperSum lowerSum gap ∧ Cont gap realHandoff consumer ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro hpacket gapRealConsumer consumerPkg
  obtain ⟨partitionUnary, upperUnary, lowerUnary, upperSumUnary, lowerSumUnary, gapUnary,
    realHandoffUnary, _transportsUnary, _routesUnary, _nameUnary, upperLowerUpperSum,
    upperLowerSumGap, namePkg⟩ := hpacket
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed gapUnary realHandoffUnary gapRealConsumer
  have core :
      NameCert
        (fun row : BHist =>
          hsame row name ∧
            DarbouxIntegralPacket partition upper lower upperSum lowerSum gap realHandoff
              transports routes name bundle pkg)
        hsame := by
    constructor
    · exact
        ⟨name, hsame_refl name, partitionUnary, upperUnary, lowerUnary, upperSumUnary,
          lowerSumUnary, gapUnary, realHandoffUnary, _transportsUnary, _routesUnary,
          _nameUnary, upperLowerUpperSum, upperLowerSumGap, namePkg⟩
    · intro row _source
      exact hsame_refl row
    · intro row other same
      exact hsame_symm same
    · intro row mid other sameRowMid sameMidOther
      exact hsame_trans sameRowMid sameMidOther
    · intro row other same source
      exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
  have semantic :
      SemanticNameCert
        (fun row : BHist =>
          hsame row name ∧
            DarbouxIntegralPacket partition upper lower upperSum lowerSum gap realHandoff
              transports routes name bundle pkg)
        (fun row : BHist => hsame row name)
        (fun row : BHist => hsame row name ∧ PkgSig bundle consumer pkg)
        hsame := by
    constructor
    · exact core
    · intro row source
      exact source.left
    · intro row source
      exact ⟨source.left, consumerPkg⟩
  exact
    ⟨semantic, partitionUnary, upperUnary, lowerUnary, upperSumUnary, lowerSumUnary, gapUnary,
      realHandoffUnary, consumerUnary, upperLowerUpperSum, upperLowerSumGap, gapRealConsumer,
      namePkg, consumerPkg⟩

theorem DarbouxIntegralPacket_upper_lower_sum_gap [AskSetup] [PackageSetup]
    {partition upper lower upperSum lowerSum gap realHandoff transports routes name refinedUpper
      refinedLower refinedUpperSum refinedLowerSum refinedGap : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DarbouxIntegralPacket partition upper lower upperSum lowerSum gap realHandoff transports
        routes name bundle pkg →
      Cont upper refinedUpper refinedUpperSum →
        Cont lower refinedLower refinedLowerSum →
          Cont refinedUpperSum refinedLowerSum refinedGap →
            hsame gap refinedGap →
              UnaryHistory refinedUpperSum ∧ UnaryHistory refinedLowerSum ∧
                UnaryHistory refinedGap ∧ Cont refinedUpperSum refinedLowerSum refinedGap ∧
                  hsame gap refinedGap := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet _upperRefinement _lowerRefinement refinedGapRoute sameGap
  obtain ⟨_partitionUnary, _upperUnary, _lowerUnary, _upperSumUnary, _lowerSumUnary, gapUnary,
    _realHandoffUnary, _transportsUnary, _routesUnary, _nameUnary, _upperLowerUpperSum,
    _upperLowerSumGap, _namePkg⟩ := packet
  have refinedGapUnary : UnaryHistory refinedGap :=
    unary_transport gapUnary sameGap
  have refinedUpperSumUnary : UnaryHistory refinedUpperSum :=
    unary_cont_left_factor refinedGapRoute refinedGapUnary
  have refinedLowerSumUnary : UnaryHistory refinedLowerSum :=
    unary_cont_right_factor refinedGapRoute refinedGapUnary
  exact
    ⟨refinedUpperSumUnary, refinedLowerSumUnary, refinedGapUnary, refinedGapRoute, sameGap⟩

theorem DarbouxIntegralPacket_integral_consumer_surface [AskSetup] [PackageSetup]
    {partition upper lower upperSum lowerSum gap realHandoff transports routes name
      integralConsumer integralSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DarbouxIntegralPacket partition upper lower upperSum lowerSum gap realHandoff transports routes
        name bundle pkg ->
      Cont gap realHandoff integralConsumer ->
        Cont integralConsumer name integralSurface ->
          PkgSig bundle integralConsumer pkg ->
            PkgSig bundle integralSurface pkg ->
              UnaryHistory integralConsumer ∧ UnaryHistory integralSurface ∧
                Cont upper lower upperSum ∧ Cont upperSum lowerSum gap ∧
                  Cont gap realHandoff integralConsumer ∧
                    Cont integralConsumer name integralSurface ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle integralConsumer pkg ∧
                        PkgSig bundle integralSurface pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro packet gapRealConsumer consumerNameSurface consumerPkg surfacePkg
  obtain ⟨_partitionUnary, _upperUnary, _lowerUnary, _upperSumUnary, _lowerSumUnary,
    gapUnary, realHandoffUnary, _transportsUnary, _routesUnary, nameUnary,
    upperLowerUpperSum, upperLowerSumGap, namePkg⟩ := packet
  have consumerUnary : UnaryHistory integralConsumer :=
    unary_cont_closed gapUnary realHandoffUnary gapRealConsumer
  have surfaceUnary : UnaryHistory integralSurface :=
    unary_cont_closed consumerUnary nameUnary consumerNameSurface
  exact
    ⟨consumerUnary, surfaceUnary, upperLowerUpperSum, upperLowerSumGap, gapRealConsumer,
      consumerNameSurface, namePkg, consumerPkg, surfacePkg⟩

end BEDC.Derived.DarbouxIntegralUp
