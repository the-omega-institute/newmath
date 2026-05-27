import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RiemannIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RiemannIntegralUp : Type where
  | mk (M T F S D G R H C P N : BHist) : RiemannIntegralUp
  deriving DecidableEq

def RiemannIntegralPacket [AskSetup] [PackageSetup]
    (mesh tags integrand sum darboux gap realHandoff transports routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory mesh ∧ UnaryHistory tags ∧ UnaryHistory integrand ∧ UnaryHistory sum ∧
    UnaryHistory darboux ∧ UnaryHistory gap ∧ UnaryHistory realHandoff ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont mesh tags integrand ∧ Cont integrand sum darboux ∧
          Cont darboux gap realHandoff ∧ PkgSig bundle name pkg

theorem RiemannIntegralPacket_namecert_obligations [AskSetup] [PackageSetup]
    {mesh tags integrand sum darboux gap realHandoff transports routes provenance name consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannIntegralPacket mesh tags integrand sum darboux gap realHandoff transports routes
        provenance name bundle pkg ->
      Cont gap realHandoff consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row name ∧
                  RiemannIntegralPacket mesh tags integrand sum darboux gap realHandoff
                    transports routes provenance name bundle pkg)
              (fun row : BHist => hsame row name)
              (fun row : BHist => hsame row name ∧ PkgSig bundle consumer pkg)
              hsame ∧
            UnaryHistory mesh ∧ UnaryHistory tags ∧ UnaryHistory integrand ∧
              UnaryHistory sum ∧ UnaryHistory darboux ∧ UnaryHistory gap ∧
                UnaryHistory realHandoff ∧ UnaryHistory consumer ∧ Cont mesh tags integrand ∧
                  Cont integrand sum darboux ∧ Cont darboux gap realHandoff ∧
                    Cont gap realHandoff consumer ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet gapRealConsumer consumerPkg
  obtain ⟨meshUnary, tagsUnary, integrandUnary, sumUnary, darbouxUnary, gapUnary,
    realHandoffUnary, transportsUnary, routesUnary, provenanceUnary, nameUnary, meshTagsIntegrand,
    integrandSumDarboux, darbouxGapReal, namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed gapUnary realHandoffUnary gapRealConsumer
  have core :
      NameCert
        (fun row : BHist =>
          hsame row name ∧
            RiemannIntegralPacket mesh tags integrand sum darboux gap realHandoff transports routes
              provenance name bundle pkg)
        hsame := by
    constructor
    · exact
        ⟨name, hsame_refl name, meshUnary, tagsUnary, integrandUnary, sumUnary, darbouxUnary,
          gapUnary, realHandoffUnary, transportsUnary, routesUnary, provenanceUnary, nameUnary,
          meshTagsIntegrand, integrandSumDarboux, darbouxGapReal, namePkg⟩
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
            RiemannIntegralPacket mesh tags integrand sum darboux gap realHandoff transports routes
              provenance name bundle pkg)
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
    ⟨semantic, meshUnary, tagsUnary, integrandUnary, sumUnary, darbouxUnary, gapUnary,
      realHandoffUnary, consumerUnary, meshTagsIntegrand, integrandSumDarboux, darbouxGapReal,
      gapRealConsumer, namePkg, consumerPkg⟩

theorem RiemannIntegralPacket_real_seal_boundary [AskSetup] [PackageSetup]
    {mesh tags integrand sum darboux gap realHandoff transports routes provenance name realSeal :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannIntegralPacket mesh tags integrand sum darboux gap realHandoff transports routes
        provenance name bundle pkg ->
      Cont gap realHandoff realSeal ->
        PkgSig bundle realSeal pkg ->
          UnaryHistory mesh ∧ UnaryHistory tags ∧ UnaryHistory integrand ∧ UnaryHistory sum ∧
            UnaryHistory darboux ∧ UnaryHistory gap ∧ UnaryHistory realHandoff ∧
              UnaryHistory realSeal ∧ Cont mesh tags integrand ∧ Cont integrand sum darboux ∧
                Cont darboux gap realHandoff ∧ Cont gap realHandoff realSeal ∧
                  PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet gapRealSeal sealPkg
  obtain ⟨meshUnary, tagsUnary, integrandUnary, sumUnary, darbouxUnary, gapUnary,
    realHandoffUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    meshTagsIntegrand, integrandSumDarboux, darbouxGapReal, namePkg⟩ := packet
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed gapUnary realHandoffUnary gapRealSeal
  exact
    ⟨meshUnary, tagsUnary, integrandUnary, sumUnary, darbouxUnary, gapUnary,
      realHandoffUnary, sealUnary, meshTagsIntegrand, integrandSumDarboux, darbouxGapReal,
      gapRealSeal, namePkg, sealPkg⟩

end BEDC.Derived.RiemannIntegralUp
