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
          Cont darboux gap realHandoff ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle name pkg

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
    integrandSumDarboux, darbouxGapReal, _provenancePkg, namePkg⟩ := packet
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
          meshTagsIntegrand, integrandSumDarboux, darbouxGapReal, _provenancePkg, namePkg⟩
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
    meshTagsIntegrand, integrandSumDarboux, darbouxGapReal, _provenancePkg, namePkg⟩ := packet
  have sealUnary : UnaryHistory realSeal :=
    unary_cont_closed gapUnary realHandoffUnary gapRealSeal
  exact
    ⟨meshUnary, tagsUnary, integrandUnary, sumUnary, darbouxUnary, gapUnary,
      realHandoffUnary, sealUnary, meshTagsIntegrand, integrandSumDarboux, darbouxGapReal,
      gapRealSeal, namePkg, sealPkg⟩

theorem RiemannIntegralCarrier_scope_closure_package [AskSetup] [PackageSetup]
    {M T F S D G R H C P N consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannIntegralPacket M T F S D G R H C P N bundle pkg ->
      Cont G R consumer ->
        PkgSig bundle consumer pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row S ∨
                  hsame row D ∨ hsame row G ∨ hsame row R ∨ Cont G R consumer)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle consumer pkg ∧ hsame row consumer)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory F ∧ UnaryHistory S ∧
              UnaryHistory D ∧ UnaryHistory G ∧ UnaryHistory R ∧ UnaryHistory consumer ∧
                Cont M T F ∧ Cont F S D ∧ Cont D G R ∧ Cont G R consumer ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet gapRealConsumer consumerPkg
  obtain ⟨mUnary, tUnary, fUnary, sUnary, dUnary, gUnary, rUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, mtf, fsd, dgr, provenancePkg, _namePkg⟩ := packet
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed gUnary rUnary gapRealConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row S ∨ hsame row D ∨
              hsame row G ∨ hsame row R ∨ Cont G R consumer)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle consumer pkg ∧ hsame row consumer)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer ⟨hsame_refl consumer, consumerUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows source
        have otherSame : hsame other consumer :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr gapRealConsumer))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, consumerPkg, source.left⟩
  }
  exact
    ⟨cert, mUnary, tUnary, fUnary, sUnary, dUnary, gUnary, rUnary, consumerUnary, mtf, fsd,
      dgr, gapRealConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.RiemannIntegralUp
