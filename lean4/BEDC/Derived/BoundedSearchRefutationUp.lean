import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundedSearchRefutationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedSearchRefutationCarrier [AskSetup] [PackageSetup]
    (proposition budget frontier refutation gap transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory proposition ∧ UnaryHistory budget ∧ UnaryHistory frontier ∧
    UnaryHistory refutation ∧ UnaryHistory gap ∧ UnaryHistory replay ∧
      UnaryHistory name ∧ Cont proposition budget frontier ∧
        Cont frontier refutation transport ∧ Cont transport replay gap ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem BoundedSearchRefutationNameCertObligations [AskSetup] [PackageSetup]
    {proposition budget frontier refutation gap transport replay provenance name
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSearchRefutationCarrier proposition budget frontier refutation gap transport replay
        provenance name bundle pkg ->
      Cont frontier refutation publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                BoundedSearchRefutationCarrier proposition budget frontier refutation gap
                    transport replay provenance name bundle pkg ∧ hsame row frontier)
              (fun row : BHist =>
                hsame row proposition ∨ hsame row budget ∨ hsame row frontier ∨
                  hsame row refutation ∨ hsame row gap ∨ hsame row publicRead)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                  hsame row frontier)
              hsame ∧ UnaryHistory frontier ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier frontierRefutationPublic publicPkg
  have carrierWitness :
      BoundedSearchRefutationCarrier proposition budget frontier refutation gap transport
        replay provenance name bundle pkg := carrier
  obtain ⟨propositionUnary, budgetUnary, frontierUnary, refutationUnary, _gapUnary,
    _replayUnary, _nameUnary, _propositionBudgetFrontier, _frontierRefutationTransport,
    _transportReplayGap, provenancePkg, _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed frontierUnary refutationUnary frontierRefutationPublic
  have certCore :
      NameCert
        (fun row : BHist =>
          BoundedSearchRefutationCarrier proposition budget frontier refutation gap transport
              replay provenance name bundle pkg ∧ hsame row frontier)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro frontier
        (And.intro carrierWitness (hsame_refl frontier))
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
        intro _row _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            BoundedSearchRefutationCarrier proposition budget frontier refutation gap
                transport replay provenance name bundle pkg ∧ hsame row frontier)
          (fun row : BHist =>
            hsame row proposition ∨ hsame row budget ∨ hsame row frontier ∨
              hsame row refutation ∨ hsame row gap ∨ hsame row publicRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              hsame row frontier)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inl source.right))
      ledger_sound := by
        intro _row source
        exact And.intro provenancePkg (And.intro publicPkg source.right)
    }
  exact And.intro semantic (And.intro frontierUnary publicUnary)

theorem BoundedSearchRefutationDepthSoundness [AskSetup] [PackageSetup]
    {A K F R G H C P N witnessRead depthRead boundedWitnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSearchRefutationCarrier A K F R G H C P N bundle pkg →
      Cont F R witnessRead →
        Cont K witnessRead depthRead →
          Cont depthRead N boundedWitnessRead →
            PkgSig bundle boundedWitnessRead pkg →
              SemanticNameCert
                    (fun row : BHist => hsame row boundedWitnessRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row F ∨ hsame row R ∨ hsame row N ∨
                        hsame row witnessRead ∨ hsame row depthRead ∨
                          hsame row boundedWitnessRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F R witnessRead ∧ Cont K witnessRead depthRead ∧
                        Cont depthRead N boundedWitnessRead ∧
                          PkgSig bundle boundedWitnessRead pkg)
                    hsame ∧
                  UnaryHistory witnessRead ∧ UnaryHistory depthRead ∧
                    UnaryHistory boundedWitnessRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier witnessRoute depthRoute boundedRoute boundedPkg
  obtain ⟨_aUnary, kUnary, fUnary, rUnary, _gUnary, _cUnary, nUnary,
    _propositionBudgetFrontier, _frontierRefutationTransport, _transportReplayGap,
    _provenancePkg, _namePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed fUnary rUnary witnessRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed kUnary witnessUnary depthRoute
  have boundedUnary : UnaryHistory boundedWitnessRead :=
    unary_cont_closed depthUnary nUnary boundedRoute
  have semantic :
      SemanticNameCert
          (fun row : BHist => hsame row boundedWitnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row R ∨ hsame row N ∨
              hsame row witnessRead ∨ hsame row depthRead ∨ hsame row boundedWitnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F R witnessRead ∧ Cont K witnessRead depthRead ∧
              Cont depthRead N boundedWitnessRead ∧ PkgSig bundle boundedWitnessRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro boundedWitnessRead ⟨hsame_refl boundedWitnessRead, boundedUnary⟩
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
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, witnessRoute, depthRoute, boundedRoute, boundedPkg⟩
  }
  exact And.intro semantic (And.intro witnessUnary (And.intro depthUnary boundedUnary))

theorem BoundedSearchRefutationNonEscape [AskSetup] [PackageSetup]
    {proposition budget frontier refutation gap transport replay provenance name
      consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSearchRefutationCarrier proposition budget frontier refutation gap transport replay
        provenance name bundle pkg ->
      Cont transport replay consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row proposition ∨ hsame row budget ∨ hsame row frontier ∨
                  hsame row refutation ∨ hsame row gap ∨ hsame row consumerRead)
              (fun row : BHist =>
                hsame row consumerRead ∧ Cont transport replay consumerRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg)
              hsame ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier transportReplayConsumer consumerPkg
  obtain ⟨_propositionUnary, _budgetUnary, frontierUnary, refutationUnary, _gapUnary,
    replayUnary, _nameUnary, _propositionBudgetFrontier, frontierRefutationTransport,
    _transportReplayGap, provenancePkg, _namePkg⟩ := carrier
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed frontierUnary refutationUnary frontierRefutationTransport
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed transportUnary replayUnary transportReplayConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row proposition ∨ hsame row budget ∨ hsame row frontier ∨
              hsame row refutation ∨ hsame row gap ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont transport replay consumerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, transportReplayConsumer, provenancePkg, consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

theorem BoundedSearchRefutationObligationScope [AskSetup] [PackageSetup]
    {A K F R G H C P N initialRead stepRead boundedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSearchRefutationCarrier A K F R G H C P N bundle pkg ->
      Cont A K initialRead ->
        Cont initialRead F stepRead ->
          Cont stepRead N boundedRead ->
            PkgSig bundle boundedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row A ∨ hsame row K ∨ hsame row F ∨ hsame row R ∨
                      hsame row G ∨ hsame row N ∨ hsame row initialRead ∨
                        hsame row stepRead ∨ hsame row boundedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont A K initialRead ∧
                      Cont initialRead F stepRead ∧ Cont stepRead N boundedRead ∧
                        PkgSig bundle boundedRead pkg)
                  hsame ∧
                UnaryHistory initialRead ∧ UnaryHistory stepRead ∧
                  UnaryHistory boundedRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier initialRoute stepRoute boundedRoute boundedPkg
  obtain ⟨aUnary, kUnary, fUnary, _rUnary, _gUnary, _hUnary, nUnary,
    _propositionBudgetFrontier, _frontierRefutationTransport, _transportReplayGap,
    _provenancePkg, _namePkg⟩ := carrier
  have initialUnary : UnaryHistory initialRead :=
    unary_cont_closed aUnary kUnary initialRoute
  have stepUnary : UnaryHistory stepRead :=
    unary_cont_closed initialUnary fUnary stepRoute
  have boundedUnary : UnaryHistory boundedRead :=
    unary_cont_closed stepUnary nUnary boundedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row K ∨ hsame row F ∨ hsame row R ∨
              hsame row G ∨ hsame row N ∨ hsame row initialRead ∨
                hsame row stepRead ∨ hsame row boundedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A K initialRead ∧ Cont initialRead F stepRead ∧
              Cont stepRead N boundedRead ∧ PkgSig bundle boundedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedRead ⟨hsame_refl boundedRead, boundedUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, initialRoute, stepRoute, boundedRoute, boundedPkg⟩
  }
  exact ⟨cert, initialUnary, stepUnary, boundedUnary⟩

theorem BoundedSearchRefutationPublicExport [AskSetup] [PackageSetup]
    {A K F R G H C P N witnessRead gapRead publicRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSearchRefutationCarrier A K F R G H C P N bundle pkg →
      Cont F R witnessRead →
        Cont F G gapRead →
          Cont witnessRead gapRead publicRead →
            Cont publicRead N exportRead →
              PkgSig bundle exportRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row K ∨ hsame row F ∨ hsame row R ∨
                        hsame row G ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row publicRead ∨ hsame row exportRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F R witnessRead ∧ Cont F G gapRead ∧
                        Cont witnessRead gapRead publicRead ∧
                          Cont publicRead N exportRead ∧ PkgSig bundle exportRead pkg)
                    hsame ∧
                  UnaryHistory witnessRead ∧ UnaryHistory gapRead ∧
                    UnaryHistory publicRead ∧ UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier witnessRoute gapRoute publicRoute exportRoute exportPkg
  obtain ⟨_aUnary, _kUnary, fUnary, rUnary, gUnary, _hUnary, nUnary,
    _akFrontier, _frTransport, _hcGap, _provenancePkg, _namePkg⟩ := carrier
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed fUnary rUnary witnessRoute
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed fUnary gUnary gapRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed witnessUnary gapUnary publicRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed publicUnary nUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row K ∨ hsame row F ∨ hsame row R ∨ hsame row G ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row publicRead ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F R witnessRead ∧ Cont F G gapRead ∧
              Cont witnessRead gapRead publicRead ∧ Cont publicRead N exportRead ∧
                PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, witnessRoute, gapRoute, publicRoute, exportRoute, exportPkg⟩
  }
  exact ⟨cert, witnessUnary, gapUnary, publicUnary, exportUnary⟩

end BEDC.Derived.BoundedSearchRefutationUp
