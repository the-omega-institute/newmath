import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Derived.RiemannSumUp.TasteGate

namespace BEDC.Derived.RiemannSumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RiemannSumCarrier [AskSetup] [PackageSetup]
    (mesh tag value width sum transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame
  UnaryHistory mesh ∧ UnaryHistory tag ∧ UnaryHistory value ∧ UnaryHistory width ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont mesh tag value ∧ Cont value width sum ∧
        Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg

theorem RiemannSumCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {mesh tag value width sum transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier mesh tag value width sum transport replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row sum ∧
              RiemannSumCarrier mesh tag value width sum transport replay provenance localName
                bundle pkg)
          (fun row : BHist =>
            hsame row sum ∧ UnaryHistory mesh ∧ UnaryHistory tag ∧ UnaryHistory value ∧
              UnaryHistory width)
          (fun row : BHist => hsame row sum ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory mesh ∧ UnaryHistory tag ∧ UnaryHistory value ∧ UnaryHistory width ∧
          UnaryHistory sum ∧ Cont mesh tag value ∧ Cont value width sum ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨meshUnary, tagUnary, valueUnary, widthUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, meshTagValue, valueWidthSum, _replayRoute,
    provenancePkg, _localNamePkg⟩ := carrier
  have carrierAtSum :
      RiemannSumCarrier mesh tag value width sum transport replay provenance localName
        bundle pkg :=
    ⟨meshUnary, tagUnary, valueUnary, widthUnary, _transportUnary, _replayUnary,
      _provenanceUnary, _localNameUnary, meshTagValue, valueWidthSum, _replayRoute,
      provenancePkg, _localNamePkg⟩
  have sumUnary : UnaryHistory sum :=
    unary_cont_closed valueUnary widthUnary valueWidthSum
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row sum ∧
              RiemannSumCarrier mesh tag value width sum transport replay provenance localName
                bundle pkg)
          (fun row : BHist =>
            hsame row sum ∧ UnaryHistory mesh ∧ UnaryHistory tag ∧ UnaryHistory value ∧
              UnaryHistory width)
          (fun row : BHist => hsame row sum ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sum ⟨hsame_refl sum, carrierAtSum⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, meshUnary, tagUnary, valueUnary, widthUnary⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }
  exact
    ⟨cert, meshUnary, tagUnary, valueUnary, widthUnary, sumUnary, meshTagValue,
      valueWidthSum, provenancePkg⟩

theorem RiemannSumCarrier_width_sum_exactness_obligation [AskSetup] [PackageSetup]
    {mesh tag value width sum transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier mesh tag value width sum transport replay provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row sum ∧
            RiemannSumCarrier mesh tag value width sum transport replay provenance localName
              bundle pkg)
        (fun row : BHist => hsame row sum ∧ UnaryHistory value ∧ UnaryHistory width)
        (fun row : BHist => hsame row sum ∧ Cont value width sum)
        hsame ∧ UnaryHistory width ∧ UnaryHistory sum ∧ Cont value width sum := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, replayUnary,
    provenanceUnary, localNameUnary, meshTagValue, valueWidthSum, replayRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have carrierAtSum :
      RiemannSumCarrier mesh tag value width sum transport replay provenance localName
        bundle pkg :=
    ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, replayUnary,
      provenanceUnary, localNameUnary, meshTagValue, valueWidthSum, replayRoute, provenancePkg,
      localNamePkg⟩
  have sumUnary : UnaryHistory sum :=
    unary_cont_closed valueUnary widthUnary valueWidthSum
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row sum ∧
            RiemannSumCarrier mesh tag value width sum transport replay provenance localName
              bundle pkg)
        (fun row : BHist => hsame row sum ∧ UnaryHistory value ∧ UnaryHistory width)
        (fun row : BHist => hsame row sum ∧ Cont value width sum)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sum ⟨hsame_refl sum, carrierAtSum⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, valueUnary, widthUnary⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, valueWidthSum⟩
  }
  exact ⟨cert, widthUnary, sumUnary, valueWidthSum⟩

theorem RiemannSumCarrier_ledger_nonescape_obligation [AskSetup] [PackageSetup]
    {mesh tag value width sum transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier mesh tag value width sum transport replay provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          hsame row provenance ∧
            RiemannSumCarrier mesh tag value width sum transport replay provenance localName
              bundle pkg)
        (fun row : BHist => hsame row provenance ∧ Cont transport replay provenance)
        (fun row : BHist =>
          hsame row provenance ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame ∧ Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert PkgSig
  intro carrier
  obtain ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, replayUnary,
    provenanceUnary, localNameUnary, meshTagValue, valueWidthSum, replayRoute, provenancePkg,
    localNamePkg⟩ := carrier
  have carrierAtProvenance :
      RiemannSumCarrier mesh tag value width sum transport replay provenance localName
        bundle pkg :=
    ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, replayUnary,
      provenanceUnary, localNameUnary, meshTagValue, valueWidthSum, replayRoute, provenancePkg,
      localNamePkg⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row provenance ∧
            RiemannSumCarrier mesh tag value width sum transport replay provenance localName
              bundle pkg)
        (fun row : BHist => hsame row provenance ∧ Cont transport replay provenance)
        (fun row : BHist =>
          hsame row provenance ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance ⟨hsame_refl provenance, carrierAtProvenance⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, replayRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, replayRoute, provenancePkg, localNamePkg⟩

theorem RiemannSumCarrier_darboux_handoff [AskSetup] [PackageSetup]
    {M T F W S H C P N darboux : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier M T F W S H C P N bundle pkg ->
      Cont S H darboux ->
        PkgSig bundle darboux pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row darboux ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨
                  hsame row S ∨ Cont S H darboux)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle darboux pkg ∧ hsame row darboux)
              hsame ∧
            UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory F ∧ UnaryHistory W ∧
              UnaryHistory S ∧ UnaryHistory darboux ∧ Cont M T F ∧ Cont F W S ∧
                Cont S H darboux ∧ PkgSig bundle P pkg ∧ PkgSig bundle darboux pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sumTransportDarboux darbouxPkg
  obtain ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, _replayUnary,
    provenanceUnary, _localNameUnary, meshTagValue, valueWidthSum, _transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have sumUnary : UnaryHistory S :=
    unary_cont_closed valueUnary widthUnary valueWidthSum
  have darbouxUnary : UnaryHistory darboux :=
    unary_cont_closed sumUnary transportUnary sumTransportDarboux
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row darboux ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨ hsame row S ∨
              Cont S H darboux)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle darboux pkg ∧ hsame row darboux)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro darboux ⟨hsame_refl darboux, darbouxUnary⟩
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
        have otherSame : hsame other darboux :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sumTransportDarboux))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, darbouxPkg, source.left⟩
  }
  exact
    ⟨cert, meshUnary, tagUnary, valueUnary, widthUnary, sumUnary, darbouxUnary,
      meshTagValue, valueWidthSum, sumTransportDarboux, provenancePkg, darbouxPkg⟩

theorem RiemannSumCarrier_public_finite_tagged_sum_interface [AskSetup] [PackageSetup]
    {M T F W S H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier M T F W S H C P N bundle pkg ->
      Cont S C publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨
                  hsame row S ∨ Cont S C publicRead)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                  PkgSig bundle publicRead pkg ∧ hsame row publicRead)
              hsame ∧
            UnaryHistory S ∧ UnaryHistory publicRead ∧ Cont S C publicRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sumReplayPublic publicPkg
  obtain ⟨_meshUnary, _tagUnary, valueUnary, widthUnary, _transportUnary, replayUnary,
    provenanceUnary, localNameUnary, _meshTagValue, valueWidthSum, _transportReplayProvenance,
    provenancePkg, localNamePkg⟩ := carrier
  have sumUnary : UnaryHistory S :=
    unary_cont_closed valueUnary widthUnary valueWidthSum
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sumUnary replayUnary sumReplayPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨ hsame row S ∨
              Cont S C publicRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
              PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sumReplayPublic))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, publicPkg, source.left⟩
  }
  exact ⟨cert, sumUnary, publicUnary, sumReplayPublic, provenancePkg, localNamePkg, publicPkg⟩

theorem RiemannSumCarrier_tagged_mesh_exactness [AskSetup] [PackageSetup]
    {M T F W S H C P N leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier M T F W S H C P N bundle pkg ->
      Cont M T F ->
        Cont F W S ->
          hsame leftRead S ->
            hsame rightRead S ->
              SemanticNameCert
                  (fun row : BHist => hsame row S ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨
                      hsame row S ∨ Cont M T F ∨ Cont F W S)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row S)
                  hsame ∧ hsame leftRead rightRead ∧ Cont M T F ∧ Cont F W S := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier meshTagValue valueWidthSum leftSame rightSame
  obtain ⟨_meshUnary, _tagUnary, valueUnary, widthUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _carrierMeshRoute, _carrierValueRoute,
    _transportReplayProvenance, provenancePkg, localNamePkg⟩ := carrier
  have sumUnary : UnaryHistory S :=
    unary_cont_closed valueUnary widthUnary valueWidthSum
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row S ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row W ∨ hsame row S ∨
              Cont M T F ∨ Cont F W S)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧ hsame row S)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro S ⟨hsame_refl S, sumUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }
  exact
    ⟨cert, hsame_trans leftSame (hsame_symm rightSame), meshTagValue, valueWidthSum⟩

theorem RiemannSumCarrier_tagless_refinement_ledger [AskSetup] [PackageSetup]
    {M T F W S H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier M T F W S H C P N bundle pkg ->
      riemannSumDecodeBHist (riemannSumEncodeBHist M) = M ∧
        riemannSumDecodeBHist (riemannSumEncodeBHist T) = T ∧
          riemannSumDecodeBHist (riemannSumEncodeBHist F) = F ∧
            riemannSumDecodeBHist (riemannSumEncodeBHist W) = W ∧
              riemannSumDecodeBHist (riemannSumEncodeBHist S) = S ∧
                riemannSumDecodeBHist (riemannSumEncodeBHist H) = H ∧
                  riemannSumDecodeBHist (riemannSumEncodeBHist C) = C ∧
                    riemannSumDecodeBHist (riemannSumEncodeBHist P) = P ∧
                      riemannSumDecodeBHist (riemannSumEncodeBHist N) = N := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg RiemannSumCarrier
  intro carrier
  obtain ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, replayUnary,
    provenanceUnary, localNameUnary, _meshTagValue, _valueWidthSum, _transportReplay,
    _provenancePkg, _localNamePkg⟩ := carrier
  have decode : ∀ row : BHist, riemannSumDecodeBHist (riemannSumEncodeBHist row) = row := by
    intro row
    induction row with
    | Empty => rfl
    | e0 row ih => exact congrArg BHist.e0 ih
    | e1 row ih => exact congrArg BHist.e1 ih
  have _acceptedRows :
      UnaryHistory M ∧ UnaryHistory T ∧ UnaryHistory F ∧ UnaryHistory W ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N :=
    ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, replayUnary,
      provenanceUnary, localNameUnary⟩
  exact
    ⟨decode M, decode T, decode F, decode W, decode S, decode H, decode C, decode P,
      decode N⟩

theorem RiemannSumCarrier_mesh_tag_obligation [AskSetup] [PackageSetup]
    {mesh tag value width sum transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier mesh tag value width sum transport replay provenance localName bundle pkg ->
      PkgSig bundle value pkg ->
        SemanticNameCert
            (fun row : BHist => hsame row value ∧ UnaryHistory row)
            (fun row : BHist => hsame row mesh ∨ hsame row tag ∨ Cont mesh tag value)
            (fun row : BHist =>
              PkgSig bundle provenance pkg ∧ PkgSig bundle value pkg ∧ hsame row value)
            hsame ∧
          UnaryHistory mesh ∧ UnaryHistory tag ∧ UnaryHistory value ∧ Cont mesh tag value ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle value pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier valuePkg
  obtain ⟨meshUnary, tagUnary, valueUnary, _widthUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, meshTagValue, _valueWidthSum, _replayRoute,
    provenancePkg, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row value ∧ UnaryHistory row)
          (fun row : BHist => hsame row mesh ∨ hsame row tag ∨ Cont mesh tag value)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle value pkg ∧ hsame row value)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro value ⟨hsame_refl value, valueUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr meshTagValue)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, valuePkg, source.left⟩
  }
  exact ⟨cert, meshUnary, tagUnary, valueUnary, meshTagValue, provenancePkg, valuePkg⟩

theorem RiemannSumCarrier_obligation_closure_package [AskSetup] [PackageSetup]
    {mesh tag value width sum transport replay provenance localName darbouRead consumerRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannSumCarrier mesh tag value width sum transport replay provenance localName bundle pkg ->
      Cont sum transport darbouRead ->
        Cont darbouRead replay consumerRead ->
          PkgSig bundle darbouRead pkg ->
            PkgSig bundle consumerRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row mesh ∨ hsame row tag ∨ hsame row value ∨ hsame row width ∨
                      hsame row sum ∨ Cont darbouRead replay consumerRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle darbouRead pkg ∧
                      PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
                  hsame ∧
                UnaryHistory mesh ∧ UnaryHistory tag ∧ UnaryHistory value ∧
                  UnaryHistory width ∧ UnaryHistory sum ∧ UnaryHistory darbouRead ∧
                    UnaryHistory consumerRead ∧ Cont mesh tag value ∧ Cont value width sum ∧
                      Cont sum transport darbouRead ∧
                        Cont darbouRead replay consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sumTransportDarbou darbouReplayConsumer darbouPkg consumerPkg
  obtain ⟨meshUnary, tagUnary, valueUnary, widthUnary, transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, meshTagValue, valueWidthSum, _replayRoute,
    provenancePkg, _localNamePkg⟩ := carrier
  have sumUnary : UnaryHistory sum :=
    unary_cont_closed valueUnary widthUnary valueWidthSum
  have darbouUnary : UnaryHistory darbouRead :=
    unary_cont_closed sumUnary transportUnary sumTransportDarbou
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed darbouUnary replayUnary darbouReplayConsumer
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row mesh ∨ hsame row tag ∨ hsame row value ∨ hsame row width ∨
              hsame row sum ∨ Cont darbouRead replay consumerRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle darbouRead pkg ∧
              PkgSig bundle consumerRead pkg ∧ hsame row consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr darbouReplayConsumer))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, darbouPkg, consumerPkg, source.left⟩
  }
  exact
    ⟨cert, meshUnary, tagUnary, valueUnary, widthUnary, sumUnary, darbouUnary,
      consumerUnary, meshTagValue, valueWidthSum, sumTransportDarbou, darbouReplayConsumer⟩

end BEDC.Derived.RiemannSumUp
