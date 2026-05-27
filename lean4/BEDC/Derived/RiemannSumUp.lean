import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

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

end BEDC.Derived.RiemannSumUp
