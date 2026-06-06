import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FanFunctionalCarrierSurface [AskSetup] [PackageSetup]
    (cantor fan tolerance branch depth witness modulus transport replay provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory hsame NameCert
  UnaryHistory cantor ∧ UnaryHistory fan ∧ UnaryHistory tolerance ∧
    UnaryHistory branch ∧ UnaryHistory depth ∧ UnaryHistory witness ∧
      UnaryHistory modulus ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ hsame transport localName ∧
          Cont branch depth witness ∧ Cont witness modulus replay ∧
            PkgSig bundle provenance pkg

theorem FanFunctionalNameCertObligations [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport
        replay provenance localName bundle pkg →
      Cont branch depth witness →
        Cont witness modulus modulusRead →
          PkgSig bundle modulusRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  FanFunctionalCarrierSurface cantor fan tolerance branch depth witness
                    modulus transport replay provenance localName bundle pkg ∧
                    hsame row modulus)
                (fun row : BHist =>
                  Cont branch depth witness ∧ Cont witness modulus modulusRead ∧
                    hsame row modulus)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle modulusRead pkg ∧
                    hsame row modulus)
                hsame ∧
              UnaryHistory witness ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier branchDepthWitness witnessModulusRead modulusReadPkg
  have carrierSurface :
      FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus
        transport replay provenance localName bundle pkg := carrier
  obtain ⟨_cantorUnary, _fanUnary, _toleranceUnary, branchUnary, depthUnary,
    witnessUnaryCarrier, modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _carrierBranchDepthWitness,
    _carrierWitnessModulusReplay, provenancePkg⟩ := carrier
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed branchUnary depthUnary branchDepthWitness
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary modulusUnary witnessModulusRead
  have sourceModulus :
      (fun row : BHist =>
        FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus
          transport replay provenance localName bundle pkg ∧ hsame row modulus) modulus := by
    exact ⟨carrierSurface, hsame_refl modulus⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus
              transport replay provenance localName bundle pkg ∧ hsame row modulus)
          (fun row : BHist =>
            Cont branch depth witness ∧ Cont witness modulus modulusRead ∧
              hsame row modulus)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle modulusRead pkg ∧
              hsame row modulus)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulus sourceModulus
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨branchDepthWitness, witnessModulusRead, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, modulusReadPkg, source.right⟩
  }
  exact ⟨cert, witnessUnaryCarrier, modulusReadUnary⟩

theorem FanFunctionalUniformModulusExtraction [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg →
      Cont branch depth witness →
        Cont witness modulus modulusRead →
          PkgSig bundle modulusRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row branch ∨ hsame row depth ∨ hsame row witness ∨ hsame row modulus ∨
                    hsame row modulusRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont branch depth witness ∧ Cont witness modulus modulusRead ∧
                    PkgSig bundle modulusRead pkg)
                hsame ∧
              UnaryHistory witness ∧ UnaryHistory modulusRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier branchDepthWitness witnessModulusRead modulusReadPkg
  obtain ⟨_cantorUnary, _fanUnary, _toleranceUnary, branchUnary, depthUnary,
    witnessUnaryCarrier, modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _transportLocalName, _carrierBranchDepthWitness,
    _carrierWitnessModulusReplay, _provenancePkg⟩ := carrier
  have witnessUnary : UnaryHistory witness :=
    unary_cont_closed branchUnary depthUnary branchDepthWitness
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary modulusUnary witnessModulusRead
  have sourceModulusRead :
      (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row) modulusRead := by
    exact ⟨hsame_refl modulusRead, modulusReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row modulusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row branch ∨ hsame row depth ∨ hsame row witness ∨ hsame row modulus ∨
              hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont branch depth witness ∧ Cont witness modulus modulusRead ∧
              PkgSig bundle modulusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro modulusRead sourceModulusRead
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro row source
      exact ⟨source.right, branchDepthWitness, witnessModulusRead, modulusReadPkg⟩
  }
  exact ⟨cert, witnessUnaryCarrier, modulusReadUnary⟩

end BEDC.Derived.FanfunctionalUp
