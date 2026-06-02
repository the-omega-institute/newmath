import BEDC.Derived.ClaimRegistryLayerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClaimRegistryLayerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClaimRegistryLayerCarrier
    (entry refusal closure formalTarget provenance verification transport package name :
      BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory entry ∧
    UnaryHistory refusal ∧
      UnaryHistory formalTarget ∧
        UnaryHistory provenance ∧
          UnaryHistory transport ∧
            UnaryHistory package ∧
              Cont entry refusal closure ∧
                Cont formalTarget provenance verification ∧
                  Cont transport package name

theorem ClaimRegistryLayer_export_control_certificate
    {entry refusal closure formalTarget provenance verification transport package name : BHist} :
    ClaimRegistryLayerCarrier entry refusal closure formalTarget provenance verification transport
        package name →
      SemanticNameCert
        (fun row : BHist => hsame row name ∧ UnaryHistory row)
        (fun row : BHist =>
          Cont entry refusal closure ∧ Cont formalTarget provenance verification ∧
            Cont transport package row)
        (fun row : BHist => hsame row name ∧ Cont transport package name)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier
  obtain ⟨unaryEntry, unaryRefusal, unaryFormalTarget, unaryProvenance, unaryTransport,
    unaryPackage, entryRoute, formalRoute, nameRoute⟩ := carrier
  have unaryName : UnaryHistory name :=
    unary_cont_closed unaryTransport unaryPackage nameRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, unaryName⟩
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
      intro row source
      exact
        ⟨entryRoute, formalRoute,
          cont_result_hsame_transport nameRoute (hsame_symm source.left)⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, nameRoute⟩
  }

theorem ClaimRegistryLayer_mature_package_claim_index [AskSetup] [PackageSetup]
    {entry refusal closure formalTarget provenance verification transport package name bridgeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClaimRegistryLayerCarrier entry refusal closure formalTarget provenance verification transport
        package name →
      Cont entry refusal bridgeRead →
        PkgSig bundle bridgeRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              ClaimRegistryLayerCarrier entry refusal closure formalTarget provenance verification
                  transport package name ∧
                hsame row bridgeRead)
            (fun row : BHist =>
              hsame row entry ∨
                hsame row refusal ∨
                  hsame row closure ∨
                    hsame row formalTarget ∨
                      hsame row provenance ∨
                        hsame row verification ∨
                          hsame row transport ∨
                            hsame row package ∨
                              hsame row name ∨ Cont entry refusal bridgeRead)
            (fun row : BHist =>
              hsame row bridgeRead ∧ UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier bridgeRoute packageSig
  have carrierSource :
      ClaimRegistryLayerCarrier entry refusal closure formalTarget provenance verification transport
        package name := carrier
  obtain ⟨unaryEntry, unaryRefusal, _unaryFormalTarget, _unaryProvenance, _unaryTransport,
    _unaryPackage, _closureRoute, _formalRoute, _nameRoute⟩ := carrier
  have unaryBridge : UnaryHistory bridgeRead :=
    unary_cont_closed unaryEntry unaryRefusal bridgeRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨carrierSource, hsame_refl bridgeRead⟩
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
      intro _row _source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr bridgeRoute))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right,
          unary_transport unaryBridge (hsame_symm source.right),
          packageSig⟩
  }

end BEDC.Derived.ClaimRegistryLayerUp
