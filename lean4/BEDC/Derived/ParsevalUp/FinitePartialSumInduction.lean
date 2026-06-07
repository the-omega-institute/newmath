import BEDC.Derived.ParsevalUp.RootEnergyCarrierAdmission
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalFinitePartialSumInduction [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      baseWindow stepWindow partialLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont BHist.Empty fourier baseWindow →
        Cont baseWindow source stepWindow →
          Cont stepWindow tolerance partialLedger →
            PkgSig bundle partialLedger pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row partialLedger ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row BHist.Empty ∨ hsame row fourier ∨ hsame row baseWindow ∨
                      hsame row stepWindow ∨ hsame row partialLedger)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont BHist.Empty fourier baseWindow ∧
                      Cont baseWindow source stepWindow ∧
                        Cont stepWindow tolerance partialLedger ∧
                          PkgSig bundle partialLedger pkg)
                  hsame ∧ UnaryHistory baseWindow ∧ UnaryHistory stepWindow ∧
                UnaryHistory partialLedger := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier baseRoute stepRoute partialRoute partialPkg
  obtain ⟨fourierUnary, sourceUnary, _pairingUnary, _integralUnary, _readbackUnary,
    toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have baseUnary : UnaryHistory baseWindow :=
    unary_cont_closed emptyUnary fourierUnary baseRoute
  have stepUnary : UnaryHistory stepWindow :=
    unary_cont_closed baseUnary sourceUnary stepRoute
  have partialUnary : UnaryHistory partialLedger :=
    unary_cont_closed stepUnary toleranceUnary partialRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row partialLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row BHist.Empty ∨ hsame row fourier ∨ hsame row baseWindow ∨
              hsame row stepWindow ∨ hsame row partialLedger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont BHist.Empty fourier baseWindow ∧
              Cont baseWindow source stepWindow ∧ Cont stepWindow tolerance partialLedger ∧
                PkgSig bundle partialLedger pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro partialLedger ⟨hsame_refl partialLedger, partialUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, baseRoute, stepRoute, partialRoute, partialPkg⟩
  }
  exact ⟨cert, baseUnary, stepUnary, partialUnary⟩

end BEDC.Derived.ParsevalUp
