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

theorem ParsevalSOneBasisLedger [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      sourceBasis coefficientRead basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont source pairing sourceBasis →
        Cont fourier source coefficientRead →
          Cont sourceBasis coefficientRead basisRead →
            PkgSig bundle basisRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row source ∨ hsame row pairing ∨ hsame row sourceBasis ∨
                      hsame row coefficientRead ∨ hsame row basisRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont source pairing sourceBasis ∧
                      Cont fourier source coefficientRead ∧
                        Cont sourceBasis coefficientRead basisRead ∧
                          PkgSig bundle basisRead pkg)
                  hsame ∧
                UnaryHistory sourceBasis ∧ UnaryHistory coefficientRead ∧
                  UnaryHistory basisRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourcePairingBasis fourierSourceCoefficient basisRoute basisPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, _integralUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have sourceBasisUnary : UnaryHistory sourceBasis :=
    unary_cont_closed sourceUnary pairingUnary sourcePairingBasis
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary fourierSourceCoefficient
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed sourceBasisUnary coefficientUnary basisRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row pairing ∨ hsame row sourceBasis ∨
              hsame row coefficientRead ∨ hsame row basisRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source pairing sourceBasis ∧
              Cont fourier source coefficientRead ∧
                Cont sourceBasis coefficientRead basisRead ∧ PkgSig bundle basisRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro basisRead ⟨hsame_refl basisRead, basisUnary⟩
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
      exact ⟨source.right, sourcePairingBasis, fourierSourceCoefficient, basisRoute, basisPkg⟩
  }
  exact ⟨cert, sourceBasisUnary, coefficientUnary, basisUnary⟩

end BEDC.Derived.ParsevalUp
