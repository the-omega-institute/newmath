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

theorem ParsevalRootFourierInnerProductRoute [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead pairingRead routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont coefficientRead pairing pairingRead →
          Cont pairingRead integral routeRead →
            PkgSig bundle routeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
                      hsame row coefficientRead ∨ hsame row pairingRead ∨
                        hsame row routeRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont fourier source coefficientRead ∧
                      Cont coefficientRead pairing pairingRead ∧
                        Cont pairingRead integral routeRead ∧ PkgSig bundle routeRead pkg)
                  hsame ∧
                UnaryHistory coefficientRead ∧ UnaryHistory pairingRead ∧
                  UnaryHistory routeRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute pairingRoute routeIntegral routePkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback,
    _readbackToleranceSeal, _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have pairingReadUnary : UnaryHistory pairingRead :=
    unary_cont_closed coefficientUnary pairingUnary pairingRoute
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed pairingReadUnary integralUnary routeIntegral
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
              hsame row coefficientRead ∨ hsame row pairingRead ∨ hsame row routeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont fourier source coefficientRead ∧
              Cont coefficientRead pairing pairingRead ∧ Cont pairingRead integral routeRead ∧
                PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coefficientRoute, pairingRoute, routeIntegral, routePkg⟩
  }
  exact ⟨cert, coefficientUnary, pairingReadUnary, routeUnary⟩

end BEDC.Derived.ParsevalUp
