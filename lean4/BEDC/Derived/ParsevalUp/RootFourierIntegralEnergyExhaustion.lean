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

theorem ParsevalRootFourierIntegralEnergyExhaustion [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead energyRead toleranceRead sealRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont pairing integral energyRead →
          Cont energyRead tolerance toleranceRead →
            Cont toleranceRead sealRow sealRead →
              Cont sealRead replay rootRead →
                PkgSig bundle rootRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
                          hsame row integral ∨ hsame row readback ∨ hsame row tolerance ∨
                            hsame row sealRow ∨ hsame row rootRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont fourier source coefficientRead ∧
                          Cont pairing integral energyRead ∧
                            Cont energyRead tolerance toleranceRead ∧
                              Cont toleranceRead sealRow sealRead ∧
                                Cont sealRead replay rootRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle rootRead pkg)
                      hsame ∧
                    UnaryHistory coefficientRead ∧ UnaryHistory energyRead ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute energyRoute toleranceRoute sealRoute rootRoute rootPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, replayUnary, provenanceUnary, _nameUnary,
    _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed energyUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sealReadUnary replayUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
              hsame row integral ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row sealRow ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont fourier source coefficientRead ∧
              Cont pairing integral energyRead ∧ Cont energyRead tolerance toleranceRead ∧
                Cont toleranceRead sealRow sealRead ∧ Cont sealRead replay rootRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coefficientRoute, energyRoute, toleranceRoute, sealRoute, rootRoute,
          provenancePkg, rootPkg⟩
  }
  exact ⟨cert, coefficientUnary, energyUnary, toleranceReadUnary, sealReadUnary, rootUnary⟩

end BEDC.Derived.ParsevalUp
