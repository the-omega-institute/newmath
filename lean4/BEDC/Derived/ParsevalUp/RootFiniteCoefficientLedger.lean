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

theorem ParsevalRootFiniteCoefficientLedger [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead finiteLedger rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont coefficientRead tolerance finiteLedger →
          Cont finiteLedger replay rootRead →
            PkgSig bundle rootRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row fourier ∨ hsame row source ∨ hsame row coefficientRead ∨
                      hsame row tolerance ∨ hsame row finiteLedger ∨ hsame row rootRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont fourier source coefficientRead ∧
                      Cont coefficientRead tolerance finiteLedger ∧
                        Cont finiteLedger replay rootRead ∧ PkgSig bundle rootRead pkg)
                  hsame ∧ UnaryHistory coefficientRead ∧ UnaryHistory finiteLedger ∧
                UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute finiteRoute rootRoute rootPkg
  obtain ⟨fourierUnary, sourceUnary, _pairingUnary, _integralUnary, _readbackUnary,
    toleranceUnary, _sealUnary, _transportUnary, replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback,
    _readbackToleranceSeal, _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have finiteUnary : UnaryHistory finiteLedger :=
    unary_cont_closed coefficientUnary toleranceUnary finiteRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed finiteUnary replayUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fourier ∨ hsame row source ∨ hsame row coefficientRead ∨
              hsame row tolerance ∨ hsame row finiteLedger ∨ hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont fourier source coefficientRead ∧
              Cont coefficientRead tolerance finiteLedger ∧ Cont finiteLedger replay rootRead ∧
                PkgSig bundle rootRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coefficientRoute, finiteRoute, rootRoute, rootPkg⟩
  }
  exact ⟨cert, coefficientUnary, finiteUnary, rootUnary⟩

end BEDC.Derived.ParsevalUp
