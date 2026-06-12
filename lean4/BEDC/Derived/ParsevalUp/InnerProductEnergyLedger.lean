import BEDC.Derived.ParsevalUp.InnerProductNameCertObligations

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalInnerProductEnergyLedger [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      coefficientRead energyRead combinedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont fourier source coefficientRead →
        Cont pairing integral energyRead →
          Cont coefficientRead energyRead combinedRead →
            Cont combinedRead replay namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
                        hsame row integral ∨ hsame row coefficientRead ∨
                          hsame row energyRead ∨ hsame row combinedRead ∨
                            hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont fourier source coefficientRead ∧
                        Cont pairing integral energyRead ∧
                          Cont coefficientRead energyRead combinedRead ∧
                            Cont combinedRead replay namedRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory coefficientRead ∧ UnaryHistory energyRead ∧
                    UnaryHistory combinedRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute energyRoute combinedRoute namedRoute namedPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, replayUnary, _provenanceUnary, _nameUnary,
    _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, provenancePkg, _namePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed coefficientUnary energyUnary combinedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed combinedUnary replayUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
              hsame row integral ∨ hsame row coefficientRead ∨
                hsame row energyRead ∨ hsame row combinedRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont fourier source coefficientRead ∧
              Cont pairing integral energyRead ∧ Cont coefficientRead energyRead combinedRead ∧
                Cont combinedRead replay namedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        ⟨source.right, coefficientRoute, energyRoute, combinedRoute, namedRoute,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, coefficientUnary, energyUnary, combinedUnary, namedUnary⟩

end BEDC.Derived.ParsevalUp
