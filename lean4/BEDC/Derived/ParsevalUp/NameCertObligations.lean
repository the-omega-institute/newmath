import BEDC.Derived.ParsevalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ParsevalCarrierSurface [AskSetup] [PackageSetup]
    (F S I E R D L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: ParsevalUp BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory F ∧ UnaryHistory S ∧ UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory R ∧
    UnaryHistory D ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem ParsevalNameCertObligations [AskSetup] [PackageSetup]
    {F S I E R D L H C P N coefficientRead energyRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrierSurface F S I E R D L H C P N bundle pkg →
      Cont F S coefficientRead →
        Cont I E energyRead →
          Cont energyRead L sealRead →
            Cont sealRead N namedRead →
              PkgSig bundle namedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨
                        hsame row R ∨ hsame row D ∨ hsame row L ∨ hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F S coefficientRead ∧
                        Cont I E energyRead ∧ Cont energyRead L sealRead ∧
                          Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle namedRead pkg)
                    hsame ∧ UnaryHistory coefficientRead ∧ UnaryHistory energyRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: ParsevalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientWindow integralEnergy energySeal sealNamed namedPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    _toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientWindow
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary integralEnergy
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed energyUnary sealUnary energySeal
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealReadUnary localNameUnary sealNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨ hsame row R ∨
              hsame row D ∨ hsame row L ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F S coefficientRead ∧ Cont I E energyRead ∧
              Cont energyRead L sealRead ∧ Cont sealRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
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
        ⟨source.right, coefficientWindow, integralEnergy, energySeal, sealNamed,
          provenancePkg, namedPkg⟩
  }
  exact ⟨cert, coefficientUnary, energyUnary, sealReadUnary, namedUnary⟩

theorem ParsevalDyadicToleranceLedger [AskSetup] [PackageSetup]
    {F S I E R D L H C P N coefficientRead energyRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrierSurface F S I E R D L H C P N bundle pkg ->
      Cont F S coefficientRead ->
        Cont I E energyRead ->
          Cont energyRead D toleranceRead ->
            Cont toleranceRead L sealRead ->
              PkgSig bundle sealRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨
                        hsame row D ∨ hsame row L ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont F S coefficientRead ∧
                        Cont I E energyRead ∧ Cont energyRead D toleranceRead ∧
                          Cont toleranceRead L sealRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle sealRead pkg)
                    hsame ∧ UnaryHistory coefficientRead ∧ UnaryHistory energyRead ∧
                  UnaryHistory toleranceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: ParsevalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coefficientRoute energyRoute toleranceRoute sealRoute sealPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, provenancePkg, _localNamePkg⟩ := carrier
  have coefficientUnary : UnaryHistory coefficientRead :=
    unary_cont_closed fourierUnary sourceUnary coefficientRoute
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary energyRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed energyUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨ hsame row D ∨
              hsame row L ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F S coefficientRead ∧ Cont I E energyRead ∧
              Cont energyRead D toleranceRead ∧ Cont toleranceRead L sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coefficientRoute, energyRoute, toleranceRoute, sealRoute,
          provenancePkg, sealPkg⟩
  }
  exact ⟨cert, coefficientUnary, energyUnary, toleranceReadUnary, sealReadUnary⟩

end BEDC.Derived.ParsevalUp
