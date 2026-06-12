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

def ParsevalInnerProductCarrierRoute [AskSetup] [PackageSetup]
    (F S I E R D L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: ParsevalCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  ParsevalCarrier F S I E R D L H C P N bundle pkg ∧ Cont F S I ∧ Cont I E R ∧
    Cont R D L ∧ Cont H C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem ParsevalInnerProductCarrierRoute_obligation [AskSetup] [PackageSetup]
    {F S I E R D L H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalInnerProductCarrierRoute F S I E R D L H C P N bundle pkg →
      SemanticNameCert
        (fun row : BHist => hsame row N ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row F ∨ hsame row S ∨ hsame row I ∨ hsame row E ∨ hsame row R ∨
            hsame row D ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont F S I ∧ Cont I E R ∧ Cont R D L ∧ Cont H C P ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := by
  -- BEDC touchpoint anchor: ParsevalInnerProductCarrierRoute ParsevalCarrier BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro route
  obtain ⟨carrier, fsiRoute, ierRoute, rdlRoute, hcpRoute, provenancePkg, localNamePkg⟩ :=
    route
  obtain ⟨_fourierUnary, _sourceUnary, _pairingUnary, _integralUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _carrierFsi, _carrierIer, _carrierRdl, _carrierLhc,
    _carrierProvenancePkg, _carrierLocalNamePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨hsame_refl N, localNameUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, fsiRoute, ierRoute, rdlRoute, hcpRoute, provenancePkg,
          localNamePkg⟩
  }

end BEDC.Derived.ParsevalUp
