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

theorem ParsevalInnerProductNormScope [AskSetup] [PackageSetup]
    {F S I E R D L H C P N normRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier F S I E R D L H C P N bundle pkg →
      Cont I L normRead →
        PkgSig bundle normRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row normRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row I ∨ hsame row L ∨ hsame row R ∨ hsame row D ∨
                  hsame row normRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont I L normRead ∧ PkgSig bundle normRead pkg)
              hsame ∧
            UnaryHistory normRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier normRoute normPkg
  obtain ⟨_fUnary, _sUnary, innerProductUnary, _energyUnary, _readbackUnary,
    _toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed innerProductUnary sealUnary normRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row normRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row L ∨ hsame row R ∨ hsame row D ∨
              hsame row normRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I L normRead ∧ PkgSig bundle normRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro normRead ⟨hsame_refl normRead, normUnary⟩
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
      exact ⟨source.right, normRoute, normPkg⟩
  }
  exact ⟨cert, normUnary⟩

end BEDC.Derived.ParsevalUp
