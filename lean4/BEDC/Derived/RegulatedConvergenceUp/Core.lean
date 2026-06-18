import BEDC.Derived.RegulatedConvergenceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatedConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatedConvergenceCarrier
    (family uniformTail finiteWindow regularReadback realSeal integralHandoff transport
      route provenance localName : BHist) : Prop :=
  UnaryHistory family ∧ UnaryHistory uniformTail ∧ UnaryHistory finiteWindow ∧
    UnaryHistory regularReadback ∧ UnaryHistory realSeal ∧ UnaryHistory integralHandoff ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ hsame localName family ∧
          Cont family uniformTail finiteWindow ∧ Cont finiteWindow regularReadback realSeal ∧
            Cont realSeal integralHandoff transport ∧ Cont transport route provenance

theorem RegulatedConvergenceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {family uniformTail finiteWindow regularReadback realSeal integralHandoff transport route
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedConvergenceCarrier family uniformTail finiteWindow regularReadback realSeal
        integralHandoff transport route provenance localName →
      PkgSig bundle provenance pkg →
        SemanticNameCert
            (fun row : BHist =>
              hsame row localName ∧
                RegulatedConvergenceCarrier family uniformTail finiteWindow regularReadback
                  realSeal integralHandoff transport route provenance localName)
            (fun row : BHist =>
              hsame row family ∨ hsame row uniformTail ∨ hsame row finiteWindow ∨
                hsame row regularReadback ∨ hsame row realSeal ∨
                  hsame row integralHandoff)
            (fun row : BHist => hsame row localName ∧ PkgSig bundle provenance pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory Cont
  intro carrierEvidence provenancePkg
  obtain ⟨_familyUnary, _uniformTailUnary, _finiteWindowUnary, _regularReadbackUnary,
    _realSealUnary, _integralHandoffUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, localNameFamily, _familyUniformWindow, _windowReadSeal,
    _sealIntegralTransport, _transportRouteProvenance⟩ := carrierEvidence
  have carrierRebuilt :
      RegulatedConvergenceCarrier family uniformTail finiteWindow regularReadback realSeal
        integralHandoff transport route provenance localName := by
    exact
      ⟨_familyUnary, _uniformTailUnary, _finiteWindowUnary, _regularReadbackUnary,
        _realSealUnary, _integralHandoffUnary, _transportUnary, _routeUnary, _provenanceUnary,
        _localNameUnary, localNameFamily, _familyUniformWindow, _windowReadSeal,
        _sealIntegralTransport, _transportRouteProvenance⟩
  have sourceLocal :
      (fun row : BHist =>
        hsame row localName ∧
          RegulatedConvergenceCarrier family uniformTail finiteWindow regularReadback
            realSeal integralHandoff transport route provenance localName) localName := by
    exact ⟨hsame_refl localName, carrierRebuilt⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocal
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inl (hsame_trans source.left localNameFamily)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg⟩
  }

end BEDC.Derived.RegulatedConvergenceUp
