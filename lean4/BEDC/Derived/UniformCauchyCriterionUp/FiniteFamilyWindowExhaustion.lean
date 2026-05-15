import BEDC.Derived.UniformCauchyCriterionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_family_window_exhaustion [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windowRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      Cont index windows windowRead →
        PkgSig bundle windowRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports
                  routes provenance name bundle pkg ∧
                hsame row windowRead)
            (fun row : BHist => Cont index windows row ∧ PkgSig bundle windowRead pkg)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle windowRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet windowRoute windowPkg
  have packetWitness := packet
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, _tailUnary,
    _sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  have sourceWindow :
      (fun row : BHist =>
        UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports
            routes provenance name bundle pkg ∧
          hsame row windowRead) windowRead := by
    exact And.intro packetWitness (hsame_refl windowRead)
  exact {
    core := {
      carrier_inhabited := Exists.intro windowRead sourceWindow
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        And.intro (cont_result_hsame_transport windowRoute (hsame_symm source.right))
          windowPkg
    ledger_sound := by
      intro row source
      have windowUnary : UnaryHistory windowRead :=
        unary_cont_closed indexUnary windowsUnary windowRoute
      exact And.intro (unary_transport windowUnary (hsame_symm source.right)) windowPkg
  }

end BEDC.Derived.UniformCauchyCriterionUp
