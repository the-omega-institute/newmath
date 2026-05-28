import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedBoundedIntervalCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalCompactCarrier [AskSetup] [PackageSetup]
    (intervalSource finiteNet uniformModulus compactMetric realSeal transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory intervalSource ∧ UnaryHistory finiteNet ∧ UnaryHistory uniformModulus ∧
    UnaryHistory compactMetric ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont intervalSource finiteNet compactMetric ∧ Cont uniformModulus compactMetric realSeal ∧
          Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle localName pkg

theorem ClosedBoundedIntervalCompactPacket_finite_net_route [AskSetup] [PackageSetup]
    {intervalSource finiteNet uniformModulus compactMetric realSeal transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalCompactCarrier intervalSource finiteNet uniformModulus compactMetric
        realSeal transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row realSeal ∧
              ClosedBoundedIntervalCompactCarrier intervalSource finiteNet uniformModulus
                compactMetric realSeal transport replay provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row intervalSource ∨ hsame row finiteNet ∨ hsame row compactMetric ∨
              hsame row realSeal ∨ Cont intervalSource finiteNet compactMetric)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧ hsame row realSeal)
          hsame ∧
        UnaryHistory intervalSource ∧ UnaryHistory finiteNet ∧ UnaryHistory compactMetric ∧
          UnaryHistory realSeal ∧ Cont intervalSource finiteNet compactMetric ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  have carrierRows := carrier
  obtain ⟨intervalUnary, finiteUnary, _uniformUnary, compactUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, finiteRoute,
    _uniformRoute, _replayRoute, provenancePkg, localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row realSeal ∧
              ClosedBoundedIntervalCompactCarrier intervalSource finiteNet uniformModulus
                compactMetric realSeal transport replay provenance localName bundle pkg)
          (fun row : BHist =>
            hsame row intervalSource ∨ hsame row finiteNet ∨ hsame row compactMetric ∨
              hsame row realSeal ∨ Cont intervalSource finiteNet compactMetric)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧ hsame row realSeal)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal
        ⟨hsame_refl realSeal, carrierRows⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, localNamePkg, source.left⟩
  }
  exact
    ⟨cert, intervalUnary, finiteUnary, compactUnary, realSealUnary, finiteRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.ClosedBoundedIntervalCompactUp
