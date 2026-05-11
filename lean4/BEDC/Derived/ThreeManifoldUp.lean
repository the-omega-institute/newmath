import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ThreeManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ThreeManifoldFiniteCarrier [AskSetup] [PackageSetup]
    (manifold topology decomposition classifier contRows provenance : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory manifold ∧ UnaryHistory topology ∧ UnaryHistory decomposition ∧
    UnaryHistory classifier ∧ UnaryHistory contRows ∧ UnaryHistory provenance ∧
      Cont manifold topology decomposition ∧ Cont decomposition classifier contRows ∧
        PkgSig probe provenance pkg

theorem ThreeManifoldFiniteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {manifold topology decomposition classifier contRows provenance : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows provenance
        probe pkg ->
      SemanticNameCert
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          hsame ∧
        Cont manifold topology decomposition ∧ Cont decomposition classifier contRows ∧
          PkgSig probe provenance pkg := by
  intro carrier
  have sourceProvenance :
      ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
          provenance probe pkg ∧ hsame provenance provenance :=
    And.intro carrier (hsame_refl provenance)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          (fun row : BHist =>
            ThreeManifoldFiniteCarrier manifold topology decomposition classifier contRows
              provenance probe pkg ∧ hsame row provenance)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance sourceProvenance
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact And.intro cert
    (And.intro carrier.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.left
        carrier.right.right.right.right.right.right.right.right))

end BEDC.Derived.ThreeManifoldUp
