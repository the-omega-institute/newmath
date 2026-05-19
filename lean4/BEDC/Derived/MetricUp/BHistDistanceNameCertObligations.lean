import BEDC.Derived.MetricUp

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricBHistDistance_namecert_obligations [AskSetup] [PackageSetup]
    {x y d witness carrierRoute provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricDistanceWitness x y d →
      Cont d witness carrierRoute →
        PkgSig bundle provenance pkg →
          PkgSig bundle name pkg →
            SemanticNameCert
                (fun row : BHist => MetricDistanceWitness x y d ∧ hsame row d)
                (fun row : BHist =>
                  Cont x y d ∧
                    (hsame row x ∨ hsame row y ∨ hsame row d ∨ hsame row carrierRoute))
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory d ∧ Cont d witness carrierRoute ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro distanceWitness dWitnessCarrierRoute provenancePkg namePkg
  have dUnary : UnaryHistory d := distanceWitness.right.right.left
  have cert :
      SemanticNameCert
          (fun row : BHist => MetricDistanceWitness x y d ∧ hsame row d)
          (fun row : BHist =>
            Cont x y d ∧
              (hsame row x ∨ hsame row y ∨ hsame row d ∨ hsame row carrierRoute))
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro d ⟨distanceWitness, hsame_refl d⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left.right.right.right, Or.inr (Or.inr (Or.inl source.right))⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport dUnary (hsame_symm source.right), provenancePkg⟩
  }
  exact ⟨cert, dUnary, dWitnessCarrierRoute, namePkg⟩

end BEDC.Derived.MetricUp
