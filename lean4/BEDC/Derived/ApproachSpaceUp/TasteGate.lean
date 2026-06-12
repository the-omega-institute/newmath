import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ApproachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

structure ApproachSpaceCarrier [AskSetup] [PackageSetup]
    (X D T F H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop where
  point_unary : UnaryHistory X
  distance_unary : UnaryHistory D
  topology_unary : UnaryHistory T
  filter_unary : UnaryHistory F
  transport_unary : UnaryHistory H
  replay_unary : UnaryHistory C
  name_unary : UnaryHistory N
  classifier_transport : Cont X D H
  metric_topology_compatibility : Cont D T C
  cauchy_filter_handoff : Cont D T F
  provenance_pkg : PkgSig bundle P pkg

theorem ApproachSpaceNameCertObligations [AskSetup] [PackageSetup]
    {X D T F H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApproachSpaceCarrier X D T F H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row P ∧ ApproachSpaceCarrier X D T F H C P N bundle pkg)
          (fun row : BHist =>
            hsame row X ∨ hsame row D ∨ hsame row T ∨ hsame row F ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row P ∧ PkgSig bundle P pkg)
          hsame ∧
        UnaryHistory X ∧ UnaryHistory D ∧ UnaryHistory T ∧ UnaryHistory F ∧
          UnaryHistory H ∧ UnaryHistory C ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row P ∧ ApproachSpaceCarrier X D T F H C P N bundle pkg)
          (fun row : BHist =>
            hsame row X ∨ hsame row D ∨ hsame row T ∨ hsame row F ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row P ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro P ⟨hsame_refl P, carrier⟩
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
      right
      right
      right
      right
      right
      right
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, source.right.provenance_pkg⟩
  }
  exact
    ⟨cert, carrier.point_unary, carrier.distance_unary, carrier.topology_unary,
      carrier.filter_unary, carrier.transport_unary, carrier.replay_unary,
      carrier.provenance_pkg⟩

end BEDC.Derived.ApproachSpaceUp
