import BEDC.Derived.NestedDyadicIntervalUp

namespace BEDC.Derived.NestedDyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NestedDyadicIntervalPacket_finite_prefix_induction_derivation [AskSetup] [PackageSetup]
    {first next tail schedule refinement provenance ledger endpoint nextTail chainedRefinement
      chainedEndpoint exported : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint bundle pkg →
      UnaryHistory tail → Cont next tail nextTail → Cont refinement tail chainedRefinement →
        Cont schedule chainedRefinement chainedEndpoint → Cont chainedEndpoint ledger exported →
          PkgSig bundle chainedEndpoint pkg → PkgSig bundle exported pkg →
            SemanticNameCert (fun row : BHist => hsame row exported ∧ UnaryHistory row)
              (fun row : BHist => hsame row first ∨ hsame row nextTail ∨ hsame row schedule ∨
                hsame row chainedRefinement ∨ hsame row chainedEndpoint ∨ hsame row exported)
              (fun row : BHist => UnaryHistory row ∧ Cont first nextTail chainedRefinement ∧
                Cont schedule chainedRefinement chainedEndpoint ∧
                  Cont chainedEndpoint ledger exported ∧ PkgSig bundle exported pkg)
              hsame ∧ NestedDyadicIntervalPacket first nextTail schedule chainedRefinement
                provenance ledger chainedEndpoint bundle pkg ∧ UnaryHistory exported := by
  -- BEDC touchpoint anchor: NestedDyadicIntervalPacket BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet tailUnary nextTailRoute chainedRefinementRoute chainedEndpointRoute exportRoute
    chainedEndpointSig exportedSig
  have chained := NestedDyadicIntervalPacket_successive_refinement_chain packet tailUnary
    nextTailRoute chainedRefinementRoute chainedEndpointRoute chainedEndpointSig
  have chainedPacket := chained.left
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed chainedPacket.right.right.right.right.right.right.left
      chainedPacket.right.right.right.right.right.left exportRoute
  refine ⟨?_, chainedPacket, exportedUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro exported ⟨hsame_refl exported, exportedUnary⟩
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, chained.left.right.right.right.right.right.right.right.left,
        chainedEndpointRoute, exportRoute, exportedSig⟩
  }

end BEDC.Derived.NestedDyadicIntervalUp
