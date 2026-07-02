import BEDC.Derived.NestedDyadicIntervalUp

namespace BEDC.Derived.NestedDyadicIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NestedDyadicIntervalPacket_dyadic_interval_source_route [AskSetup] [PackageSetup]
    {first next schedule refinement provenance ledger endpoint sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedDyadicIntervalPacket first next schedule refinement provenance ledger endpoint bundle pkg ->
      Cont first provenance sourceRead ->
        PkgSig bundle sourceRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row first ∨ hsame row next ∨ hsame row schedule ∨
                  hsame row refinement ∨ hsame row provenance ∨ hsame row ledger ∨
                    hsame row endpoint ∨ hsame row sourceRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont first next refinement ∧
                  Cont schedule refinement endpoint ∧ Cont first provenance sourceRead ∧
                    PkgSig bundle sourceRead pkg)
              hsame ∧
            UnaryHistory sourceRead := by
  -- BEDC touchpoint anchor: NestedDyadicIntervalPacket BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute sourceSig
  obtain ⟨firstUnary, _, _, _, provenanceUnary, _, _, refinementRoute, endpointRoute, _⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed firstUnary provenanceUnary sourceRoute
  exact ⟨{
    core := {
      carrier_inhabited := Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
      equiv_refl := by intro row _source; exact hsame_refl row
      equiv_symm := by intro _row _other sameRows; exact hsame_symm sameRows
      equiv_trans := by intro _ _ _ sameLeft sameRight; exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refinementRoute, endpointRoute, sourceRoute, sourceSig⟩
  }, sourceUnary⟩

end BEDC.Derived.NestedDyadicIntervalUp
