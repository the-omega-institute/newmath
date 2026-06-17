import BEDC.Derived.ConnectedIntervalUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ConnectedIntervalDyadicNestingObligations [AskSetup] [PackageSetup]
    {L R W B S T E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConnectedIntervalCarrier L R W B S T E H C P N ->
      PkgSig bundle P pkg ->
        PkgSig bundle N pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row S ∧ ConnectedIntervalCarrier L R W B S T E H C P N)
              (fun row : BHist =>
                hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row B ∨
                  hsame row S ∨ hsame row T ∨ hsame row E ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont L W B ∧ Cont B S T ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory B ∧ UnaryHistory S ∧ Cont L W B ∧ Cont B S T := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier provenancePkg namePkg
  have carrierWhole := carrier
  obtain ⟨lUnary, _rUnary, wUnary, sUnary, _eUnary, branchRoute, nestingRoute,
    _sealRoute, _publicRoute⟩ := carrier
  have bUnary : UnaryHistory B :=
    unary_cont_closed lUnary wUnary branchRoute
  have sourceNested :
      (fun row : BHist =>
        hsame row S ∧ ConnectedIntervalCarrier L R W B S T E H C P N) S := by
    exact ⟨hsame_refl S, carrierWhole⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row S ∧ ConnectedIntervalCarrier L R W B S T E H C P N)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row W ∨ hsame row B ∨ hsame row S ∨
              hsame row T ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L W B ∧ Cont B S T ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro S sourceNested
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport sUnary (hsame_symm source.left), branchRoute, nestingRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, bUnary, sUnary, branchRoute, nestingRoute⟩

end BEDC.Derived.ConnectedIntervalUp
