import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Derived.GapClosureBoundaryUp.TasteGate

namespace BEDC.Derived.GapClosureBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem GapClosureBoundary_refusal_nonescape [AskSetup] [PackageSetup]
    {G S R H C P N refusalRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont G C refusalRead ->
      Cont refusalRead R consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row refusalRead ∧
                  ∃ packet : GapClosureBoundaryUp,
                    packet = GapClosureBoundaryUp.mk G S R H C P N)
              (fun row : BHist => hsame row refusalRead ∧ Cont G C refusalRead)
              (fun row : BHist =>
                hsame row refusalRead ∧ Cont refusalRead R consumerRead ∧
                  PkgSig bundle consumerRead pkg)
              hsame ∧
            Cont G C refusalRead ∧ Cont refusalRead R consumerRead ∧
              PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro refusalRoute consumerRoute consumerPkg
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusalRead ∧
              ∃ packet : GapClosureBoundaryUp, packet = GapClosureBoundaryUp.mk G S R H C P N)
          (fun row : BHist => hsame row refusalRead ∧ Cont G C refusalRead)
          (fun row : BHist =>
            hsame row refusalRead ∧ Cont refusalRead R consumerRead ∧
              PkgSig bundle consumerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := by
          exact Exists.intro refusalRead
            (And.intro (hsame_refl refusalRead)
              (Exists.intro (GapClosureBoundaryUp.mk G S R H C P N) rfl))
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
          exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
      }
      pattern_sound := by
        intro _row source
        exact And.intro source.left refusalRoute
      ledger_sound := by
        intro _row source
        exact And.intro source.left (And.intro consumerRoute consumerPkg)
    }
  exact ⟨cert, refusalRoute, consumerRoute, consumerPkg⟩

end BEDC.Derived.GapClosureBoundaryUp
