import BEDC.Derived.RegularCauchyCompletionFrontierUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RegularCauchyCompletionFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem RegularCauchyCompletionFrontierNameCert_obligations [AskSetup] [PackageSetup]
    {D S R L M A T E H C P N completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (RegularCauchyCompletionFrontierUp.mk D S R L M A T E H C P N) =
        [D, S, R, L, M, A, T, E, H, C, P, N] ->
      Cont D S M ->
        Cont M A T ->
          Cont T E L ->
            Cont L H completionRead ->
              PkgSig bundle N pkg ->
                PkgSig bundle completionRead pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row completionRead ∧
                        ∃ packet : RegularCauchyCompletionFrontierUp,
                          packet = RegularCauchyCompletionFrontierUp.mk
                            D S R L M A T E H C P N ∧
                            FieldFaithful.fields packet =
                              [D, S, R, L, M, A, T, E, H, C, P, N])
                    (fun row : BHist =>
                      Cont D S M ∧ Cont M A T ∧ Cont T E L ∧ Cont L H row)
                    (fun row : BHist =>
                      hsame row completionRead ∧ PkgSig bundle completionRead pkg)
                    hsame ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro fields routeSource routeTail routeSeal routeCompletion namePkg completionPkg
  have sourceCompletion :
      (fun row : BHist =>
        hsame row completionRead ∧
          ∃ packet : RegularCauchyCompletionFrontierUp,
            packet = RegularCauchyCompletionFrontierUp.mk D S R L M A T E H C P N ∧
              FieldFaithful.fields packet = [D, S, R, L, M, A, T, E, H, C, P, N])
        completionRead := by
    exact ⟨hsame_refl completionRead,
      ⟨RegularCauchyCompletionFrontierUp.mk D S R L M A T E H C P N, rfl, fields⟩⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row completionRead ∧
            ∃ packet : RegularCauchyCompletionFrontierUp,
              packet = RegularCauchyCompletionFrontierUp.mk D S R L M A T E H C P N ∧
                FieldFaithful.fields packet = [D, S, R, L, M, A, T, E, H, C, P, N])
        (fun row : BHist =>
          Cont D S M ∧ Cont M A T ∧ Cont T E L ∧ Cont L H row)
        (fun row : BHist => hsame row completionRead ∧ PkgSig bundle completionRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro completionRead sourceCompletion
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨routeSource, routeTail, routeSeal,
            cont_result_hsame_transport routeCompletion (hsame_symm source.left)⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, completionPkg⟩
    }
  exact ⟨cert, namePkg, completionPkg⟩

end BEDC.Derived.RegularCauchyCompletionFrontierUp
