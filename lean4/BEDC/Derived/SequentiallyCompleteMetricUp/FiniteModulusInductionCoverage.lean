import BEDC.Derived.SequentiallyCompleteMetricUp.TailInduction

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricFiniteModulusInductionCoverage [AskSetup] [PackageSetup]
    {X S M L D H C P N baseWindow stepWindow baseModulus stepModulus baseLimit stepLimit
      baseDistance stepDistance namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                UnaryHistory N ->
                  Cont X S baseWindow ->
                    Cont baseWindow M baseModulus ->
                      Cont baseModulus L baseLimit ->
                        Cont baseLimit D baseDistance ->
                          Cont baseDistance S stepWindow ->
                            Cont stepWindow M stepModulus ->
                              Cont stepModulus L stepLimit ->
                                Cont stepLimit D stepDistance ->
                                  Cont stepDistance N namedRead ->
                                    PkgSig bundle P pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row namedRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row S ∨ hsame row M ∨
                                              hsame row L ∨ hsame row D ∨
                                                hsame row baseDistance ∨
                                                  hsame row stepDistance ∨
                                                    hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont baseLimit D baseDistance ∧
                                                Cont stepLimit D stepDistance ∧
                                                  Cont stepDistance N namedRead ∧
                                                    PkgSig bundle P pkg)
                                          hsame ∧
                                        UnaryHistory baseDistance ∧
                                          UnaryHistory stepDistance ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro fields xUnary sUnary mUnary lUnary dUnary nUnary baseWindowRoute baseModulusRoute
    baseLimitRoute baseDistanceRoute stepWindowRoute stepModulusRoute stepLimitRoute
    stepDistanceRoute namedRoute packageRead
  have _acceptedFields :
      sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] := fields
  have baseWindowUnary : UnaryHistory baseWindow :=
    unary_cont_closed xUnary sUnary baseWindowRoute
  have baseModulusUnary : UnaryHistory baseModulus :=
    unary_cont_closed baseWindowUnary mUnary baseModulusRoute
  have baseLimitUnary : UnaryHistory baseLimit :=
    unary_cont_closed baseModulusUnary lUnary baseLimitRoute
  have baseDistanceUnary : UnaryHistory baseDistance :=
    unary_cont_closed baseLimitUnary dUnary baseDistanceRoute
  have stepWindowUnary : UnaryHistory stepWindow :=
    unary_cont_closed baseDistanceUnary sUnary stepWindowRoute
  have stepModulusUnary : UnaryHistory stepModulus :=
    unary_cont_closed stepWindowUnary mUnary stepModulusRoute
  have stepLimitUnary : UnaryHistory stepLimit :=
    unary_cont_closed stepModulusUnary lUnary stepLimitRoute
  have stepDistanceUnary : UnaryHistory stepDistance :=
    unary_cont_closed stepLimitUnary dUnary stepDistanceRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed stepDistanceUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨ hsame row D ∨
              hsame row baseDistance ∨ hsame row stepDistance ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont baseLimit D baseDistance ∧
              Cont stepLimit D stepDistance ∧ Cont stepDistance N namedRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, baseDistanceRoute, stepDistanceRoute, namedRoute, packageRead⟩
  }
  exact ⟨cert, baseDistanceUnary, stepDistanceUnary, namedUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
