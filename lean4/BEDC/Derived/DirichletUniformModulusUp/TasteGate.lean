import BEDC.Derived.DirichletUniformModulusUp

namespace BEDC.Derived.DirichletUniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DirichletUniformModulusNameCertObligations [AskSetup] [PackageSetup]
    {boundedSums abelWindow monotoneWindow dyadicBudget modulusRow transports replay
      provenance localNameCert consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirichletUniformModulusCarrier boundedSums abelWindow monotoneWindow dyadicBudget
        modulusRow transports replay provenance localNameCert bundle pkg ->
      Cont modulusRow replay consumerRead ->
        PkgSig bundle consumerRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                (hsame row boundedSums ∨ hsame row abelWindow ∨
                    hsame row monotoneWindow ∨ hsame row dyadicBudget ∨
                      hsame row modulusRow ∨ hsame row consumerRead) ∧
                  UnaryHistory row)
              (fun row : BHist =>
                hsame row boundedSums ∨ hsame row abelWindow ∨
                  hsame row monotoneWindow ∨ hsame row dyadicBudget ∨
                    hsame row modulusRow ∨ hsame row consumerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont boundedSums abelWindow monotoneWindow ∧
                  Cont monotoneWindow dyadicBudget modulusRow ∧
                    Cont modulusRow replay provenance ∧
                      Cont modulusRow replay consumerRead ∧
                        PkgSig bundle provenance pkg ∧
                          PkgSig bundle localNameCert pkg ∧ PkgSig bundle consumerRead pkg)
              hsame ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier modulusReplayConsumer consumerPkg
  obtain ⟨_boundedUnary, _abelUnary, _monotoneUnary, _dyadicUnary, modulusUnary,
    _transportsUnary, replayUnary, _provenanceUnary, _localNameCertUnary,
    boundedAbelMonotone, monotoneDyadicModulus, modulusReplayProvenance,
    provenancePkg, localNameCertPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed modulusUnary replayUnary modulusReplayConsumer
  have sourceConsumer :
      (fun row : BHist =>
        (hsame row boundedSums ∨ hsame row abelWindow ∨ hsame row monotoneWindow ∨
            hsame row dyadicBudget ∨ hsame row modulusRow ∨ hsame row consumerRead) ∧
          UnaryHistory row)
        consumerRead := by
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl consumerRead))))),
      consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row boundedSums ∨ hsame row abelWindow ∨ hsame row monotoneWindow ∨
                hsame row dyadicBudget ∨ hsame row modulusRow ∨ hsame row consumerRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row boundedSums ∨ hsame row abelWindow ∨ hsame row monotoneWindow ∨
              hsame row dyadicBudget ∨ hsame row modulusRow ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundedSums abelWindow monotoneWindow ∧
              Cont monotoneWindow dyadicBudget modulusRow ∧ Cont modulusRow replay provenance ∧
                Cont modulusRow replay consumerRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localNameCert pkg ∧ PkgSig bundle consumerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceConsumer
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
        intro row other sameRows source
        have transportSame : hsame other row := hsame_symm sameRows
        have transportPattern :
            hsame other boundedSums ∨ hsame other abelWindow ∨
              hsame other monotoneWindow ∨ hsame other dyadicBudget ∨
                hsame other modulusRow ∨ hsame other consumerRead := by
          cases source.left with
          | inl sameBounded =>
              exact Or.inl (hsame_trans transportSame sameBounded)
          | inr rest0 =>
              cases rest0 with
              | inl sameAbel =>
                  exact Or.inr (Or.inl (hsame_trans transportSame sameAbel))
              | inr rest1 =>
                  cases rest1 with
                  | inl sameMonotone =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans transportSame sameMonotone)))
                  | inr rest2 =>
                      cases rest2 with
                      | inl sameDyadic =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans transportSame sameDyadic))))
                      | inr rest3 =>
                          cases rest3 with
                          | inl sameModulus =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans transportSame sameModulus)))))
                          | inr sameConsumer =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (hsame_trans transportSame sameConsumer)))))
        exact ⟨transportPattern, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, boundedAbelMonotone, monotoneDyadicModulus,
          modulusReplayProvenance, modulusReplayConsumer, provenancePkg, localNameCertPkg,
          consumerPkg⟩
  }
  exact ⟨cert, consumerUnary⟩

end BEDC.Derived.DirichletUniformModulusUp
