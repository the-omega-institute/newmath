import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_obligation_closure_package [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name handoff
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      UnaryHistory normal →
        Cont normal continuation handoff →
          Cont handoff routes consumer →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row typed ∨ hsame row terminal ∨ hsame row normal ∨
                      hsame row continuation ∨ hsame row handoff ∨ hsame row consumer)
                  (fun _row : BHist =>
                    Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
                      Cont normal continuation handoff ∧ Cont handoff routes consumer)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (PkgSig bundle provenance pkg ∨ PkgSig bundle consumer pkg))
                  hsame ∧
                UnaryHistory handoff ∧ UnaryHistory consumer ∧
                  hsame handoff (append normal continuation) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet normalUnary normalContinuationHandoff handoffRoutesConsumer consumerPkg
  obtain ⟨typedUnary, _fuelUnary, terminalUnary, normalUnaryFromPacket, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed normalUnary continuationUnary normalContinuationHandoff
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed handoffUnary routesUnary handoffRoutesConsumer
  have handoffSame : hsame handoff (append normal continuation) :=
    normalContinuationHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row typed ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row continuation ∨ hsame row handoff ∨ hsame row consumer)
          (fun _row : BHist =>
            Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
              Cont normal continuation handoff ∧ Cont handoff routes consumer)
          (fun row : BHist =>
            UnaryHistory row ∧
              (PkgSig bundle provenance pkg ∨ PkgSig bundle consumer pkg))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro typed (Or.inl (hsame_refl typed))
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
        cases source with
        | inl sameTyped =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameTyped)
        | inr rest =>
            cases rest with
            | inl sameTerminal =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameTerminal))
            | inr rest =>
                cases rest with
                | inl sameNormal =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameNormal)))
                | inr rest =>
                    cases rest with
                    | inl sameContinuation =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows)
                                    sameContinuation))))
                    | inr rest =>
                        cases rest with
                        | inl sameHandoff =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameHandoff)))))
                        | inr sameConsumer =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (hsame_trans (hsame_symm sameRows)
                                          sameConsumer)))))
    }
    pattern_sound := by
      intro _row _source
      exact
        ⟨typedFuelTerminal, terminalNormalContinuation, normalContinuationHandoff,
          handoffRoutesConsumer⟩
    ledger_sound := by
      intro _row source
      cases source with
      | inl sameTyped =>
          exact ⟨unary_transport typedUnary (hsame_symm sameTyped), Or.inl provenancePkg⟩
      | inr rest =>
          cases rest with
          | inl sameTerminal =>
              exact
                ⟨unary_transport terminalUnary (hsame_symm sameTerminal),
                  Or.inl provenancePkg⟩
          | inr rest =>
              cases rest with
              | inl sameNormal =>
                  exact
                    ⟨unary_transport normalUnaryFromPacket (hsame_symm sameNormal),
                      Or.inl provenancePkg⟩
              | inr rest =>
                  cases rest with
                  | inl sameContinuation =>
                      exact
                        ⟨unary_transport continuationUnary (hsame_symm sameContinuation),
                          Or.inl provenancePkg⟩
                  | inr rest =>
                      cases rest with
                      | inl sameHandoff =>
                          exact
                            ⟨unary_transport handoffUnary (hsame_symm sameHandoff),
                              Or.inr consumerPkg⟩
                      | inr sameConsumer =>
                          exact
                            ⟨unary_transport consumerUnary (hsame_symm sameConsumer),
                              Or.inr consumerPkg⟩
  }
  exact ⟨cert, handoffUnary, consumerUnary, handoffSame⟩

end BEDC.Derived.ZnormalUp
