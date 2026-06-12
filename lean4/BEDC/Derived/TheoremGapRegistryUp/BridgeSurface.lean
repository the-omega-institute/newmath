import BEDC.Derived.TheoremGapRegistryUp.PublicExportSurface

namespace BEDC.Derived.TheoremGapRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TheoremGapRegistry_bridge_surface [AskSetup] [PackageSetup]
    {T D S G C F A L _H P N strength gapCovered failure auditExport publicRead bridgeRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory D →
        UnaryHistory G →
          UnaryHistory C →
            UnaryHistory F →
              UnaryHistory A →
                UnaryHistory L →
                  Cont T D S →
                    Cont D S strength →
                      Cont G C gapCovered →
                        Cont gapCovered F failure →
                          Cont A L auditExport →
                            Cont failure auditExport publicRead →
                              Cont publicRead A bridgeRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          (hsame row publicRead ∨ hsame row bridgeRead) ∧
                                            UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row T ∨ hsame row D ∨ hsame row S ∨
                                            hsame row G ∨ hsame row C ∨ hsame row F ∨
                                              hsame row A ∨ hsame row L ∨
                                                hsame row publicRead ∨
                                                  hsame row bridgeRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont T D S ∧
                                            Cont D S strength ∧
                                              Cont G C gapCovered ∧
                                                Cont gapCovered F failure ∧
                                                  Cont A L auditExport ∧
                                                    Cont failure auditExport publicRead ∧
                                                      Cont publicRead A bridgeRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro tUnary dUnary gUnary cUnary fUnary aUnary lUnary strengthSeed strengthRoute
    coverageRoute failureRoute auditRoute publicRoute bridgeRoute provenancePkg namePkg
  have strengthSeedUnary : UnaryHistory S :=
    unary_cont_closed tUnary dUnary strengthSeed
  have strengthUnary : UnaryHistory strength :=
    unary_cont_closed dUnary strengthSeedUnary strengthRoute
  have gapCoveredUnary : UnaryHistory gapCovered :=
    unary_cont_closed gUnary cUnary coverageRoute
  have failureUnary : UnaryHistory failure :=
    unary_cont_closed gapCoveredUnary fUnary failureRoute
  have auditExportUnary : UnaryHistory auditExport :=
    unary_cont_closed aUnary lUnary auditRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed failureUnary auditExportUnary publicRoute
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicReadUnary aUnary bridgeRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro bridgeRead
            ⟨Or.inr (hsame_refl bridgeRead), bridgeReadUnary⟩
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
          constructor
          · cases source.left with
            | inl samePublic =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) samePublic)
            | inr sameBridge =>
                exact Or.inr (hsame_trans (hsame_symm sameRows) sameBridge)
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl samePublic =>
            right
            right
            right
            right
            right
            right
            right
            right
            left
            exact samePublic
        | inr sameBridge =>
            right
            right
            right
            right
            right
            right
            right
            right
            right
            exact sameBridge
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, strengthSeed, strengthRoute, coverageRoute, failureRoute,
            auditRoute, publicRoute, bridgeRoute, provenancePkg, namePkg⟩
    }
  · exact bridgeReadUnary

end BEDC.Derived.TheoremGapRegistryUp
