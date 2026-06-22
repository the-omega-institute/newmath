import BEDC.Derived.MetacicDecidabilityWitnessUp.DecidabilityWitnessPublicExport

namespace BEDC.Derived.MetacicDecidabilityWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetacicDecidabilityWitnessConfluenceHandoffBoundary [AskSetup] [PackageSetup]
    {T S B F R H C P N checkerRead conversionRead normalRead handoffRead boundaryRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetacicDecidabilityWitnessCarrier T S B F R H C P N bundle pkg →
      Cont T S checkerRead →
        Cont B F conversionRead →
          Cont checkerRead conversionRead normalRead →
            Cont normalRead R handoffRead →
              Cont handoffRead N boundaryRead →
                PkgSig bundle boundaryRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row normalRead ∨ hsame row handoffRead ∨
                          hsame row boundaryRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
                          hsame row R ∨ hsame row N ∨ hsame row normalRead ∨
                            hsame row handoffRead ∨ hsame row boundaryRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont T S checkerRead ∧
                          Cont B F conversionRead ∧
                            Cont checkerRead conversionRead normalRead ∧
                              Cont normalRead R handoffRead ∧
                                Cont handoffRead N boundaryRead ∧
                                  PkgSig bundle boundaryRead pkg)
                      hsame ∧
                    UnaryHistory normalRead ∧ UnaryHistory handoffRead ∧
                      UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: MetacicDecidabilityWitnessCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier checkerRoute conversionRoute normalRoute handoffRoute boundaryRoute boundaryPkg
  obtain ⟨tUnary, sUnary, bUnary, fUnary, rUnary, _hUnary, _cUnary, _pUnary, nUnary,
    _provenancePkg, _namePkg, _packetWitness⟩ := carrier
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed tUnary sUnary checkerRoute
  have conversionUnary : UnaryHistory conversionRead :=
    unary_cont_closed bUnary fUnary conversionRoute
  have normalUnary : UnaryHistory normalRead :=
    unary_cont_closed checkerUnary conversionUnary normalRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed normalUnary rUnary handoffRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed handoffUnary nUnary boundaryRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro boundaryRead
            ⟨Or.inr (Or.inr (hsame_refl boundaryRead)), boundaryUnary⟩
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
            | inl sameNormal =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameNormal)
            | inr rest =>
                cases rest with
                | inl sameHandoff =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameHandoff))
                | inr sameBoundary =>
                    exact
                      Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameBoundary))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl sameNormal =>
            exact
              Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameNormal))))))
        | inr rest =>
            cases rest with
            | inl sameHandoff =>
                exact
                  Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inl sameHandoff)))))))
            | inr sameBoundary =>
                exact
                  Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr sameBoundary)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, checkerRoute, conversionRoute, normalRoute, handoffRoute,
            boundaryRoute, boundaryPkg⟩
    }
  · exact ⟨normalUnary, handoffUnary, boundaryUnary⟩

end BEDC.Derived.MetacicDecidabilityWitnessUp
