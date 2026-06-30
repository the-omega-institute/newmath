import BEDC.Derived.ObserverperspectiveclassifierUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierObligationClosureWitness [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont gap route publicRead →
        Cont publicRead name verdict →
          PkgSig bundle publicRead pkg →
            PkgSig bundle verdict pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row observerLeft ∨ hsame row observerRight ∨
                        hsame row universeLeft ∨ hsame row universeRight ∨
                          hsame row locality ∨ hsame row gap ∨ hsame row transport ∨
                            hsame row route ∨ hsame row publicRead ∨ hsame row verdict) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row observerLeft ∨ hsame row observerRight ∨
                      hsame row universeLeft ∨ hsame row universeRight ∨ hsame row locality ∨
                        hsame row gap ∨ hsame row transport ∨ hsame row route ∨
                          hsame row publicRead ∨ hsame row verdict)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont observerLeft observerRight universeLeft ∧
                      Cont universeLeft universeRight locality ∧ Cont locality gap transport ∧
                        Cont transport route gap ∧ Cont gap route publicRead ∧
                          Cont publicRead name verdict ∧ PkgSig bundle provenance pkg ∧
                            PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg ∧
                              PkgSig bundle verdict pkg)
                  hsame ∧
                UnaryHistory verdict := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier gapRoutePublicRead publicReadNameVerdict publicReadPkg verdictPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, _localityUnary, gapUnary, transportUnary, routeUnary,
    _provenanceUnary, nameUnary, observerUniverse, universeLocality, localityTransport,
    transportGap, provenancePkg, namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed gapUnary routeUnary gapRoutePublicRead
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed publicReadUnary nameUnary publicReadNameVerdict
  have verdictPattern :
      hsame verdict observerLeft ∨ hsame verdict observerRight ∨
        hsame verdict universeLeft ∨ hsame verdict universeRight ∨
          hsame verdict locality ∨ hsame verdict gap ∨ hsame verdict transport ∨
            hsame verdict route ∨ hsame verdict publicRead ∨ hsame verdict verdict := by
    right
    right
    right
    right
    right
    right
    right
    right
    right
    exact hsame_refl verdict
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
                hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨
                  hsame row transport ∨ hsame row route ∨ hsame row publicRead ∨
                    hsame row verdict) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row observerLeft ∨ hsame row observerRight ∨ hsame row universeLeft ∨
              hsame row universeRight ∨ hsame row locality ∨ hsame row gap ∨
                hsame row transport ∨ hsame row route ∨ hsame row publicRead ∨
                  hsame row verdict)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont observerLeft observerRight universeLeft ∧
              Cont universeLeft universeRight locality ∧ Cont locality gap transport ∧
                Cont transport route gap ∧ Cont gap route publicRead ∧
                  Cont publicRead name verdict ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg ∧
                      PkgSig bundle verdict pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro verdict ⟨verdictPattern, verdictUnary⟩
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
          | inl sameObserverLeft =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameObserverLeft)
          | inr rest =>
              cases rest with
              | inl sameObserverRight =>
                  exact Or.inr
                    (Or.inl (hsame_trans (hsame_symm sameRows) sameObserverRight))
              | inr rest =>
                  cases rest with
                  | inl sameUniverseLeft =>
                      exact Or.inr
                        (Or.inr
                          (Or.inl (hsame_trans (hsame_symm sameRows) sameUniverseLeft)))
                  | inr rest =>
                      cases rest with
                      | inl sameUniverseRight =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl
                                  (hsame_trans (hsame_symm sameRows) sameUniverseRight))))
                      | inr rest =>
                          cases rest with
                          | inl sameLocality =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameLocality)))))
                          | inr rest =>
                              cases rest with
                              | inl sameGap =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows) sameGap))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameTransport =>
                                      exact Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameTransport)))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameRoute =>
                                          exact Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans
                                                            (hsame_symm sameRows)
                                                            sameRoute))))))))
                                      | inr rest =>
                                          cases rest with
                                          | inl samePublicRead =>
                                              exact Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inl
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  samePublicRead)))))))))
                                          | inr sameVerdict =>
                                              exact Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (Or.inr
                                                            (Or.inr
                                                              (Or.inr
                                                                (hsame_trans
                                                                  (hsame_symm sameRows)
                                                                  sameVerdict)))))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, observerUniverse, universeLocality, localityTransport, transportGap,
          gapRoutePublicRead, publicReadNameVerdict, provenancePkg, namePkg, publicReadPkg,
          verdictPkg⟩
  }
  exact ⟨cert, verdictUnary⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
