import BEDC.Derived.LocallyCompactUp.PublicNeighbourhoodBaseExport

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactAbstractSchemaBridgeSurface [AskSetup] [PackageSetup]
    {X x r B K A H C P N basisRead completionRead properRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory x →
        UnaryHistory r →
          UnaryHistory A →
            UnaryHistory P →
              UnaryHistory N →
                Cont X x B →
                  Cont B r K →
                    Cont K A H →
                      Cont H P C →
                        Cont C N basisRead →
                          Cont A C completionRead →
                            Cont K H properRead →
                              Cont basisRead completionRead bridgeRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          (hsame row bridgeRead ∨ hsame row basisRead ∨
                                              hsame row completionRead ∨ hsame row properRead) ∧
                                            UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row X ∨ hsame row B ∨ hsame row K ∨
                                            hsame row A ∨ hsame row H ∨ hsame row C ∨
                                              hsame row basisRead ∨ hsame row completionRead ∨
                                                hsame row properRead ∨ hsame row bridgeRead)
                                        (fun _row : BHist =>
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory bridgeRead ∧
                                        hsame bridgeRead (append basisRead completionRead) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro XUnary xUnary rUnary AUnary PUnary NUnary routeXB routeBK routeKH routeHC
    routeBasis routeCompletion routeProper routeBridge pkgP pkgN
  have publicExport :=
    LocallyCompactPublicNeighbourhoodBaseExport
      (X := X) (x := x) (r := r) (B := B) (K := K) (A := A) (H := H) (C := C)
      (P := P) (N := N) (basisRead := basisRead) (completionRead := completionRead)
      (properRead := properRead) (bundle := bundle) (pkg := pkg)
      XUnary xUnary rUnary AUnary PUnary NUnary routeXB routeBK routeKH routeHC
      routeBasis routeCompletion routeProper pkgP pkgN
  have basisUnary : UnaryHistory basisRead := publicExport.2.1
  have completionUnary : UnaryHistory completionRead := publicExport.2.2.1
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed basisUnary completionUnary routeBridge
  have bridgeSource :
      (fun row : BHist =>
        (hsame row bridgeRead ∨ hsame row basisRead ∨ hsame row completionRead ∨
            hsame row properRead) ∧
          UnaryHistory row) bridgeRead := by
    exact ⟨Or.inl (hsame_refl bridgeRead), bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row bridgeRead ∨ hsame row basisRead ∨ hsame row completionRead ∨
                hsame row properRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row B ∨ hsame row K ∨ hsame row A ∨ hsame row H ∨
              hsame row C ∨ hsame row basisRead ∨ hsame row completionRead ∨
                hsame row properRead ∨ hsame row bridgeRead)
          (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead bridgeSource
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
        have transportedUnary : UnaryHistory _ :=
          unary_transport source.right sameRows
        cases source.left with
        | inl bridgeSame =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) bridgeSame),
                transportedUnary⟩
        | inr tail =>
            cases tail with
            | inl basisSame =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) basisSame)),
                    transportedUnary⟩
            | inr tail =>
                cases tail with
                | inl completionSame =>
                    exact
                      ⟨Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) completionSame))),
                        transportedUnary⟩
                | inr properSame =>
                    exact
                      ⟨Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) properSame))),
                        transportedUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl bridgeSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inr bridgeSame))))))))
      | inr tail =>
          cases tail with
          | inl basisSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr (Or.inl basisSame))))))
          | inr tail =>
              cases tail with
              | inl completionSame =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl completionSame)))))))
              | inr properSame =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inr (Or.inl properSame))))))))
    ledger_sound := by
      intro _row _source
      exact ⟨pkgP, pkgN⟩
  }
  exact ⟨cert, bridgeUnary, routeBridge⟩

end BEDC.Derived.LocallyCompactUp
