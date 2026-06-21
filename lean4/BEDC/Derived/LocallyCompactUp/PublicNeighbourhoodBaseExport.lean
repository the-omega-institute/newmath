import BEDC.Derived.LocallyCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactPublicNeighbourhoodBaseExport [AskSetup] [PackageSetup]
    {X x r B K A H C P N basisRead completionRead properRead : BHist}
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
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row basisRead ∨ hsame row completionRead ∨
                                            hsame row properRead) ∧
                                          UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row X ∨ hsame row B ∨ hsame row K ∨
                                          hsame row A ∨ hsame row H ∨ hsame row C ∨
                                            hsame row basisRead ∨ hsame row completionRead ∨
                                              hsame row properRead)
                                      (fun _row : BHist =>
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory basisRead ∧
                                      UnaryHistory completionRead ∧ UnaryHistory properRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro XUnary xUnary rUnary AUnary PUnary NUnary routeXB routeBK routeKH routeHC
    routeBasis routeCompletion routeProper pkgP pkgN
  have BUnary : UnaryHistory B :=
    unary_cont_closed XUnary xUnary routeXB
  have KUnary : UnaryHistory K :=
    unary_cont_closed BUnary rUnary routeBK
  have HUnary : UnaryHistory H :=
    unary_cont_closed KUnary AUnary routeKH
  have CUnary : UnaryHistory C :=
    unary_cont_closed HUnary PUnary routeHC
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed CUnary NUnary routeBasis
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed AUnary CUnary routeCompletion
  have properUnary : UnaryHistory properRead :=
    unary_cont_closed KUnary HUnary routeProper
  have basisSource :
      (fun row : BHist =>
        (hsame row basisRead ∨ hsame row completionRead ∨ hsame row properRead) ∧
          UnaryHistory row) basisRead := by
    exact ⟨Or.inl (hsame_refl basisRead), basisUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row basisRead ∨ hsame row completionRead ∨ hsame row properRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row B ∨ hsame row K ∨ hsame row A ∨ hsame row H ∨
              hsame row C ∨ hsame row basisRead ∨ hsame row completionRead ∨
                hsame row properRead)
          (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro basisRead basisSource
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
        | inl basisSame =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) basisSame),
                transportedUnary⟩
        | inr tail =>
            cases tail with
            | inl completionSame =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) completionSame)),
                    transportedUnary⟩
            | inr properSame =>
                exact
                  ⟨Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) properSame)),
                    transportedUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl basisSame =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl basisSame))))))
      | inr tail =>
          cases tail with
          | inl completionSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inl completionSame)))))))
          | inr properSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr properSame)))))))
    ledger_sound := by
      intro _row _source
      exact ⟨pkgP, pkgN⟩
  }
  exact ⟨cert, basisUnary, completionUnary, properUnary⟩

end BEDC.Derived.LocallyCompactUp
