import BEDC.Derived.LocallyCompactUp.LocatedHandoffBoundary

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactLocatedBallRealSealBoundary [AskSetup] [PackageSetup]
    {X x r B K A P N realRead : BHist} {_H _C : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory x ->
        UnaryHistory r ->
          UnaryHistory B ->
            UnaryHistory K ->
              UnaryHistory A ->
                UnaryHistory P ->
                  Cont X x B ->
                    Cont B r K ->
                      Cont K A realRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                              (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨
                                  hsame row K ∨ hsame row A ∨ hsame row realRead)
                              (fun _row : BHist =>
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                              hsame ∧
                              UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro xUnary pointUnary radiusUnary _closedBallUnary _compactUnary locatedUnary _provenanceUnary
    closedBallRoute compactRoute realRoute provenancePkg localNamePkg
  have closedBallUnary : UnaryHistory B :=
    unary_cont_closed xUnary pointUnary closedBallRoute
  have compactUnary : UnaryHistory K :=
    unary_cont_closed closedBallUnary radiusUnary compactRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed compactUnary locatedUnary realRoute
  have realSource :
      (fun row : BHist => hsame row realRead ∧ UnaryHistory row) realRead := by
    exact ⟨hsame_refl realRead, realUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨ hsame row K ∨
            hsame row A ∨ hsame row realRead)
        (fun _row : BHist => PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead realSource
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
        intro row other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.1,
            unary_transport source.2 same⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.1)))))
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, realUnary⟩

end BEDC.Derived.LocallyCompactUp
