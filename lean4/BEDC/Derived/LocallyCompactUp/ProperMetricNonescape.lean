import BEDC.Derived.LocallyCompactUp.ClosedBallNeighborhoodBase

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactProperMetricNonescape [AskSetup] [PackageSetup]
    {X x r B K A H C P N compactRead locatedRead completionRead properRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory x →
        UnaryHistory r →
          UnaryHistory A →
            UnaryHistory H →
              UnaryHistory C →
                UnaryHistory P →
                  Cont X x B →
                    Cont B r K →
                      Cont K A compactRead →
                        Cont compactRead H locatedRead →
                          Cont locatedRead C completionRead →
                            Cont B K properRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row properRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row X ∨ hsame row x ∨ hsame row r ∨
                                          hsame row B ∨ hsame row K ∨ hsame row A ∨
                                            hsame row properRead ∨ hsame row completionRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory compactRead ∧
                                      UnaryHistory locatedRead ∧
                                        UnaryHistory completionRead ∧
                                          UnaryHistory properRead ∧
                                            hsame properRead (append B K) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory append
  intro sourceUnary pointUnary radiusUnary locatedUnary transportUnary completionUnary
    provenanceUnary sourcePointRoute closedBallRoute compactRoute locatedRoute completionRoute
    properRoute provenancePkg localNamePkg
  have closedBallUnary : UnaryHistory B :=
    unary_cont_closed sourceUnary pointUnary sourcePointRoute
  have compactWitnessUnary : UnaryHistory K :=
    unary_cont_closed closedBallUnary radiusUnary closedBallRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactWitnessUnary locatedUnary compactRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed compactReadUnary transportUnary locatedRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed locatedReadUnary completionUnary completionRoute
  have properReadUnary : UnaryHistory properRead :=
    unary_cont_closed closedBallUnary compactWitnessUnary properRoute
  have properReadExact : hsame properRead (append B K) := by
    cases properRoute
    exact hsame_refl _
  have properSource :
      (fun row : BHist => hsame row properRead ∧ UnaryHistory row) properRead := by
    exact ⟨hsame_refl properRead, properReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row properRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨ hsame row K ∨
              hsame row A ∨ hsame row properRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro properRead properSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, compactReadUnary, locatedReadUnary, completionReadUnary, properReadUnary,
      properReadExact⟩

end BEDC.Derived.LocallyCompactUp
