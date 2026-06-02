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

theorem LocallyCompactPropernessLocalityRootBoundary [AskSetup] [PackageSetup]
    {X x r B K A H C P N compactRead locatedRead completionRead properRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X ->
      UnaryHistory x ->
        UnaryHistory r ->
          UnaryHistory A ->
            UnaryHistory H ->
              UnaryHistory C ->
                UnaryHistory P ->
                  Cont X x B ->
                    Cont B r K ->
                      Cont K A compactRead ->
                        Cont compactRead H locatedRead ->
                          Cont locatedRead C completionRead ->
                            Cont B K properRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row properRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row X ∨ hsame row x ∨ hsame row r ∨
                                          hsame row B ∨ hsame row K ∨ hsame row A ∨
                                            hsame row properRead ∨ hsame row completionRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory compactRead ∧ UnaryHistory locatedRead ∧
                                      UnaryHistory completionRead ∧ UnaryHistory properRead ∧
                                        hsame properRead (append B K) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro xUnary pointUnary radiusUnary locatedHandoffUnary transportUnary consumerUnary
    _provenanceUnary sourcePointClosedBall closedBallRadiusCompact compactLocatedRead
    compactTransportLocated locatedConsumerCompletion properRoute provenancePkg localNamePkg
  have closedBallUnary : UnaryHistory B :=
    unary_cont_closed xUnary pointUnary sourcePointClosedBall
  have compactWitnessUnary : UnaryHistory K :=
    unary_cont_closed closedBallUnary radiusUnary closedBallRadiusCompact
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed compactWitnessUnary locatedHandoffUnary compactLocatedRead
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed compactReadUnary transportUnary compactTransportLocated
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed locatedReadUnary consumerUnary locatedConsumerCompletion
  have properReadUnary : UnaryHistory properRead :=
    unary_cont_closed closedBallUnary compactWitnessUnary properRoute
  have properAppend : hsame properRead (append B K) := by
    exact properRoute
  have sourceProper :
      (fun row : BHist => hsame row properRead ∧ UnaryHistory row) properRead := by
    exact ⟨hsame_refl properRead, properReadUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row properRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro properRead sourceProper
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other sameRows sourceRow
        have sameOtherProper : hsame other properRead :=
          hsame_trans (hsame_symm sameRows) sourceRow.left
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right sameRows
        exact ⟨sameOtherProper, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row properRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨ hsame row K ∨
              hsame row A ∨ hsame row properRead ∨ hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, provenancePkg, localNamePkg⟩
    }
  exact
    ⟨cert, compactReadUnary, locatedReadUnary, completionReadUnary, properReadUnary,
      properAppend⟩

end BEDC.Derived.LocallyCompactUp
