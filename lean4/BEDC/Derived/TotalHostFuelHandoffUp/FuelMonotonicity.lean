import BEDC.Derived.TotalHostFuelHandoffUp.NameCertObligations

namespace BEDC.Derived.TotalHostFuelHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotalHostFuelHandoffFuelMonotonicity [AskSetup] [PackageSetup]
    {H F S T R B X C P N smallerFuel shortenedTrace terminalRead refused : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H →
      UnaryHistory F →
        UnaryHistory S →
          UnaryHistory T →
            UnaryHistory R →
              UnaryHistory B →
                Cont H F smallerFuel →
                  Cont smallerFuel S shortenedTrace →
                    Cont shortenedTrace R terminalRead →
                      Cont terminalRead B refused →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row refused ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row H ∨ hsame row F ∨ hsame row S ∨
                                    hsame row T ∨ hsame row R ∨ hsame row B ∨
                                      hsame row X ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N ∨ hsame row refused)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont H F smallerFuel ∧
                                    Cont smallerFuel S shortenedTrace ∧
                                      Cont shortenedTrace R terminalRead ∧
                                        Cont terminalRead B refused ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory smallerFuel ∧ UnaryHistory shortenedTrace ∧
                                UnaryHistory terminalRead ∧ UnaryHistory refused := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro hUnary fUnary sUnary _tUnary rUnary bUnary smallerFuelRoute shortenedTraceRoute
    terminalReadRoute refusedRoute pkgP pkgN
  have smallerFuelUnary : UnaryHistory smallerFuel :=
    unary_cont_closed hUnary fUnary smallerFuelRoute
  have shortenedTraceUnary : UnaryHistory shortenedTrace :=
    unary_cont_closed smallerFuelUnary sUnary shortenedTraceRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed shortenedTraceUnary rUnary terminalReadRoute
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed terminalReadUnary bUnary refusedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refused ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row S ∨ hsame row T ∨ hsame row R ∨
              hsame row B ∨ hsame row X ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row refused)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F smallerFuel ∧ Cont smallerFuel S shortenedTrace ∧
              Cont shortenedTrace R terminalRead ∧ Cont terminalRead B refused ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refused ⟨hsame_refl refused, refusedUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, smallerFuelRoute, shortenedTraceRoute, terminalReadRoute,
          refusedRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, smallerFuelUnary, shortenedTraceUnary, terminalReadUnary, refusedUnary⟩

end BEDC.Derived.TotalHostFuelHandoffUp
