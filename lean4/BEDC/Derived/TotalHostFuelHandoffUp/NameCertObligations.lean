import BEDC.Derived.TotalHostFuelHandoffUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TotalHostFuelHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotalHostFuelHandoffNameCertObligations [AskSetup] [PackageSetup]
    {H F S T R B X C P N hostFuel fuelTrace traceRead refused : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H →
      UnaryHistory F →
        UnaryHistory S →
          UnaryHistory T →
            UnaryHistory R →
              UnaryHistory B →
                Cont H F hostFuel →
                  Cont F S fuelTrace →
                    Cont T R traceRead →
                      Cont hostFuel traceRead refused →
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
                                  UnaryHistory row ∧ Cont H F hostFuel ∧
                                    Cont F S fuelTrace ∧ Cont T R traceRead ∧
                                      Cont hostFuel traceRead refused ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory hostFuel ∧ UnaryHistory fuelTrace ∧
                                UnaryHistory traceRead ∧ UnaryHistory refused := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro hUnary fUnary sUnary tUnary rUnary _bUnary hostFuelRoute fuelTraceRoute
    traceReadRoute refusedRoute pkgP pkgN
  have hostFuelUnary : UnaryHistory hostFuel :=
    unary_cont_closed hUnary fUnary hostFuelRoute
  have fuelTraceUnary : UnaryHistory fuelTrace :=
    unary_cont_closed fUnary sUnary fuelTraceRoute
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed tUnary rUnary traceReadRoute
  have refusedUnary : UnaryHistory refused :=
    unary_cont_closed hostFuelUnary traceReadUnary refusedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refused ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row S ∨ hsame row T ∨ hsame row R ∨
              hsame row B ∨ hsame row X ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row refused)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F hostFuel ∧ Cont F S fuelTrace ∧
              Cont T R traceRead ∧ Cont hostFuel traceRead refused ∧
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
        ⟨sourceRow.right, hostFuelRoute, fuelTraceRoute, traceReadRoute,
          refusedRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, hostFuelUnary, fuelTraceUnary, traceReadUnary, refusedUnary⟩

theorem TotalHostFuelHandoffSiblingBoundary [AskSetup] [PackageSetup]
    {H F S T R B X C P N hostFuel substrateTrace boundedTrace terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory H →
      UnaryHistory F →
        UnaryHistory S →
          UnaryHistory T →
            UnaryHistory R →
              UnaryHistory B →
                Cont H F hostFuel →
                  Cont hostFuel S substrateTrace →
                    Cont substrateTrace T boundedTrace →
                      Cont boundedTrace R terminalRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle N pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row H ∨ hsame row F ∨ hsame row S ∨
                                    hsame row T ∨ hsame row R ∨ hsame row B ∨
                                      hsame row X ∨ hsame row C ∨ hsame row P ∨
                                        hsame row N ∨ hsame row terminalRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont H F hostFuel ∧
                                    Cont hostFuel S substrateTrace ∧
                                      Cont substrateTrace T boundedTrace ∧
                                        Cont boundedTrace R terminalRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory hostFuel ∧ UnaryHistory substrateTrace ∧
                                UnaryHistory boundedTrace ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro hUnary fUnary sUnary tUnary rUnary _bUnary hostFuelRoute substrateTraceRoute
    boundedTraceRoute terminalReadRoute pkgP pkgN
  have hostFuelUnary : UnaryHistory hostFuel :=
    unary_cont_closed hUnary fUnary hostFuelRoute
  have substrateTraceUnary : UnaryHistory substrateTrace :=
    unary_cont_closed hostFuelUnary sUnary substrateTraceRoute
  have boundedTraceUnary : UnaryHistory boundedTrace :=
    unary_cont_closed substrateTraceUnary tUnary boundedTraceRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed boundedTraceUnary rUnary terminalReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row S ∨ hsame row T ∨ hsame row R ∨
              hsame row B ∨ hsame row X ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H F hostFuel ∧ Cont hostFuel S substrateTrace ∧
              Cont substrateTrace T boundedTrace ∧ Cont boundedTrace R terminalRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead
        ⟨hsame_refl terminalRead, terminalReadUnary⟩
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
        ⟨sourceRow.right, hostFuelRoute, substrateTraceRoute, boundedTraceRoute,
          terminalReadRoute, pkgP, pkgN⟩
  }
  exact
    ⟨cert, hostFuelUnary, substrateTraceUnary, boundedTraceUnary, terminalReadUnary⟩

end BEDC.Derived.TotalHostFuelHandoffUp
