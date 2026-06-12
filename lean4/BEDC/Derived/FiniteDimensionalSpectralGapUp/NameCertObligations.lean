import BEDC.Derived.FiniteDimensionalSpectralGapUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteDimensionalSpectralGapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteDimensionalSpectralGap_namecert_obligations [AskSetup] [PackageSetup]
    {M T V E D R S H C P N matrixOperator eigenWindow gapSeal spectralBound transportRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory T →
        UnaryHistory V →
          UnaryHistory E →
            UnaryHistory D →
              UnaryHistory R →
                UnaryHistory S →
                  UnaryHistory H →
                    UnaryHistory C →
                      Cont M T matrixOperator →
                        Cont matrixOperator V eigenWindow →
                          Cont E D gapSeal →
                            Cont gapSeal R spectralBound →
                              Cont spectralBound H transportRead →
                                Cont transportRead C replayRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row replayRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row M ∨ hsame row T ∨ hsame row V ∨
                                              hsame row E ∨ hsame row D ∨ hsame row R ∨
                                                hsame row S ∨ hsame row replayRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧
                                              Cont M T matrixOperator ∧
                                                Cont matrixOperator V eigenWindow ∧
                                                  Cont E D gapSeal ∧
                                                    Cont gapSeal R spectralBound ∧
                                                      Cont spectralBound H transportRead ∧
                                                        Cont transportRead C replayRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory matrixOperator ∧
                                          UnaryHistory eigenWindow ∧
                                            UnaryHistory gapSeal ∧
                                              UnaryHistory spectralBound ∧
                                                UnaryHistory transportRead ∧
                                                  UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro mUnary tUnary vUnary eUnary dUnary rUnary _sUnary hUnary cUnary matrixRoute
    eigenRoute gapRoute spectralRoute transportRoute replayRoute provenancePkg namePkg
  have matrixOperatorUnary : UnaryHistory matrixOperator :=
    unary_cont_closed mUnary tUnary matrixRoute
  have eigenWindowUnary : UnaryHistory eigenWindow :=
    unary_cont_closed matrixOperatorUnary vUnary eigenRoute
  have gapSealUnary : UnaryHistory gapSeal :=
    unary_cont_closed eUnary dUnary gapRoute
  have spectralBoundUnary : UnaryHistory spectralBound :=
    unary_cont_closed gapSealUnary rUnary spectralRoute
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed spectralBoundUnary hUnary transportRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed transportReadUnary cUnary replayRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
        right
        right
        right
        right
        right
        right
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, matrixRoute, eigenRoute, gapRoute, spectralRoute,
            transportRoute, replayRoute, provenancePkg, namePkg⟩
    }
  · exact
      ⟨matrixOperatorUnary, eigenWindowUnary, gapSealUnary, spectralBoundUnary,
        transportReadUnary, replayReadUnary⟩

end BEDC.Derived.FiniteDimensionalSpectralGapUp
