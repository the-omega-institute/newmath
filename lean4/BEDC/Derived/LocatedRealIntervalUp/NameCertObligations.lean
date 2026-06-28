import BEDC.Derived.LocatedRealIntervalUp.ExactnessRoute
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.LocatedRealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedRealIntervalCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {L U rho Delta Lambda M bracket H C P N endpointRead radiusRead dyadicIntervalRead
      locatorRead modulusRead bracketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory U →
        UnaryHistory rho →
          UnaryHistory Delta →
            UnaryHistory Lambda →
              UnaryHistory M →
                UnaryHistory bracket →
                  Cont L U endpointRead →
                    Cont endpointRead rho radiusRead →
                      Cont radiusRead Delta dyadicIntervalRead →
                        Cont dyadicIntervalRead Lambda locatorRead →
                          Cont locatorRead M modulusRead →
                            Cont modulusRead bracket bracketRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row bracketRead ∧
                                        UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row L ∨ hsame row U ∨ hsame row rho ∨
                                          hsame row Delta ∨ hsame row Lambda ∨
                                            hsame row M ∨ hsame row bracket ∨
                                              hsame row bracketRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory endpointRead ∧ UnaryHistory radiusRead ∧
                                      UnaryHistory dyadicIntervalRead ∧
                                        UnaryHistory locatorRead ∧ UnaryHistory modulusRead ∧
                                          UnaryHistory bracketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryL unaryU unaryRho unaryDelta unaryLambda unaryM unaryBracket endpointRoute
    radiusRoute dyadicIntervalRoute locatorRoute modulusRoute bracketRoute provenancePkg
    namePkg
  have _transportRow : BHist := H
  have _replayRow : BHist := C
  have exactness :=
    LocatedRealIntervalCarrier_exactness_route unaryL unaryU unaryRho unaryDelta unaryLambda
      unaryM unaryBracket endpointRoute radiusRoute dyadicIntervalRoute locatorRoute
      modulusRoute bracketRoute
  obtain ⟨_exactCert, endpointUnary, radiusUnary, dyadicIntervalUnary, locatorUnary,
    modulusUnary, bracketReadUnary, _endpointRoute, _radiusRoute, _dyadicIntervalRoute,
    _locatorRoute, _modulusRoute, _bracketRoute⟩ := exactness
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bracketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row rho ∨ hsame row Delta ∨
              hsame row Lambda ∨ hsame row M ∨ hsame row bracket ∨ hsame row bracketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bracketRead
        ⟨hsame_refl bracketRead, bracketReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, endpointUnary, radiusUnary, dyadicIntervalUnary, locatorUnary, modulusUnary,
      bracketReadUnary⟩

end BEDC.Derived.LocatedRealIntervalUp
