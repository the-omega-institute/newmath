import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalEndpointRefinementStability [AskSetup] [PackageSetup]
    {L U E D W R _S H _C P N refinedD refinedW refinedR refinedSeal refinedReplay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory refinedD → UnaryHistory refinedW → Cont D W R →
        Cont refinedD refinedW refinedR → hsame L L → hsame U U → hsame E E →
          Cont E refinedR refinedSeal → Cont refinedSeal H refinedReplay →
            PkgSig bundle P pkg → PkgSig bundle N pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row E ∨ hsame row refinedR ∨ hsame row refinedSeal ∨
                        hsame row refinedReplay) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row refinedD ∨
                      hsame row refinedW ∨ hsame row refinedR ∨ hsame row refinedSeal ∨
                        hsame row H ∨ hsame row refinedReplay ∨ hsame row P ∨
                          hsame row N)
                  (fun _row : BHist =>
                    UnaryHistory E ∧ Cont refinedD refinedW refinedR ∧
                      Cont E refinedR refinedSeal ∧ Cont refinedSeal H refinedReplay ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                  hsame ∧
                UnaryHistory R ∧ UnaryHistory refinedR ∧ UnaryHistory refinedSeal ∧
                  UnaryHistory refinedReplay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary eUnary dUnary wUnary hUnary refinedDUnary refinedWUnary
    originalWindow refinedWindow _sameL _sameU _sameE refinedSealRoute refinedReplayRoute
    provenancePkg namePkg
  have originalReadUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary originalWindow
  have refinedReadUnary : UnaryHistory refinedR :=
    unary_cont_closed refinedDUnary refinedWUnary refinedWindow
  have refinedSealUnary : UnaryHistory refinedSeal :=
    unary_cont_closed eUnary refinedReadUnary refinedSealRoute
  have refinedReplayUnary : UnaryHistory refinedReplay :=
    unary_cont_closed refinedSealUnary hUnary refinedReplayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row E ∨ hsame row refinedR ∨ hsame row refinedSeal ∨
                hsame row refinedReplay) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row refinedD ∨
              hsame row refinedW ∨ hsame row refinedR ∨ hsame row refinedSeal ∨
                hsame row H ∨ hsame row refinedReplay ∨ hsame row P ∨ hsame row N)
          (fun _row : BHist =>
            UnaryHistory E ∧ Cont refinedD refinedW refinedR ∧ Cont E refinedR refinedSeal ∧
              Cont refinedSeal H refinedReplay ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro E ⟨Or.inl (hsame_refl E), eUnary⟩
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
          | inl sameEndpoint =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)
          | inr tail =>
              cases tail with
              | inl sameRefined =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRefined))
              | inr tail =>
                  cases tail with
                  | inl sameSeal =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)))
                  | inr sameReplay =>
                      exact
                        Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameReplay)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameEndpoint =>
          exact Or.inr (Or.inr (Or.inl sameEndpoint))
      | inr tail =>
          cases tail with
          | inl sameRefined =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inr (Or.inl sameRefined)))))
          | inr tail =>
              cases tail with
              | inl sameSeal =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameSeal))))))
              | inr sameReplay =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (Or.inl sameReplay))))))))
    ledger_sound := by
      intro _row _source
      exact ⟨eUnary, refinedWindow, refinedSealRoute, refinedReplayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, originalReadUnary, refinedReadUnary, refinedSealUnary, refinedReplayUnary⟩

end BEDC.Derived.RealIntervalUp
