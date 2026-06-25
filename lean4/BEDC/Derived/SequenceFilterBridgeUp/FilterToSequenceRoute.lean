import BEDC.Derived.SequenceFilterBridgeUp.SequenceToFilterRoute

namespace BEDC.Derived.SequenceFilterBridgeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequenceFilterBridgeFilterToSequenceRoute [AskSetup] [PackageSetup]
    {S F Q T R E H C P N filterWindow sequenceRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory F →
      UnaryHistory T →
        UnaryHistory R →
          UnaryHistory S →
            UnaryHistory P →
              Cont F T filterWindow →
                Cont filterWindow R sequenceRead →
                  Cont sequenceRead S completionRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row F ∨ hsame row T ∨ hsame row R ∨ hsame row S ∨
                                hsame row Q ∨ hsame row completionRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont F T filterWindow ∧
                                Cont filterWindow R sequenceRead ∧
                                  Cont sequenceRead S completionRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory filterWindow ∧ UnaryHistory sequenceRead ∧
                            UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro fUnary tUnary rUnary sUnary _pUnary filterRoute sequenceRoute completionRoute
    packageP packageN
  have filterUnary : UnaryHistory filterWindow :=
    unary_cont_closed fUnary tUnary filterRoute
  have sequenceUnary : UnaryHistory sequenceRead :=
    unary_cont_closed filterUnary rUnary sequenceRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sequenceUnary sUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row T ∨ hsame row R ∨ hsame row S ∨ hsame row Q ∨
              hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont F T filterWindow ∧ Cont filterWindow R sequenceRead ∧
              Cont sequenceRead S completionRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, filterRoute, sequenceRoute, completionRoute, packageP, packageN⟩
  }
  exact ⟨cert, filterUnary, sequenceUnary, completionUnary⟩

end BEDC.Derived.SequenceFilterBridgeUp
